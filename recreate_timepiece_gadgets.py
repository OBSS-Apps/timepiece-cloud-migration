#!/usr/bin/env python3
"""Recreate Timepiece gadgets on Jira Cloud dashboards from a gadget migration file.

Jira Cloud Migration Assistant moves dashboards but not the Timepiece gadgets on them. During the app
migration, Timepiece writes a gadget migration file, which a Jira admin downloads from the Migration page of
the Timepiece admin menu on the server. This script adds those gadgets to the migrated cloud dashboards
through the Jira Cloud REST API.

Modes:
    list     Writes the dashboards of the file that can be migrated to a CSV file. Works offline.
    dry      Checks the dashboards listed in a CSV file and logs what migrate would do. Changes nothing.
    migrate  Adds the gadgets of the dashboards listed in a CSV file.

Usage:
    ./recreate_timepiece_gadgets.py list <migration file>
    ./recreate_timepiece_gadgets.py dry <migration file> --dashboards <CSV file>
    ./recreate_timepiece_gadgets.py migrate <migration file> --dashboards <CSV file>

dry and migrate read the credentials from a file (default: credentials.txt), never from the command line:

    JIRA_EMAIL=admin@example.com
    JIRA_API_TOKEN=<API token of that Atlassian account>
    TIMEPIECE_API_TOKEN=<optional: Timepiece API token, to give gadgets their migrated calendars>

The account must be a Jira admin. Migrated dashboards are usually private to their owners, so migrate gives
the admin edit access to each dashboard the admin cannot edit, adds the gadgets and removes that access again.

Running migrate again is safe. Each gadget it adds gets a marker, so a later run finds the gadget wherever it
sits. A Timepiece gadget already at the same position also counts; when it has no settings, migrate configures
it. A gadget that was added but could not be configured is configured by the next run.

The tokens go only over https, and the Jira token only to an Atlassian site (see --allow-any-site). The script
does not follow redirects, so a redirect cannot send a token to another host.

Each run writes a detailed log to logs/<mode>-<timestamp>.log. The screen shows only the progress and a
summary.

Needs Python 3.8 or later. No third-party packages.
"""

import argparse
import base64
import contextlib
import csv
import hashlib
import http.client
import json
import logging
import os
import platform
import re
import ssl
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from datetime import datetime
from typing import Any, Dict, Generator, List, Optional, Tuple

# Shown on the screen and written first to each log, so support can tell which script a user ran. Raise it
# with each change that users get.
VERSION = "1.0.0"

SUPPORTED_FORMAT_VERSION = 1

# The gadget's module key is
# com.atlassian.forge:ari:cloud:ecosystem::extension/<app id>/<environment id>/static/tisc-dashboard-gadget.
# Jira rejects the old Connect module key.
APP_ID = "b1a5086c-6fb8-4ec4-82e4-5e2785439e66"
PRODUCTION_ENVIRONMENT_ID = "1895fa93-4b2c-47c4-a4cd-dae3c15786e4"
GADGET_MODULE = "static/tisc-dashboard-gadget"

# The Timepiece gadget reads its settings from this dashboard item property.
CONFIG_PROPERTY_KEY = "gadgetsettingsconfiguration"
# Without this property Jira hands the gadget no configuration, and it asks to be configured.
IS_CONFIGURED_PROPERTY_KEY = "isConfigured"
# Marks a gadget that migrate added: {transferId, serverGadgetId, configured}. configured is false while the
# gadget waits for its configuration.
MARKER_PROPERTY_KEY = "timepiece-gadget-migration"

# Fallback for calendars without a cloud mapping.
NORMAL_HOURS_CALENDAR = "normalHours"
# The only day length that normalHours accepts.
NORMAL_HOURS_DAY_LENGTH = "24HourDays"

# Atlassian's API gateway. API tokens with scopes work only through it.
GATEWAY_URL = "https://api.atlassian.com/ex/jira"
DEFAULT_TIMEPIECE_URL = "https://tis.obss.io"
DEFAULT_CREDENTIALS_FILE = "credentials.txt"
DEFAULT_LOG_DIR = "logs"
# Kept in the log directory. Lists the dashboards that may still have the temporary edit access.
ACCESS_JOURNAL_FILE = "temporary-access.json"
# Kept in the log directory while migrate runs, so two runs cannot overwrite each other's journal.
MIGRATE_LOCK_FILE = "migrate.lock"
# Hosts of Jira Cloud sites. The Jira token goes to another host only with --allow-any-site.
ATLASSIAN_SITE_SUFFIXES = (".atlassian.net", ".jira.com")

LIST_HEADER = ["cloudDashboardId", "name", "owner", "gadgets", "serverDashboardId", "url"]

# Statuses that say the account cannot reach the dashboard. Expected for private dashboards.
NO_ACCESS_STATUSES = (401, 403, 404)

USER_AGENT = f"timepiece-gadget-migration-script/{VERSION}"

# Request and response bodies longer than this are cut in the log.
LOGGED_BODY_LIMIT = 2000

log = logging.getLogger("timepiece-gadget-migration")
# Until a run starts its log file, nothing goes to the screen.
log.addHandler(logging.NullHandler())


class InputError(Exception):
    """A problem with the files or the setup, found before any change."""


class RestError(Exception):
    def __init__(self, status: int, message: str):
        super().__init__(f"HTTP {status}: {message}" if status else message)
        self.status = status


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """urllib sends the Authorization header to any host that a redirect names. The Jira and Timepiece REST APIs
    do not redirect, so a redirect is answered as an error."""

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


OPENER = urllib.request.build_opener(NoRedirect)


class RestClient:
    MAX_ATTEMPTS = 5
    MAX_RETRY_DELAY = 300

    def __init__(self, base_url: str, authorization: Optional[str]):
        self.base_url = base_url.rstrip("/")
        self.headers = {
            "Accept": "application/json",
            "Content-Type": "application/json",
            "User-Agent": USER_AGENT,
        }
        if authorization:
            self.headers["Authorization"] = authorization

    def request(self, method: str, path: str, body: Any = None) -> Any:
        # Jira may have added a gadget when a POST fails with a server error or no answer, so a POST is sent
        # again only after a rate limit. Sending the other calls again changes nothing.
        retry_failures = method != "POST"
        attempt = 1
        while True:
            started = time.monotonic()
            status, retry_after, content = self.send(method, path, body)
            log.debug("%s %s -> %s in %d ms, %d bytes", method, self.base_url + path, status or "no answer",
                      (time.monotonic() - started) * 1000, len(content))
            # The bodies hold no credentials: the tokens travel only in the Authorization header.
            if body is not None:
                log.debug("  request body: %s", shorten(json.dumps(body, ensure_ascii=False)))
            if content:
                log.debug("  response body: %s", shorten(content.decode(errors="replace")))
            if 200 <= status < 300:
                try:
                    return json.loads(content) if content else None
                except ValueError:
                    raise RestError(0, f"{method} {path} returned invalid JSON: {content[:200]!r}") from None

            retry = status == 429 or (retry_failures and (status == 0 or status >= 500))
            if not retry or attempt == self.MAX_ATTEMPTS:
                raise RestError(status, error_message(content))
            delay = retry_after if retry_after is not None else 2 ** attempt
            log.warning("%s %s answered %s; trying again in %s s.", method, path, status or "nothing", delay)
            time.sleep(delay)
            attempt += 1

    def send(self, method: str, path: str, body: Any) -> Tuple[int, Optional[float], bytes]:
        """Returns the status, the Retry-After seconds and the body. Status 0: no HTTP answer."""
        data = json.dumps(body).encode() if body is not None else None
        request = urllib.request.Request(self.base_url + path, data=data, method=method, headers=self.headers)
        try:
            with OPENER.open(request, timeout=60) as response:
                return response.status, None, response.read()
        except urllib.error.HTTPError as e:
            if 300 <= e.code < 400:
                return e.code, None, (f"{method} {path} answered with a redirect to {e.headers.get('Location')}, "
                                      f"which the script does not follow").encode()
            return e.code, self.retry_after(e.headers.get("Retry-After")), e.read()
        except urllib.error.URLError as e:
            if isinstance(e.reason, ssl.SSLCertVerificationError):
                # Sending it again does not help.
                reason = getattr(e.reason, "verify_message", None) or e.reason
                raise RestError(0, f"{method} {path} failed: the certificate of the host cannot be checked: "
                                   f"{reason}.") from None
            return 0, None, f"{method} {path} failed: {e}".encode()
        except (OSError, http.client.HTTPException) as e:
            # Timeouts, and connections that break in the middle of the answer.
            return 0, None, f"{method} {path} failed: {e!r}".encode()

    def retry_after(self, value: Optional[str]) -> Optional[float]:
        try:
            return min(max(float(value), 0), self.MAX_RETRY_DELAY) if value else None
        except ValueError:
            return None


class Jira(RestClient):
    def __init__(self, site: str, email: str, token: str):
        credentials = base64.b64encode(f"{email}:{token}".encode()).decode()
        super().__init__(site, f"Basic {credentials}")

    def myself(self) -> Dict[str, Any]:
        return self.request("GET", "/rest/api/3/myself")

    def is_admin(self) -> bool:
        permissions = self.request("GET", "/rest/api/3/mypermissions?permissions=ADMINISTER")["permissions"]
        return bool((permissions.get("ADMINISTER") or {}).get("havePermission"))

    def available_gadgets(self) -> List[Dict[str, Any]]:
        return self.request("GET", "/rest/api/3/dashboard/gadgets")["gadgets"]

    def get_dashboard(self, dashboard_id: str) -> Optional[Dict[str, Any]]:
        """None when the account cannot see the dashboard: it is private, or it does not exist."""
        try:
            return self.request("GET", f"/rest/api/3/dashboard/{quote(dashboard_id)}")
        except RestError as e:
            if e.status in NO_ACCESS_STATUSES:
                return None
            raise

    def get_gadgets(self, dashboard_id: str) -> List[Dict[str, Any]]:
        return self.request("GET", f"/rest/api/3/dashboard/{quote(dashboard_id)}/gadget")["gadgets"]

    def get_item_property(self, dashboard_id: str, item_id: Any, key: str) -> Any:
        """None when the gadget has no such property."""
        try:
            return self.request("GET", self.property_path(dashboard_id, item_id, key))["value"]
        except RestError as e:
            if e.status == 404:
                return None
            raise

    def set_item_property(self, dashboard_id: str, item_id: Any, key: str, value: Any) -> None:
        self.request("PUT", self.property_path(dashboard_id, item_id, key), value)

    def add_gadget(self, dashboard_id: str, module_key: str, title: Optional[str], color: Optional[str],
                   column: Optional[int], row: Optional[int]) -> Dict[str, Any]:
        body: Dict[str, Any] = {"moduleKey": module_key}
        if title:
            body["title"] = title
        if color:
            body["color"] = color
        if column is not None and row is not None:
            body["position"] = {"column": column, "row": row}
        return self.request("POST", f"/rest/api/3/dashboard/{quote(dashboard_id)}/gadget", body)

    def remove_gadget(self, dashboard_id: str, item_id: Any) -> None:
        try:
            self.request("DELETE", f"/rest/api/3/dashboard/{quote(dashboard_id)}/gadget/{quote(item_id)}")
        except RestError as e:
            # A DELETE sent again after a lost answer finds the gadget gone.
            if e.status != 404:
                raise

    def change_edit_access(self, action: str, dashboard_id: str, account_id: str) -> None:
        """Adds or removes the account's edit permission on any dashboard. Needs the Jira admin permission."""
        result = self.request("PUT", "/rest/api/3/dashboard/bulk/edit", {
            "action": action,
            "entityIds": [int(dashboard_id)],
            "extendAdminPermissions": True,
            "permissionDetails": {
                "sharePermissions": [],
                "editPermissions": [{"type": "user", "user": {"accountId": account_id}}],
            },
        })
        errors = (result or {}).get("entityErrors") or {}
        if errors:
            raise RestError(400, json.dumps(errors))

    @staticmethod
    def property_path(dashboard_id: str, item_id: Any, key: str) -> str:
        return f"/rest/api/3/dashboard/{quote(dashboard_id)}/items/{quote(item_id)}/properties/{quote(key)}"


class Timepiece(RestClient):
    def __init__(self, url: str, token: str):
        super().__init__(url, f"TISJWT {token}")

    def get_calendar_mappings(self, transfer_id: str) -> Dict[str, str]:
        """Server calendar ID to cloud calendar ID. Needs a Jira admin and the Timepiece REST API.
        404 when the transfer imported no Timepiece data on this site."""
        return self.request("GET", f"/rest/migration/{quote(transfer_id)}/mappings")["calendars"]


def tenant_cloud_id(site: str) -> str:
    """The cloud ID of the site. Jira tells it without a login."""
    return RestClient(site, None).request("GET", "/_edge/tenant_info")["cloudId"]


def sign_in(site: str, email: str, token: str) -> Tuple[Jira, Dict[str, Any]]:
    """Returns the Jira client and the account. The site refuses an API token with scopes, so the API gateway is
    tried then."""
    jira = Jira(site, email, token)
    try:
        return jira, jira.myself()
    except RestError as e:
        if e.status not in (401, 403):
            raise InputError(f"Cannot reach Jira at {site}: {e}") from None
    try:
        jira = Jira(f"{GATEWAY_URL}/{tenant_cloud_id(site)}", email, token)
        me = jira.myself()
    except RestError as e:
        raise InputError(f"Jira did not accept the email and API token: {e}") from None
    log.info("The site refused the API token and the API gateway accepted it: a token with scopes.")
    return jira, me


def check_https(url: str, name: str) -> None:
    parts = urllib.parse.urlsplit(url)
    if parts.scheme != "https" or not parts.hostname:
        raise InputError(f"{name} {url} is not an https URL. The script sends the API tokens only over https.")


def check_site(site: str, allow_any_site: bool) -> None:
    """A typo in --site or a changed cloudUrl in the file must not send the Jira token to another host."""
    check_https(site, "The site")
    host = urllib.parse.urlsplit(site).hostname or ""
    if not allow_any_site and not host.endswith(ATLASSIAN_SITE_SUFFIXES):
        suffixes = " or ".join("*" + suffix for suffix in ATLASSIAN_SITE_SUFFIXES)
        raise InputError(f"The site {site} is not a Jira Cloud site ({suffixes}). Check --site, or cloudUrl in the "
                         f"file. Pass --allow-any-site to send the Jira token there anyway.")


def shorten(text: str, limit: int = LOGGED_BODY_LIMIT) -> str:
    text = " ".join(text.split())
    return text if len(text) <= limit else f"{text[:limit]}... ({len(text) - limit} more characters)"


def quote(value: Any) -> str:
    return urllib.parse.quote(str(value), safe="")


def error_message(content: bytes) -> str:
    try:
        body = json.loads(content)
    except ValueError:
        return content.decode(errors="replace").strip()[:500]
    if not isinstance(body, dict):
        return json.dumps(body)[:500]
    messages = list(body.get("errorMessages") or []) + [f"{k}: {v}" for k, v in (body.get("errors") or {}).items()]
    # Atlassian's API gateway answers with this one, such as for a token it does not accept.
    if body.get("message"):
        messages.append(str(body["message"]))
    return "; ".join(messages) if messages else json.dumps(body)[:500]


# Files

def read_migration_file(path: str) -> Dict[str, Any]:
    try:
        with open(path, encoding="utf-8") as f:
            export = json.load(f)
    except OSError as e:
        raise InputError(f"Cannot read {path}: {e.strerror}.") from None
    except ValueError:
        raise InputError(f"{path} is not a gadget migration file: it is not valid JSON.") from None
    if not isinstance(export, dict) or not isinstance(export.get("dashboards"), list) or not export.get("transferId"):
        raise InputError(f"{path} is not a gadget migration file.")
    if export.get("formatVersion") != SUPPORTED_FORMAT_VERSION:
        raise InputError(f"{path} has format version {export.get('formatVersion')}; "
                         f"this script reads version {SUPPORTED_FORMAT_VERSION}.")
    problems = export_problems(export)
    if problems:
        raise InputError(f"{path} is damaged:\n  " + "\n  ".join(problems[:20])
                         + (f"\n  ... and {len(problems) - 20} more" if len(problems) > 20 else ""))
    return export


def is_id(value: Any) -> bool:
    return (isinstance(value, int) and not isinstance(value, bool) and value >= 0) or (
        isinstance(value, str) and re.fullmatch(r"[0-9]+", value) is not None)


def is_position(value: Any) -> bool:
    return value is None or (isinstance(value, int) and not isinstance(value, bool) and value >= 0)


def export_problems(export: Dict[str, Any]) -> List[str]:
    """Checks every value the script uses, so a damaged file stops the run before the first change."""
    problems = []
    for key in ("warnings", "errors"):
        if not isinstance(export.get(key) or [], list):
            problems.append(f"{key} is not a list")
    for number, dashboard in enumerate(export["dashboards"], 1):
        where = f"dashboard {number}"
        if not isinstance(dashboard, dict):
            problems.append(f"{where} is not an object")
            continue
        if not is_id(dashboard.get("serverId")):
            problems.append(f"{where}: serverId {dashboard.get('serverId')!r} is not an ID")
        if dashboard.get("cloudId") is not None and not is_id(dashboard.get("cloudId")):
            problems.append(f"{where}: cloudId {dashboard.get('cloudId')!r} is not an ID")
        gadgets = dashboard.get("gadgets")
        if not isinstance(gadgets, list):
            problems.append(f"{where}: gadgets is not a list")
            continue
        for gadget_number, gadget in enumerate(gadgets, 1):
            gadget_where = f"{where} gadget {gadget_number}"
            if not isinstance(gadget, dict):
                problems.append(f"{gadget_where} is not an object")
                continue
            if not is_id(gadget.get("serverId")):
                problems.append(f"{gadget_where}: serverId {gadget.get('serverId')!r} is not an ID")
            for key in ("column", "row"):
                if not is_position(gadget.get(key)):
                    problems.append(f"{gadget_where}: {key} {gadget.get(key)!r} is not a position")
            for key in ("title", "color"):
                if gadget.get(key) is not None and not isinstance(gadget.get(key), str):
                    problems.append(f"{gadget_where}: {key} is not text")
            if gadget.get("configuration") is not None and not isinstance(gadget.get("configuration"), dict):
                problems.append(f"{gadget_where}: configuration is not an object")
            if not isinstance(gadget.get("warnings") or [], list):
                problems.append(f"{gadget_where}: warnings is not a list")
    return problems


def read_credentials(path: str) -> Dict[str, str]:
    """Reads KEY=VALUE lines. The values never reach the screen or the log."""
    try:
        with open(path, encoding="utf-8-sig") as f:
            lines = f.read().splitlines()
    except OSError:
        raise InputError(f"Cannot read the credentials file {path}. Create it with a JIRA_EMAIL=... and a "
                         f"JIRA_API_TOKEN=... line.") from None
    except UnicodeDecodeError:
        raise InputError(f"The credentials file {path} is not UTF-8 text. Save it as UTF-8.") from None
    credentials = {}
    for number, line in enumerate(lines, 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, separator, value = line.partition("=")
        if not separator:
            raise InputError(f"{path} line {number} is not KEY=VALUE.")
        credentials[key.strip()] = value.strip().strip("'\"")
    missing = [key for key in ("JIRA_EMAIL", "JIRA_API_TOKEN") if not credentials.get(key)]
    if missing:
        raise InputError(f"{path} has no {' and no '.join(missing)}.")
    return credentials


def read_dashboard_list(path: str, export: Dict[str, Any]) -> List[Dict[str, Any]]:
    """The file's dashboards that the list names, in the order of the list. The list is the CSV file that list
    wrote, maybe edited: one dashboard per line, its cloud ID first. Lines that start with # are skipped."""
    by_cloud_id = {str(d["cloudId"]): d for d in export["dashboards"] if d.get("cloudId")}
    try:
        with open(path, encoding="utf-8-sig") as f:
            lines = f.read().splitlines()
    except OSError as e:
        raise InputError(f"Cannot read {path}: {e.strerror}.") from None
    except UnicodeDecodeError:
        raise InputError(f"{path} is not UTF-8 text. Save it as CSV UTF-8.") from None

    selected: List[Dict[str, Any]] = []
    seen = set()
    problems = []
    for number, line in enumerate(lines, 1):
        # Spreadsheet apps may save the file with ; or tabs between the columns.
        first = re.split(r"[,;\t]", line, maxsplit=1)[0].strip().strip('"').strip()
        if not first or first.startswith("#") or first == LIST_HEADER[0]:
            continue
        if not first.isdigit():
            problems.append(f"line {number}: '{first}' is not a dashboard ID")
        elif first not in by_cloud_id:
            problems.append(f"line {number}: dashboard {first} is not in the migration file")
        elif first not in seen:
            seen.add(first)
            selected.append(by_cloud_id[first])

    if problems:
        more = f"\n  ... and {len(problems) - 20} more" if len(problems) > 20 else ""
        raise InputError(f"{path} has problems:\n  " + "\n  ".join(problems[:20]) + more)
    if not selected:
        raise InputError(f"{path} lists no dashboards.")
    return selected


def write_dashboard_list(path: str, dashboards: List[Dict[str, Any]], site: str) -> None:
    def text(value: Any) -> str:
        value = "" if value is None else str(value)
        # A spreadsheet app would run a cell that starts like a formula.
        return "'" + value if value[:1] in ("=", "+", "-", "@", "\t", "\r") else value

    try:
        # "x": never overwrites a list that was edited.
        with open(path, "x", encoding="utf-8-sig", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(LIST_HEADER)
            for d in dashboards:
                writer.writerow([text(cell) for cell in (
                    d["cloudId"], d.get("name"), d.get("ownerServerUsername"), len(d["gadgets"]), d.get("serverId"),
                    f"{site}/jira/dashboards/{d['cloudId']}")])
    except FileExistsError:
        raise InputError(f"{path} already exists. Pass another --output.") from None


class AccessJournal:
    """Dashboards that got the temporary edit access and may still have it. A run that stops before it removes
    the access leaves them here, and the next migrate removes it first."""

    def __init__(self, path: str, site: str):
        self.path = path
        self.site = site
        try:
            with open(path, encoding="utf-8") as f:
                self.entries: Dict[str, Dict[str, str]] = json.load(f)
        except FileNotFoundError:
            self.entries = {}
        except ValueError:
            raise InputError(f"{path} is damaged. Check the temporary edit access in the logs, then delete it.")

    def pending(self) -> Dict[str, str]:
        """Dashboard ID to the account ID that got the access."""
        return dict(self.entries.get(self.site, {}))

    def add(self, dashboard_id: str, account_id: str) -> None:
        self.entries.setdefault(self.site, {})[dashboard_id] = account_id
        self.save()

    def remove(self, dashboard_id: str) -> None:
        self.entries.get(self.site, {}).pop(dashboard_id, None)
        if not self.entries.get(self.site):
            self.entries.pop(self.site, None)
        self.save()

    def save(self) -> None:
        if not self.entries:
            if os.path.exists(self.path):
                os.remove(self.path)
            return
        temporary = self.path + ".tmp"
        with open(temporary, "w", encoding="utf-8") as f:
            json.dump(self.entries, f, indent=2)
        os.replace(temporary, self.path)


@contextlib.contextmanager
def migrate_lock(log_dir: str) -> Generator[None, None, None]:
    """Each migrate rewrites the whole access journal. A second run on the same log directory would drop the
    entries of the first, and access they record would never be removed."""
    path = os.path.join(log_dir, MIGRATE_LOCK_FILE)
    try:
        descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        raise InputError(f"Another migrate run uses {log_dir}, or one was killed. If no other run is going on, "
                         f"delete {path}.") from None
    os.write(descriptor, str(os.getpid()).encode())
    os.close(descriptor)
    try:
        yield
    finally:
        os.remove(path)


# What happens to a gadget

def to_cloud_configuration(configuration: Dict[str, Any],
                           calendar_mappings: Dict[str, str]) -> Tuple[Dict[str, Any], Optional[str]]:
    """Server calendars get new IDs on the cloud. Returns the configuration with the cloud calendar, and a
    warning when the gadget has to fall back to Normal Hours."""
    configuration = dict(configuration)
    calendar = configuration.get("calendar")
    if not calendar or calendar == NORMAL_HOURS_CALENDAR:
        return configuration, None

    cloud_calendar = calendar_mappings.get(str(calendar))
    if cloud_calendar and cloud_calendar != NORMAL_HOURS_CALENDAR:
        configuration["calendar"] = cloud_calendar
        return configuration, None

    configuration["calendar"] = NORMAL_HOURS_CALENDAR
    configuration["dayLength"] = NORMAL_HOURS_DAY_LENGTH
    warning = None if cloud_calendar else f"calendar {calendar} has no cloud calendar, so the gadget uses Normal Hours"
    return configuration, warning


def is_marked_for(marker: Any, transfer_id: str, server_id: Any) -> bool:
    return (isinstance(marker, dict) and marker.get("transferId") == transfer_id
            and marker.get("serverGadgetId") == server_id)


def find_existing_gadget(existing: List[Dict[str, Any]], transfer_id: str, module_key: str,
                         gadget: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    """The gadget on the dashboard that stands for the file's gadget. The marker of an earlier run of this file
    wins. Otherwise a Timepiece gadget at the same position counts, such as one added by hand, unless this
    file's marker says that it stands for another gadget."""
    server_id = gadget.get("serverId")
    for e in existing:
        if is_marked_for(e.get("marker"), transfer_id, server_id):
            return e
    for e in existing:
        marker = e.get("marker")
        if isinstance(marker, dict) and marker.get("transferId") == transfer_id:
            continue
        position = e.get("position") or {}
        if (e.get("moduleKey") == module_key and position.get("column") == gadget.get("column")
                and position.get("row") == gadget.get("row")):
            return e
    return None


def awaits_configuration(found: Dict[str, Any], transfer_id: str, server_id: Any) -> bool:
    """True when an earlier run added the gadget but did not write its configuration, and when a gadget with no
    marker has no settings. A run that stopped right after adding a gadget leaves such a gadget."""
    marker = found.get("marker")
    if marker is None:
        return bool(found.get("unconfigured"))
    return is_marked_for(marker, transfer_id, server_id) and not marker.get("configured")


def row_in_column(gadget: Dict[str, Any], existing: List[Dict[str, Any]]) -> Optional[int]:
    """Jira refuses a row past the end of the column. That happens when the gadgets above this one did not
    reach the cloud, such as those of an app the migration does not cover."""
    row = gadget.get("row")
    if row is None:
        return None
    in_column = sum(1 for e in existing if (e.get("position") or {}).get("column") == gadget.get("column"))
    return min(row, in_column)


def top_to_bottom(gadgets: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return sorted(gadgets, key=lambda g: (g.get("column") or 0, g.get("row") or 0))


class Run:
    """What dry and migrate share: the Jira client, the file, the checks and the counts for the summary."""

    def __init__(self, jira: Jira, export: Dict[str, Any], module_key: str, account_id: str, is_admin: bool,
                 calendar_mappings: Dict[str, str], journal: AccessJournal):
        self.jira = jira
        self.transfer_id = export["transferId"]
        self.module_key = module_key
        self.account_id = account_id
        self.is_admin = is_admin
        self.calendar_mappings = calendar_mappings
        self.journal = journal
        self.checks: List[str] = []
        # Set when a check finds that migrate cannot run as it should.
        self.setup_problem: Optional[str] = None
        self.counts: Counter = Counter()

    def plan_gadget(self, gadget: Dict[str, Any], prefix: str) -> Optional[Dict[str, Any]]:
        """Logs the warnings of the gadget and returns its cloud configuration, None when the server had none."""
        for warning in gadget.get("warnings") or []:
            log.warning("%s warning from the server: %s", prefix, warning)
            self.counts["server_warnings"] += 1
        configuration = gadget.get("configuration")
        if not gadget.get("configured") or not isinstance(configuration, dict):
            log.warning("%s not configured on the server, so it is added without configuration.", prefix)
            self.counts["not_configured_on_server"] += 1
            return None
        cloud_configuration, warning = to_cloud_configuration(configuration, self.calendar_mappings)
        if warning:
            log.warning("%s %s.", prefix, warning)
            self.counts["normal_hours"] += 1
        elif cloud_configuration.get("dayLength") != configuration.get("dayLength"):
            log.warning("%s calendar %s is Normal Hours on the cloud, which needs 24-hour days, so the day length "
                        "changes from %s to %s.", prefix, configuration.get("calendar"),
                        configuration.get("dayLength"), cloud_configuration.get("dayLength"))
            self.counts["day_length_changed"] += 1
        return cloud_configuration

    def read_existing_gadgets(self, cloud_id: str) -> List[Dict[str, Any]]:
        """The gadgets of a dashboard, with the marker of each Timepiece gadget. A Timepiece gadget with no
        marker also tells whether it has settings."""
        gadgets = self.jira.get_gadgets(cloud_id)
        for gadget in gadgets:
            gadget["marker"] = None
            if gadget.get("moduleKey") != self.module_key:
                continue
            gadget["marker"] = self.jira.get_item_property(cloud_id, gadget["id"], MARKER_PROPERTY_KEY)
            if gadget["marker"] is None:
                gadget["unconfigured"] = (
                    self.jira.get_item_property(cloud_id, gadget["id"], CONFIG_PROPERTY_KEY) is None)
        return gadgets

    def find_added_gadget(self, cloud_id: str, existing: List[Dict[str, Any]]) -> Optional[Any]:
        """Jira may have added the gadget of a POST that got no answer. Returns the ID of the one new Timepiece
        gadget on the dashboard, None when there is none or more than one."""
        known = {e.get("id") for e in existing}
        try:
            gadgets = self.jira.get_gadgets(cloud_id)
        except RestError as e:
            log.warning("  Cannot read the gadgets again to look for the added gadget: %s", e)
            return None
        added = [g.get("id") for g in gadgets if g.get("moduleKey") == self.module_key and g.get("id") not in known]
        return added[0] if len(added) == 1 else None


def dashboard_label(dashboard: Dict[str, Any]) -> str:
    return f"Dashboard {dashboard['cloudId']} '{dashboard.get('name')}' (server {dashboard.get('serverId')})"


def log_dashboard(index: int, total: int, dashboard: Dict[str, Any]) -> None:
    log.info("[%d/%d] %s: %d gadget(s)", index, total, dashboard_label(dashboard), len(dashboard["gadgets"]))


def log_gadget(dashboard: Dict[str, Any], gadget: Dict[str, Any]) -> None:
    """Starts the lines of each gadget in the migrate log, so its calls and warnings are not taken for another's."""
    log.info("%s '%s', column %s, row %s", gadget_prefix(dashboard, gadget), gadget.get("title"),
             gadget.get("column"), gadget.get("row"))


def gadget_prefix(dashboard: Dict[str, Any], gadget: Dict[str, Any]) -> str:
    return f"  [{dashboard['cloudId']}] gadget {gadget.get('serverId')}:"


# dry

def check_dashboard(run: Run, dashboard: Dict[str, Any]) -> None:
    """Works out what migrate would do with the dashboard. Only reads."""
    cloud_id = str(dashboard["cloudId"])
    gadgets = dashboard["gadgets"]

    existing: List[Dict[str, Any]] = []
    try:
        info = run.jira.get_dashboard(cloud_id)
        if info is not None:
            existing = run.read_existing_gadgets(cloud_id)
    except RestError as e:
        log.error("  Cannot read the dashboard: %s", e)
        run.counts["dashboards_failed"] += 1
        run.counts["to_check"] += len(gadgets)
        return

    if info is None:
        log.info("  Not visible to the account: private, or deleted. migrate gives the account edit access and "
                 "checks it then.")
        run.counts["not_visible"] += 1
        if not run.is_admin:
            log.error("  migrate cannot reach it: the account is not a Jira admin.")
            run.counts["unreachable"] += 1
        for gadget in gadgets:
            run.plan_gadget(gadget, gadget_prefix(dashboard, gadget))
            run.counts["to_check"] += 1
        return

    run.counts["readable"] += 1
    if not info.get("isWritable"):
        log.info("  Visible but not editable. migrate gives the account edit access while it works on it.")
        run.counts["needs_access"] += 1
        if not run.is_admin:
            log.error("  migrate cannot change it: the account is not a Jira admin.")
            run.counts["unreachable"] += 1

    for gadget in top_to_bottom(gadgets):
        prefix = gadget_prefix(dashboard, gadget)
        found = find_existing_gadget(existing, run.transfer_id, run.module_key, gadget)
        if found and not awaits_configuration(found, run.transfer_id, gadget.get("serverId")):
            log.info("%s already on the dashboard as cloud gadget %s.", prefix, found["id"])
            run.counts["already"] += 1
            continue
        run.plan_gadget(gadget, prefix)
        if found:
            log.info("%s cloud gadget %s waits for its configuration; migrate configures it.", prefix, found["id"])
            run.counts["to_configure"] += 1
        else:
            row = row_in_column(gadget, existing)
            log.info("%s migrate adds it at column %s, row %s.", prefix, gadget.get("column"), row)
            run.counts["to_add"] += 1
            existing.append({"position": {"column": gadget.get("column"), "row": row}})


# migrate

def remove_leftover_access(run: Run) -> None:
    for dashboard_id, account_id in run.journal.pending().items():
        try:
            run.jira.change_edit_access("removePermission", dashboard_id, account_id)
        except RestError as e:
            log.error("Cannot remove the temporary edit access that an earlier run left on dashboard %s for "
                      "account %s: %s", dashboard_id, account_id, e)
            run.counts["access_not_removed"] += 1
            continue
        run.journal.remove(dashboard_id)
        log.info("Removed the temporary edit access that an earlier run left on dashboard %s.", dashboard_id)
        run.counts["leftover_access_removed"] += 1


def add_access(run: Run, cloud_id: str) -> None:
    # Written down first, so the access is removed later even if this run stops right after the call.
    run.journal.add(cloud_id, run.account_id)
    try:
        run.jira.change_edit_access("addPermission", cloud_id, run.account_id)
    except RestError as e:
        # A client error means Jira did not give the access. With no answer or a server error it may have, so
        # the record stays and the next run removes the access.
        if e.status and e.status < 500:
            run.journal.remove(cloud_id)
        raise


def migrate_dashboard(run: Run, dashboard: Dict[str, Any]) -> None:
    cloud_id = str(dashboard["cloudId"])
    gadgets = dashboard["gadgets"]

    try:
        info = run.jira.get_dashboard(cloud_id)
    except RestError as e:
        log.error("  FAILED: cannot read the dashboard: %s", e)
        run.counts["dashboards_failed"] += 1
        run.counts["failed"] += len(gadgets)
        return

    access_added = False
    if not (info and info.get("isWritable")):
        # The journal keeps one account per dashboard. Access for this account would replace the entry of the
        # other account, and its access would never be removed.
        leftover = run.journal.pending().get(cloud_id)
        if leftover not in (None, run.account_id):
            log.error("  FAILED: the edit access that an earlier run gave account %s is still on the dashboard. "
                      "The next migrate removes it first.", leftover)
            run.counts["dashboards_failed"] += 1
            run.counts["failed"] += len(gadgets)
            return
        try:
            add_access(run, cloud_id)
        except RestError as e:
            log.error("  FAILED: cannot get edit access to the dashboard: %s", e)
            run.counts["dashboards_failed"] += 1
            run.counts["failed"] += len(gadgets)
            return
        access_added = True
        log.info("  Gave the account edit access while it works on the dashboard.")
        run.counts["access_added"] += 1

    failed_before = run.counts["failed"]
    try:
        try:
            existing = run.read_existing_gadgets(cloud_id)
        except RestError as e:
            log.error("  FAILED: cannot read the gadgets of the dashboard: %s", e)
            run.counts["failed"] += len(gadgets)
            return
        # Top to bottom, so each gadget lands where the server had it.
        for gadget in top_to_bottom(gadgets):
            log_gadget(dashboard, gadget)
            migrate_gadget(run, dashboard, gadget, existing)
    finally:
        if run.counts["failed"] > failed_before:
            run.counts["dashboards_failed"] += 1
        if access_added:
            try:
                run.jira.change_edit_access("removePermission", cloud_id, run.account_id)
                run.journal.remove(cloud_id)
                log.info("  Removed the temporary edit access.")
            except RestError as e:
                log.error("  Cannot remove the temporary edit access: %s. The next migrate removes it.", e)
                run.counts["access_not_removed"] += 1


def migrate_gadget(run: Run, dashboard: Dict[str, Any], gadget: Dict[str, Any],
                   existing: List[Dict[str, Any]]) -> None:
    cloud_id = str(dashboard["cloudId"])
    server_id = gadget.get("serverId")
    prefix = gadget_prefix(dashboard, gadget)

    found = find_existing_gadget(existing, run.transfer_id, run.module_key, gadget)
    if found and not awaits_configuration(found, run.transfer_id, server_id):
        log.info("%s already on the dashboard as cloud gadget %s.", prefix, found["id"])
        run.counts["already"] += 1
        return

    configuration = run.plan_gadget(gadget, prefix)
    marker = {"transferId": run.transfer_id, "serverGadgetId": server_id, "configured": configuration is None}
    if found:
        item_id = found["id"]
    else:
        row = row_in_column(gadget, existing)
        if row != gadget.get("row"):
            log.info("%s row %s does not exist on the dashboard, so it goes to row %s.", prefix, gadget.get("row"),
                     row)
        try:
            created = run.jira.add_gadget(cloud_id, run.module_key, gadget.get("title"), gadget.get("color"),
                                          gadget.get("column"), row)
            item_id = (created or {}).get("id")
            no_id = "Jira answered without the ID of the gadget"
        except RestError as e:
            # A client error means Jira did not add it. With no answer or a server error it may have.
            if e.status and e.status < 500:
                log.error("%s FAILED to add: %s", prefix, e)
                run.counts["failed"] += 1
                return
            item_id, no_id = None, str(e)
        if item_id is None:
            item_id = run.find_added_gadget(cloud_id, existing)
            if item_id is None:
                log.error("%s FAILED to add: %s. Check whether the dashboard got the gadget anyway.", prefix, no_id)
                run.counts["failed"] += 1
                return
            log.warning("%s %s, but the dashboard has a new Timepiece gadget %s. It is taken as this one.",
                        prefix, no_id, item_id)
        existing.append({"id": item_id, "moduleKey": run.module_key, "marker": marker,
                         "position": {"column": gadget.get("column"), "row": row}})

    marked = False
    try:
        # The marker goes first, so a gadget that misses its configuration is found and configured next time.
        run.jira.set_item_property(cloud_id, item_id, MARKER_PROPERTY_KEY, marker)
        marked = True
        if configuration is not None:
            run.jira.set_item_property(cloud_id, item_id, CONFIG_PROPERTY_KEY, configuration)
            run.jira.set_item_property(cloud_id, item_id, IS_CONFIGURED_PROPERTY_KEY, True)
            run.jira.set_item_property(cloud_id, item_id, MARKER_PROPERTY_KEY, {**marker, "configured": True})
    except RestError as e:
        run.counts["failed"] += 1
        if found or marked:
            log.error("%s FAILED to configure cloud gadget %s: %s. The next migrate configures it.", prefix, item_id,
                      e)
            return
        # Without its marker, the next run would not find a gadget that had to move up, and would add another.
        try:
            run.jira.remove_gadget(cloud_id, item_id)
        except RestError as removal_error:
            log.error("%s FAILED to mark cloud gadget %s: %s. It cannot be removed either: %s. Remove it from the "
                      "dashboard by hand, or the next migrate may add the gadget again.", prefix, item_id, e,
                      removal_error)
            return
        existing[:] = [g for g in existing if g.get("id") != item_id]
        log.error("%s FAILED to mark cloud gadget %s: %s. Removed it, so the next migrate adds it again.", prefix,
                  item_id, e)
        return

    if found:
        log.info("%s configured cloud gadget %s.", prefix, item_id)
        run.counts["configured"] += 1
    else:
        log.info("%s added as cloud gadget %s%s.", prefix, item_id, " and configured" if configuration else "")
        run.counts["added"] += 1


# Screen and log

class LiveLine:
    """One terminal line that changes in place. Dots move after the text while the run works, so a long wait, such
    as for a rate limit, does not look like a hang."""

    INTERVAL = 0.4

    def __init__(self, text: str):
        self.text = text
        self.frame = 0
        self.width = 0
        self.lock = threading.Lock()
        self.stopped = threading.Event()
        with self.lock:
            self.draw(self.dots())
        self.thread = threading.Thread(target=self.animate, daemon=True)
        self.thread.start()

    def update(self, text: str) -> None:
        with self.lock:
            self.text = text
            self.draw(self.dots())

    def stop(self, text: str) -> None:
        """Ends the line with the text, without dots."""
        self.stopped.set()
        self.thread.join()
        with self.lock:
            self.draw(text)
            print(flush=True)

    def dots(self) -> str:
        return self.text + ("." * (self.frame % 3 + 1)).ljust(3)

    def animate(self) -> None:
        while not self.stopped.wait(self.INTERVAL):
            with self.lock:
                self.frame += 1
                self.draw(self.dots())

    def draw(self, line: str) -> None:
        print("\r" + line.ljust(self.width), end="", flush=True)
        self.width = len(line)


SETUP_STATUS = "Checking the account, the Timepiece gadget and the calendar mappings"


@contextlib.contextmanager
def screen_status(text: str) -> Generator[None, None, None]:
    """Shows the text with moving dots while the block runs, then whether it finished. Without a terminal, the text
    and the result."""
    live = LiveLine(text) if sys.stdout.isatty() else None
    if live is None:
        print(f"{text}...", end="", flush=True)

    def finish(result: str) -> None:
        if live is not None:
            live.stop(f"{text}... {result}")
        else:
            print(f" {result}", flush=True)

    try:
        yield
    except KeyboardInterrupt:
        finish("stopped")
        raise
    except BaseException:
        finish("failed")
        raise
    finish("done")


class Progress:
    """One line on the screen that shows how far the run is, with moving dots. Without a terminal, a line per
    tenth."""

    def __init__(self, total: int):
        self.total = total
        self.live: Optional[LiveLine] = None
        self.terminal = sys.stdout.isatty()
        self.line = ""
        self.tenth = -1

    def show(self, done: int, text: str) -> None:
        self.line = f"[{done}/{self.total}] {text}"
        if self.terminal:
            # Two spaces, so the dots do not read as part of the last number.
            if self.live is None:
                self.live = LiveLine(self.line + "  ")
            else:
                self.live.update(self.line + "  ")
            return
        tenth = done * 10 // max(self.total, 1)
        if tenth > self.tenth:
            self.tenth = tenth
            print(self.line, flush=True)

    def close(self) -> None:
        if self.live is not None:
            self.live.stop(self.line)


SCREEN_WIDTH = 80


def section_line(title: str) -> str:
    return f"---- {title} ".ljust(SCREEN_WIDTH, "-")


def screen_section(title: str) -> None:
    print()
    print(section_line(title))


def file_hash(path: str) -> str:
    """Returns the first 12 characters of the SHA-256 of a file, or "unknown" when the file cannot be read."""
    try:
        with open(path, "rb") as file:
            content = file.read()
    except OSError:
        return "unknown"
    # Git or a download can turn LF into CRLF on Windows. That must not change the hash.
    return hashlib.sha256(content.replace(b"\r\n", b"\n")).hexdigest()[:12]


# Shown with the version, so support can tell whether a user changed the script. Hash of a released script:
# git show <tag>:scripts/gadget-migration/recreate_timepiece_gadgets.py | shasum -a 256 | cut -c1-12
# __file__ is missing when Python reads the script from stdin.
SCRIPT_HASH = file_hash(globals().get("__file__", ""))


def show_header(args: argparse.Namespace, started: datetime, site: str, transfer_id: str, log_path: str) -> None:
    rule = "=" * SCREEN_WIDTH
    print("\n".join([rule,
                     f"{args.mode}, started {started:%Y-%m-%d %H:%M:%S}",
                     f"  Version:  {VERSION} (sha256 {SCRIPT_HASH})",
                     f"  Python:   {platform.python_version()}",
                     f"  OS:       {platform.platform()}",
                     f"  File:     {args.file}",
                     f"  Site:     {site}",
                     f"  Transfer: {transfer_id}",
                     f"  Log:      {log_path}",
                     rule]))
    log.info("Mode %s, file %s, site %s, transfer %s", args.mode, args.file, site, transfer_id)


def start_log(log_dir: str, mode: str, started: datetime) -> str:
    os.makedirs(log_dir, exist_ok=True)
    base = os.path.join(log_dir, f"{mode}-{started:%Y%m%d-%H%M%S}")
    path, number = base + ".log", 1
    # Each run gets its own file, also two runs in the same second.
    while os.path.exists(path):
        number += 1
        path = f"{base}-{number}.log"
    handler = logging.FileHandler(path, encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s %(levelname)-7s %(message)s"))
    log.addHandler(handler)
    log.setLevel(logging.DEBUG)
    log.propagate = False
    log.info("Script version %s, sha256 %s, Python %s, OS %s", VERSION, SCRIPT_HASH, platform.python_version(),
             platform.platform())
    return path


def stop_log() -> None:
    for handler in list(log.handlers):
        if isinstance(handler, logging.FileHandler):
            handler.close()
            log.removeHandler(handler)


def show_error(text: str) -> None:
    # stdout may be buffered, such as when it goes to a file, so the header would come after the error.
    sys.stdout.flush()
    print("\n" + text, file=sys.stderr)


def report(lines: List[str]) -> None:
    """Shows the summary on the screen and writes it to the log. An empty line separates two groups on the
    screen."""
    screen_section("Summary")
    for line in lines:
        print(line)
        if line:
            log.info("%s", line)


def duration(started: datetime) -> str:
    seconds = int((datetime.now() - started).total_seconds())
    return f"{seconds // 60}m {seconds % 60}s" if seconds >= 60 else f"{seconds}s"


# Modes

def run_list(args: argparse.Namespace, export: Dict[str, Any], site: str, started: datetime) -> int:
    dashboards = export["dashboards"]
    migratable = []
    for dashboard in dashboards:
        gadgets = dashboard.get("gadgets") or []
        label = f"Dashboard server {dashboard.get('serverId')} '{dashboard.get('name')}'"
        if not dashboard.get("cloudId"):
            log.warning("%s: %d gadget(s). Jira Cloud Migration Assistant did not migrate the dashboard, so its "
                        "gadgets cannot be migrated.", label, len(gadgets))
        elif not gadgets:
            log.info("%s, cloud %s: no Timepiece gadgets.", label, dashboard["cloudId"])
        else:
            log.info("%s, cloud %s: %d gadget(s).", label, dashboard["cloudId"], len(gadgets))
            migratable.append(dashboard)

    output = args.output or f"dashboards-{started:%Y%m%d-%H%M%S}.csv"
    write_dashboard_list(output, migratable, site)
    not_migrated = sum(1 for d in dashboards if not d.get("cloudId"))
    report([
        f"Dashboards in the file: {len(dashboards)}",
        f"  can be migrated: {len(migratable)}, with {sum(len(d['gadgets']) for d in migratable)} gadget(s)",
        f"  not migrated by Jira Cloud Migration Assistant: {not_migrated}",
        "",
        f"Wrote {output}. Delete the lines of the dashboards to leave out.",
    ])
    return 0


def find_module_key(jira: Jira) -> str:
    keys = [g["moduleKey"] for g in jira.available_gadgets()
            if (g.get("moduleKey") or "").endswith(f"/{GADGET_MODULE}") and f"/{APP_ID}/" in g["moduleKey"]]
    production = [key for key in keys if f"/{APP_ID}/{PRODUCTION_ENVIRONMENT_ID}/" in key]
    if production:
        return production[0]
    if len(keys) == 1:
        return keys[0]
    if not keys:
        raise InputError("The Timepiece gadget is not available on the site. Install Timepiece first.")
    raise InputError("The site has more than one Timepiece gadget. Pass one with --module-key:\n  "
                     + "\n  ".join(keys))


def connect(args: argparse.Namespace, export: Dict[str, Any], site: str) -> Run:
    """Checks the setup and returns the run. Changes nothing."""
    credentials = read_credentials(args.credentials)
    jira, me = sign_in(site, credentials["JIRA_EMAIL"], credentials["JIRA_API_TOKEN"])
    is_admin = jira.is_admin()
    module_key = args.module_key or find_module_key(jira)
    log.info("Account %s (%s), Jira admin: %s", me.get("displayName"), me.get("accountId"), is_admin)
    log.info("Module key: %s", module_key)

    mappings: Dict[str, str] = {}
    mappings_problem, fix = None, ""
    token = credentials.get("TIMEPIECE_API_TOKEN")
    if not token:
        mappings_line = "no TIMEPIECE_API_TOKEN, so gadgets with a calendar use Normal Hours"
    else:
        try:
            mappings = Timepiece(args.timepiece_url, token).get_calendar_mappings(export["transferId"])
            mappings_line = f"{len(mappings)} read from Timepiece"
        except RestError as e:
            if e.status != 404:
                mappings_problem = f"cannot read them from Timepiece: {e}"
                mappings_line = mappings_problem
                fix = "Fix TIMEPIECE_API_TOKEN, or remove it to use Normal Hours."
            elif uses_server_calendars(export):
                # A wrong --timepiece-url answers 404 too. Normal Hours would then replace calendars that exist.
                mappings_problem = "Timepiece has no data of this transfer on this site (HTTP 404)"
                mappings_line = mappings_problem
                fix = ("Check --timepiece-url and that the Timepiece app migration of this transfer finished, or "
                       "remove TIMEPIECE_API_TOKEN to use Normal Hours.")
            else:
                mappings_line = "the transfer imported no Timepiece data on this site; no gadget needs a calendar"
    log.info("Calendar mappings: %s %s", mappings_line, json.dumps(mappings))

    run = Run(jira, export, module_key, me["accountId"], is_admin, mappings,
              AccessJournal(os.path.join(args.log_dir, ACCESS_JOURNAL_FILE), site))
    run.checks = [
        f"  Account: {me.get('displayName')}, "
        + ("Jira admin" if is_admin else "NOT a Jira admin, so dashboards it cannot edit cannot be migrated"),
        "  Timepiece gadget: available",
        f"  Calendar mappings: {mappings_line}",
    ]
    if mappings_problem:
        run.setup_problem = f"Calendar mappings {mappings_problem}. {fix}"
    return run


def uses_server_calendars(export: Dict[str, Any]) -> bool:
    return any(isinstance(g.get("configuration"), dict)
               and g["configuration"].get("calendar") not in (None, "", NORMAL_HOURS_CALENDAR)
               for d in export["dashboards"] for g in d["gadgets"] if g.get("configured"))


def run_dry(run: Run, dashboards: List[Dict[str, Any]], started: datetime) -> int:
    pending = run.journal.pending()
    screen_section(f"Progress: {len(dashboards)} dashboard(s)")
    progress = Progress(len(dashboards))
    c = run.counts

    def status() -> str:
        return f"to add {c['to_add']}, already there {c['already']}, not visible {c['not_visible']}"

    try:
        progress.show(0, status())
        for index, dashboard in enumerate(dashboards, 1):
            log_dashboard(index, len(dashboards), dashboard)
            check_dashboard(run, dashboard)
            progress.show(index, status())
    finally:
        progress.close()

    lines = ["Checks:"] + run.checks
    if pending:
        lines.append(f"  Temporary edit access left by a stopped run: {len(pending)} dashboard(s). migrate "
                     f"removes it first.")
    lines += ["", f"Dashboards: {len(dashboards)}", f"  readable: {c['readable']}"]
    if c["needs_access"]:
        lines.append(f"  readable but not editable: {c['needs_access']}. migrate gives temporary edit access.")
    if c["not_visible"]:
        lines.append(f"  not visible, private or deleted: {c['not_visible']}. migrate gives temporary edit access "
                     f"and checks them then.")
    if c["dashboards_failed"]:
        lines.append(f"  could not be read: {c['dashboards_failed']}. See the log.")
    if c["unreachable"]:
        lines.append(f"  out of reach without the Jira admin permission: {c['unreachable']}")
    lines += ["", f"Gadgets: {c['to_add']} to add, {c['to_configure']} to configure, {c['already']} already there"]
    if c["to_check"]:
        lines.append(f"  on dashboards that migrate checks: {c['to_check']}")
    lines += [
        f"  use Normal Hours, since their calendar has no cloud calendar: {c['normal_hours']}",
        f"  added without configuration, since they were not configured on the server: "
        f"{c['not_configured_on_server']}",
    ]
    if c["day_length_changed"]:
        lines.append(f"  use 24-hour days, since their calendar is Normal Hours on the cloud: {c['day_length_changed']}")
    if c["server_warnings"]:
        lines.append(f"  warnings from the server: {c['server_warnings']}")
    lines += ["", f"Nothing was changed. Took {duration(started)}."]
    report(lines)
    return 1 if run.setup_problem or c["dashboards_failed"] or c["unreachable"] else 0


def run_migrate(run: Run, dashboards: List[Dict[str, Any]], started: datetime) -> int:
    screen_section(f"Progress: {len(dashboards)} dashboard(s)")
    progress = Progress(len(dashboards))
    c = run.counts

    def status() -> str:
        return f"added {c['added'] + c['configured']}, already there {c['already']}, failed {c['failed']}"

    try:
        progress.show(0, status())
        for index, dashboard in enumerate(dashboards, 1):
            log_dashboard(index, len(dashboards), dashboard)
            migrate_dashboard(run, dashboard)
            progress.show(index, status())
    finally:
        progress.close()
        lines = ["Checks:"] + run.checks + [
            "",
            f"Dashboards: {len(dashboards)}, {c['dashboards_failed']} with failures",
            "",
            f"Gadgets: {c['added']} added, {c['configured']} configured, {c['already']} already there, "
            f"{c['failed']} failed",
        ]
        if c["normal_hours"]:
            lines.append(f"  use Normal Hours, since their calendar has no cloud calendar: {c['normal_hours']}")
        if c["day_length_changed"]:
            lines.append(f"  use 24-hour days, since their calendar is Normal Hours on the cloud: "
                         f"{c['day_length_changed']}")
        if c["not_configured_on_server"]:
            lines.append(f"  added without configuration, since they were not configured on the server: "
                         f"{c['not_configured_on_server']}")
        if c["server_warnings"]:
            lines.append(f"  warnings from the server: {c['server_warnings']}")
        lines += ["", f"Temporary edit access: given on {c['access_added']} dashboard(s) and removed afterwards"]
        if c["leftover_access_removed"]:
            lines.append(f"  left by an earlier run and removed now: {c['leftover_access_removed']}")
        if c["access_not_removed"]:
            lines.append(f"  could not be removed from {c['access_not_removed']} dashboard(s). The next migrate tries "
                         f"again.")
        lines += ["", f"Took {duration(started)}."]
        if c["failed"] or c["access_not_removed"]:
            lines.append("Run the same command again to retry. Gadgets already there are not added again.")
        report(lines)
    return 1 if c["failed"] or c["access_not_removed"] else 0


def parse_args(argv: Optional[List[str]]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Recreate Timepiece gadgets on Jira Cloud dashboards from a gadget "
                                                 "migration file.")
    parser.add_argument("--version", action="version", version=f"%(prog)s {VERSION} (sha256 {SCRIPT_HASH})")
    common = argparse.ArgumentParser(add_help=False)
    common.add_argument("file", help="the gadget migration file from the server")
    common.add_argument("--site", help="Jira Cloud URL; defaults to cloudUrl in the file")
    common.add_argument("--log-dir", default=DEFAULT_LOG_DIR, help=f"where the logs go (default: {DEFAULT_LOG_DIR})")

    online = argparse.ArgumentParser(add_help=False)
    online.add_argument("--dashboards", required=True,
                        help="CSV file of the dashboards to work on, as list wrote it; the first column is the "
                             "cloud dashboard ID")
    online.add_argument("--credentials", default=DEFAULT_CREDENTIALS_FILE,
                        help=f"file with JIRA_EMAIL, JIRA_API_TOKEN and TIMEPIECE_API_TOKEN lines "
                             f"(default: {DEFAULT_CREDENTIALS_FILE})")
    online.add_argument("--module-key", help="gadget module key; found on the site by default")
    online.add_argument("--timepiece-url", default=DEFAULT_TIMEPIECE_URL,
                        help=f"Timepiece REST API URL (default: {DEFAULT_TIMEPIECE_URL})")
    online.add_argument("--allow-any-site", action="store_true",
                        help="send the Jira token to a site outside "
                             + " and ".join("*" + suffix for suffix in ATLASSIAN_SITE_SUFFIXES))

    modes = parser.add_subparsers(dest="mode", required=True)
    list_mode = modes.add_parser("list", parents=[common],
                                 help="write the dashboards that can be migrated to a CSV file")
    list_mode.add_argument("--output", help="CSV file to write (default: dashboards-<timestamp>.csv)")
    modes.add_parser("dry", parents=[common, online], help="check the listed dashboards; changes nothing")
    modes.add_parser("migrate", parents=[common, online], help="add the gadgets of the listed dashboards")
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    started = datetime.now()
    log_path = start_log(args.log_dir, args.mode, started)
    try:
        export = read_migration_file(args.file)
        site = (args.site or export.get("cloudUrl") or "").rstrip("/")
        if not site:
            raise InputError("The migration file has no cloudUrl. Pass --site.")
        show_header(args, started, site, export["transferId"], log_path)
        for message in export.get("errors") or []:
            log.error("Error from the server export: %s", message)
        for message in export.get("warnings") or []:
            log.warning("Warning from the server export: %s", message)
        if export.get("errors"):
            print(f"\nThe file has {len(export['errors'])} error(s) from the server export. See the log.")

        if args.mode == "list":
            return run_list(args, export, site, started)

        check_site(site, args.allow_any_site)
        check_https(args.timepiece_url, "--timepiece-url")
        dashboards = read_dashboard_list(args.dashboards, export)
        screen_section("Setup")
        if args.mode == "dry":
            with screen_status(SETUP_STATUS):
                run = connect(args, export, site)
            return run_dry(run, dashboards, started)
        with migrate_lock(args.log_dir):
            with screen_status(SETUP_STATUS):
                run = connect(args, export, site)
                if run.setup_problem:
                    raise InputError(run.setup_problem)
                remove_leftover_access(run)
            return run_migrate(run, dashboards, started)
    except InputError as e:
        log.error("%s", e)
        show_error(f"Error: {e}")
        return 2
    except RestError as e:
        log.exception("Stopped")
        show_error(f"Error: {e}. See {log_path}.")
        return 2
    except KeyboardInterrupt:
        log.warning("Stopped by the user.")
        show_error("Stopped. Run the same command again to continue.")
        return 130
    except Exception as e:
        log.exception("Stopped by an unexpected error")
        show_error(f"Unexpected error: {e!r}. See {log_path}. Run the same command again to continue.")
        return 3
    finally:
        stop_log()


if __name__ == "__main__":
    sys.exit(main())
