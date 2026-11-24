# timepiece-cloud-migration

Scripts and other material supporting Timepiece-Time in Status migrations from Jira Data Center to Jira Cloud.

## Gadget migration

Jira Cloud Migration Assistant moves dashboards but not the Timepiece gadgets on them.
[`recreate_timepiece_gadgets.py`](recreate_timepiece_gadgets.py) adds those gadgets to the migrated cloud dashboards.

Read the full guide before you run it:
[Server/DC to Cloud Timepiece Gadget Migration](https://documentation.obss.tech/timepiece-time-in-status-for-jira/cloud/server-dc-to-cloud-timepiece-gadget-migration)

Quick reference:

```sh
./recreate_timepiece_gadgets.py list <migration file>
./recreate_timepiece_gadgets.py dry <migration file> --dashboards <CSV file>
./recreate_timepiece_gadgets.py migrate <migration file> --dashboards <CSV file>
```

Needs Python 3.8 or later. No third-party packages.
