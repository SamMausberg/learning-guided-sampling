"""Compare two runs of checks/research_checks.py, ignoring the elapsed time."""

import json
import sys


def main() -> int:
    recorded, fresh = (json.loads(open(p, encoding="utf-8").read()) for p in sys.argv[1:3])
    for record in (recorded, fresh):
        record.pop("elapsed_seconds", None)
    if recorded != fresh:
        print("finite checks differ from the recorded results", file=sys.stderr)
        return 1
    print("finite checks reproduce the recorded results")
    return 0


if __name__ == "__main__":
    sys.exit(main())
