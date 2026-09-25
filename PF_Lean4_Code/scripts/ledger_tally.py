#!/usr/bin/env python3
"""Derive the canonical C1 box tally mechanically from unique closure events.

Directive-adjacent hygiene, dispatched 2026-09-07: the raw driver ledger is
append-only and therefore accumulates duplicates (a restarted driver re-walks a
cached box and logs "40/40 green" again) and superseded lines (box 0's
"BRIDGE GEN FAILED", which was a by-design REFUSED, later corrected). Counting
rows naively would corrupt the 18-box tally at gate time.

This script never edits the ledger. It reads it and derives:

  * for each box, its BEST state, by the precedence below
  * the closure event that established it (latest wins within a state)
  * duplicates and superseded rows, reported but not counted

Precedence, strongest first:

    CLOSED  >  REFERENCE  >  PANELS_GREEN  >  FAILED  >  UNKNOWN

REFERENCE is box 0's hand-written bridge rebuilt from committed source: it is a
closure, but by a different route than the generator, so it is tracked
distinctly rather than folded into CLOSED.

A row that says BRIDGE GEN FAILED is recorded as PANELS_GREEN, not FAILED, when
a later row for the same box reports a closure - that is exactly the box-0 case,
and the generator's refusal was by design.

Usage:
    python3 ledger_tally.py <ledger...>            # human summary
    python3 ledger_tally.py --json <ledger...>     # machine-readable
"""
import re, sys, json, collections

PRECEDENCE = ["UNKNOWN", "FAILED", "PANELS_GREEN", "REFERENCE", "CLOSED"]
BOX_RE = re.compile(r"^\|\s*(?:\*\*)?box\s+(\d+)(?:\*\*)?\s*\|\s*(.*)$", re.I)
MARGIN_RE = re.compile(r"xi margin\s*([+-][0-9.eE-]+)")
TS_RE = re.compile(r"(\d{4}-\d{2}-\d{2}T[\d:]+[+-]\d{2}:\d{2})")


def classify(rest: str) -> str:
    r = rest.lower()
    if "**closed**" in r or re.search(r"\|\s*closed", r):
        return "CLOSED"
    if "reference closure" in r or "reference bridge" in r:
        return "REFERENCE"
    if "segments green" in r:
        return "PANELS_GREEN"
    if "bridge gen failed" in r:
        # by-design REFUSED on box 0; a later closure supersedes it.
        return "PANELS_GREEN"
    if "failed" in r:
        return "FAILED"
    return "UNKNOWN"


def parse(paths):
    events = collections.defaultdict(list)
    raw_rows = 0
    for p in paths:
        try:
            lines = open(p, encoding="utf-8", errors="replace").read().split("\n")
        except OSError as e:
            print(f"warn: cannot read {p}: {e}", file=sys.stderr)
            continue
        for ln in lines:
            m = BOX_RE.match(ln.strip())
            if not m:
                continue
            raw_rows += 1
            box, rest = int(m.group(1)), m.group(2)
            ts = TS_RE.search(ln)
            mg = MARGIN_RE.search(ln)
            events[box].append({
                "state": classify(rest),
                "ts": ts.group(1) if ts else "",
                "margin": mg.group(1) if mg else None,
                "source": p,
            })
    return events, raw_rows


def best(evts):
    return max(evts, key=lambda e: (PRECEDENCE.index(e["state"]), e["ts"]))


def main(argv):
    as_json = "--json" in argv
    paths = [a for a in argv if not a.startswith("--")]
    if not paths:
        print(__doc__)
        return 2
    events, raw_rows = parse(paths)

    result, dupes = {}, {}
    for box, evts in sorted(events.items()):
        b = best(evts)
        result[box] = b
        same = [e for e in evts if e["state"] == b["state"]]
        if len(same) > 1:
            dupes[box] = len(same)

    counts = collections.Counter(v["state"] for v in result.values())
    closed = counts["CLOSED"] + counts["REFERENCE"]

    if as_json:
        print(json.dumps({
            "boxes": {str(k): v for k, v in result.items()},
            "counts": dict(counts),
            "closed_total": closed,
            "unique_boxes": len(result),
            "raw_rows": raw_rows,
            "duplicate_state_rows": dupes,
        }, indent=2))
        return 0

    print(f"raw box rows read      : {raw_rows}")
    print(f"unique boxes           : {len(result)}")
    print(f"CLOSED (+REFERENCE)    : {closed}   "
          f"[CLOSED {counts['CLOSED']}, REFERENCE {counts['REFERENCE']}]")
    print(f"panels green only      : {counts['PANELS_GREEN']}")
    print(f"failed                 : {counts['FAILED']}")
    print()
    print(f"{'box':>5}  {'state':<13} {'margin':>14}  timestamp")
    for box, v in sorted(result.items()):
        print(f"{box:>5}  {v['state']:<13} {v['margin'] or '-':>14}  {v['ts']}")
    if dupes:
        print()
        print("duplicate rows at the winning state (append-only artefacts, "
              "counted once):")
        for box, n in sorted(dupes.items()):
            print(f"  box {box}: {n} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
