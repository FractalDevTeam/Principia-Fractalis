#!/usr/bin/env python3
"""Require one exact three-axiom print per source directive, in source order."""
import argparse
from pathlib import Path
import re
import sys

EXPECTED = {"propext", "Classical.choice", "Quot.sound"}


def check(source, log):
    # This gate is for generated march sources, whose directives occupy whole lines.
    names = re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", source, re.MULTILINE)
    if not names:
        raise ValueError("source has no #print axioms directives")
    if re.search(r"\b(?:sorryAx|nativeDecide\w*|ofReduceBool)\b", log):
        raise ValueError("forbidden axiom present")
    records = re.findall(r"'([^'\n]+)'\s+depends on axioms:\s*\[([^\]]*)\]", log)
    if len(records) != len(names) or log.count("depends on axioms:") != len(records):
        raise ValueError(f"missing/malformed/extra prints: expected {len(names)}, got {len(records)}")
    for requested, (printed, raw) in zip(names, records):
        if printed != requested and not printed.endswith("." + requested):
            raise ValueError(f"declaration mismatch: requested {requested}, printed {printed}")
        axioms = [item.strip() for item in raw.split(",")]
        if len(axioms) != 3 or set(axioms) != EXPECTED:
            raise ValueError(f"unexpected axiom set for {printed}: {raw.strip()}")
    return len(records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    try:
        count = check(args.source.read_text(encoding="utf-8"), args.log.read_text(encoding="utf-8"))
    except (ValueError, OSError) as exc:
        print(f"FAILED axiom bar: {exc}", file=sys.stderr)
        return 1
    print(f"axiom-bar OK: {args.log.name}: {count} declarations, all [propext, Classical.choice, Quot.sound]")
    return 0


if __name__ == "__main__":
    sys.exit(main())
