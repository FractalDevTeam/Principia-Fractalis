#!/usr/bin/env python3
"""Apply the OLD and the PROPOSED gate logic to a REAL build transcript.

The committed self-test (codex/ci_gate_selftest.sh) proves the old logic cannot
fail on synthetic fixtures. This answers the question the fixtures cannot: on
the tree as it stands TONIGHT, what would a gate that CAN fail actually report?

Input is an ordinary `lake build` log, so no rebuild and no lock is needed.

Scope is stated honestly in the output: this is the import closure of whatever
was built, not necessarily the whole PF target.
"""
import io
import re
import sys
from collections import Counter

ALLOWED = {
    "propext", "Classical.choice", "Quot.sound",
    # the four named conditional hypotheses verify.sh explicitly permits
    "Hardy1914_published_theorem_substrate_citation",
    "Mayer1991_Cohen2025_substrate_HP_program_citation",
    "Mayer1991_Cohen2025_T3_sym_HP_program_citation",
    "framework_substrate_pins_bulletproof_bundle",
}

path = sys.argv[1]
text = io.open(path, encoding="utf-8", errors="replace").read()

# --- PROPOSED logic: structural parse, DOTALL, so Lean's line wrapping is fine
# The name is matched with a GREEDY [^\n]+ anchored on the marker, not with
# [^']+. Lean declaration names may END IN A PRIME, which it prints inside its
# own quotes as "...sub_ne_zero'' depends on axioms:" -- so a non-prime-aware
# [^']+ stops at the prime inside the name and the record is silently dropped.
# Measured on a real transcript: 4 of 555 records were primed and invisible.
# [^\n]+ keeps the name on one line (so it cannot swallow neighbours) while
# DOTALL still lets the AXIOM LIST wrap across lines.
rec = re.compile(
    r"'(?P<name>[^\n]+)' depends on axioms: \[(?P<axioms>[^\]]*)\]",
    re.DOTALL)

records = []
for m in rec.finditer(text):
    axioms = [a.strip() for a in m.group("axioms").split(",") if a.strip()]
    records.append((m.group("name"), axioms))

# --- OLD logic, reproduced exactly: line-select then line-DELETE by allowlist
old_selected = [L for L in text.split("\n") if "depends on axioms:" in L]
old_kept = [L for L in old_selected
            if not re.search(r"propext|Classical\.choice|Quot\.sound", L)]
for pat in ("Hardy1914_published_theorem_substrate_citation",
            "Mayer1991_Cohen2025_substrate_HP_program_citation",
            "Mayer1991_Cohen2025_T3_sym_HP_program_citation",
            "framework_substrate_pins_bulletproof_bundle"):
    old_kept = [L for L in old_kept if pat not in L]

print("transcript: %s" % path)
print("")
print("RECORDS PARSED")
print("  proposed (structural, DOTALL) : %d" % len(records))
print("  old (first grep, lines only)  : %d" % len(old_selected))
print("  -> delta vs old line-grep: %d"
      % (len(records) - len(old_selected)))
print("     long axiom lists and continuation lines lack the marker text.")
print("")

names_bad = []
axset = Counter()
for name, axioms in records:
    axset[", ".join(axioms)] += 1
    bad = [a for a in axioms if a not in ALLOWED]
    if bad:
        names_bad.append((name, bad))

print("DISTINCT AXIOM SETS IN THE CLOSURE (%d)" % len(axset))
for s, n in axset.most_common():
    flag = "" if all(a.strip() in ALLOWED
                     for a in s.split(",") if a.strip()) else "   <-- VIOLATION"
    print("  %4d x  [%s]%s" % (n, s, flag))
print("")

print("VERDICTS")
print("  OLD  : %s   (kept %d lines after the allowlist deletion)"
      % ("PASS" if not old_kept else "FAIL", len(old_kept)))
if len(records) == 0:
    print("  NEW  : FAIL(checked-nothing) -- zero records parsed")
elif names_bad:
    print("  NEW  : FAIL(axiom) -- %d declaration(s) outside the allowlist"
          % len(names_bad))
    for name, bad in names_bad[:20]:
        print("           %s  ->  %s" % (name, bad))
else:
    print("  NEW  : PASS -- %d records, every axiom name inside the allowlist"
          % len(records))
print("")
print("NOTE ON SCOPE: this is the import closure actually built in that log,")
print("not a guarantee about the whole PF target.")
