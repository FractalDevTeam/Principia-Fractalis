#!/usr/bin/env python3
"""Find every ordering inversion in a mathlib `Mathlib.lean`, which is what
`lake exe mk_all --check` is really complaining about.

Doing this instead of running `lake exe mk_all` because mk_all needs the
branch's own toolchain built (v4.33.0-rc1 here, three months old). The check is
deterministic either way: mk_all emits one import line per module in sorted
order, so an inversion in the existing list is exactly the discrepancy.

Prints EVERY inversion, not just the first, so a one-line fix is not mistaken
for a complete fix.
"""
import io
import sys

path = sys.argv[1]
lines = io.open(path, encoding="utf-8").read().split("\n")

mods = []
for i, L in enumerate(lines, 1):
    s = L.strip()
    for pre in ("public import ", "import "):
        if s.startswith(pre):
            mods.append((i, s[len(pre):].strip()))
            break

# Only the Mathlib.* block is sorted by mk_all; Std/Init style lines sit first.
mathlib = [(i, m) for i, m in mods if m.startswith("Mathlib.")]
other = [(i, m) for i, m in mods if not m.startswith("Mathlib.")]

print("%s: %d import lines (%d Mathlib.*, %d other: %s)" % (
    path, len(mods), len(mathlib), len(other),
    ", ".join(m for _, m in other) or "-"))

names = [m for _, m in mathlib]
inversions = [(mathlib[k][0], names[k], mathlib[k + 1][0], names[k + 1])
              for k in range(len(names) - 1) if names[k] > names[k + 1]]

print("")
if not inversions:
    print("SORTED: no inversions -- mk_all --check would pass on ordering")
else:
    print("INVERSIONS (%d):" % len(inversions))
    for l1, n1, l2, n2 in inversions:
        print("  line %d  %s" % (l1, n1))
        print("  line %d  %s   <-- sorts BEFORE the line above" % (l2, n2))

dups = sorted(set(n for n in names if names.count(n) > 1))
print("")
print("duplicates: %s" % (", ".join(dups) if dups else "none"))
sys.exit(1 if inversions or dups else 0)
