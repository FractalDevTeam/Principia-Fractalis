#!/usr/bin/env python3
"""
Port the three c = 13/2 Gate-1 add-on modules (+ the residue base they sit on)
to c = 27/4.

WHY THIS IS A TEXTUAL PORT AND NOT A REDERIVATION
-------------------------------------------------
`c` enters the node functions only through the phase factor
`cos((c/2)·u)` / `sin((c/2)·u)`, and every add-on majorant discards that factor
via `|cos| ≤ 1` / `|sin| ≤ 1`. Verified before porting: across all four source
files the ONLY uses of the phase are `Real.abs_cos_le_one` /
`Real.abs_sin_le_one` -- no `cos_pos`, `cos_nonneg`, `cos_le_*`, no numeric
evaluation. `OmegaTailBound_c13_2`'s own docstring says so outright: "The
analytic argument is independent of [c]".

Consequence: the three add-on CONSTANTS are c-independent, so the ported
modules must prove the SAME bounds (residue 7/10^7, analytic tail 12/10^8,
omega-gap epsOm) at c = 27/4. That is the check -- if a ported constant had to
move, the premise of this port would be wrong.

CORRUPTION GUARDS
-----------------
The `231/10^6` lesson: a naive `13/2 -> 27/4` would also rewrite `113/2` and
`13/25`. Every numeric substitution below is anchored with negative lookaround
on digits and dots, and each is followed by a post-assertion. `-27/2` inside
`resMaj` comes from the pi*exp(u) linearisation and has nothing to do with c;
it must survive untouched, which is asserted explicitly.
"""
import io
import re

SRC = "addons/"
OUT = "addons_c27_4/"

FILES = {
    "ResidueBound_c13_2_three_halves_to_5_2026_10_16.lean":
        "ResidueBound_c27_4_three_halves_to_5_2026_10_19.lean",
    "ResidueBoundTight_c13_2_2026_10_18.lean":
        "ResidueBoundTight_c27_4_2026_10_19.lean",
    "AnalyticTailBound_c13_2_2026_10_16.lean":
        "AnalyticTailBound_c27_4_2026_10_19.lean",
    "OmegaTailBound_c13_2_2026_10_16.lean":
        "OmegaTailBound_c27_4_2026_10_19.lean",
}

# module-path renames, applied FIRST and longest-first so the dates of the
# four NEW modules change while the two pre-existing c=27/4 deps keep theirs
MODULE_RENAMES = [
    ("PF.Analytic.FourierPanels.ResidueBound_c13_2_three_halves_to_5_2026_10_16",
     "PF.Analytic.FourierPanels.ResidueBound_c27_4_three_halves_to_5_2026_10_19"),
    ("PF.Analytic.FourierPanels.ResidueBoundTight_c13_2_2026_10_18",
     "PF.Analytic.FourierPanels.ResidueBoundTight_c27_4_2026_10_19"),
    ("PF.Analytic.FourierPanels.AnalyticTailBound_c13_2_2026_10_16",
     "PF.Analytic.FourierPanels.AnalyticTailBound_c27_4_2026_10_19"),
    ("PF.Analytic.FourierPanels.OmegaTailBound_c13_2_2026_10_16",
     "PF.Analytic.FourierPanels.OmegaTailBound_c27_4_2026_10_19"),
    # pre-existing c=27/4 modules: name changes, date does NOT
    ("PF.Analytic.FourierPanels.CoreDefs_c13_2_2026_10_16",
     "PF.Analytic.FourierPanels.CoreDefs_c27_4_2026_10_16"),
    ("PF.Analytic.FourierPanels.Seg01Range_c13_2_2026_10_16",
     "PF.Analytic.FourierPanels.Seg01Range_c27_4_2026_10_16"),
]

NB = r"(?<![0-9.])"      # not preceded by a digit or a dot
NA = r"(?![0-9.])"       # not followed by a digit or a dot

# (regex, replacement, human description)
NUMERIC = [
    (NB + r"3\.25" + NA, "3.375", "phase c/2: 3.25 -> 3.375"),
    (NB + r"13/2" + NA, "27/4", "centre 13/2 -> 27/4"),
    (NB + r"13 / 2" + NA, "27 / 4", "centre 13 / 2 -> 27 / 4"),
    (NB + r"13/4" + NA, "27/8", "c/2 as a fraction 13/4 -> 27/8"),
]

import os
os.makedirs(OUT, exist_ok=True)

report = []
for src, dst in FILES.items():
    s = io.open(SRC + src, encoding="utf-8").read()
    orig = s

    # 0. record what must survive untouched
    n_27_2 = len(re.findall(r"-27 / 2|-\(27 / 2", s)) + len(re.findall(r"27/2", s))
    n_14 = s.count("(-14 : ℝ)")

    # 1. module paths
    for a, b in MODULE_RENAMES:
        s = s.replace(a, b)
    assert "_c13_2_2026" not in s.replace("PF.Analytic.FourierPanels.", ""), \
        f"{src}: a module path escaped renaming"

    # 2. bare module basenames in prose headers (# PF.Analytic...) already done;
    #    now the namespace / identifier token
    n_c13 = s.count("c13_2")
    s = s.replace("c13_2", "c27_4")
    assert "c13_2" not in s, f"{src}: c13_2 left over"

    # 3. numeric substitutions, each guarded and counted
    counts = {}
    for pat, rep, desc in NUMERIC:
        s, k = re.subn(pat, rep, s)
        counts[desc] = k

    # 4. post-assertions
    assert "3.25" not in s, f"{src}: a 3.25 survived"
    assert re.search(NB + r"13/2" + NA, s) is None, f"{src}: a bare 13/2 survived"
    # the pi-linearisation constants must be untouched
    n_27_2_after = len(re.findall(r"-27 / 2|-\(27 / 2", s)) + len(re.findall(r"27/2", s))
    assert n_27_2_after == n_27_2, \
        f"{src}: resMaj's 27/2 was corrupted ({n_27_2} -> {n_27_2_after})"
    assert s.count("(-14 : ℝ)") == n_14, f"{src}: resMaj's -14 was corrupted"
    # no accidental 3.3755 / 27/44 style damage
    assert "3.3755" not in s and "27/44" not in s and "3.3375" not in s, \
        f"{src}: numeric corruption detected"
    assert s != orig

    # 5. provenance line
    s = s.replace(
        "SPDX-License-Identifier: Apache-2.0",
        "Ported to c = 27/4 from the c = 13/2 module by codex/port_addons_c27_4.py\n"
        "(2026-10-19). `c` enters only through the phase, which every majorant\n"
        "discards via |cos| <= 1 / |sin| <= 1, so all three add-on constants are\n"
        "c-independent and the bounds proved here are identical to the c = 13/2 ones.\n"
        "\n"
        "SPDX-License-Identifier: Apache-2.0", 1)

    io.open(OUT + dst, "w", encoding="utf-8", newline="\n").write(s)
    report.append((dst, s.count("\n") + 1, n_c13, counts))

for dst, n, n_c13, counts in report:
    print(f"{dst}  ({n} lines)")
    print(f"    c13_2 -> c27_4 : {n_c13}")
    for d, k in counts.items():
        if k:
            print(f"    {d} : {k}")
