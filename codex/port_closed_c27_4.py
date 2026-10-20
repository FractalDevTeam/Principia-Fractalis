#!/usr/bin/env python3
"""
Port the c = 13/2 UNCONDITIONAL pilot to c = 27/4, on the hybrid enclosure.

Same premise as port_addons_c27_4.py: `c` enters only through the phase, and
every bound here discards it with |cos| <= 1 / |sin| <= 1. What is NOT a
textual substitution, and is handled explicitly below:

  * the enclosure source becomes the HYBRID assemble, so the four headline
    rationals change to the hybrid values;
  * the box composition goes through pilot_r1_box_c27_4_r1_16_from_addons
    (2 bounds + hEps) rather than the 13/2 scaffold's ..._closed (4 bounds);
  * Gate-1 arithmetic is already proved in the hybrid assemble.
"""
import io
import re
import os

SRC = "addons/R1_c13_2_r1_16_pointwise_CLOSED_2026_10_16.lean"
OUT = "R1_c27_4_r1_16_pointwise_UNCONDITIONAL_2026_10_19.lean"

# hybrid enclosure values, from Assemble_c27_4_threehalves_HYBRID
R_LB = "4510553327 / 320000000000"
R_UB = "4802446903 / 320000000000"
I_LB = "161621101 / 320000000000"
I_UB = "21496359 / 16000000000"

s = io.open(SRC, encoding="utf-8").read()
orig = s

# ---- 1. imports -------------------------------------------------------
IMPORTS = [
    ("import PF.Analytic.PilotBoxes.R1_c13_2_r_pointwise_SCAFFOLD_2026_10_16",
     "import PF.Analytic.PilotBoxes.R1_c27_4_r1_16_HYBRID_2026_10_19"),
    ("import PF.Analytic.FourierPanels.Assemble_c13_2_threehalves_2026_10_16",
     "import PF.Analytic.FourierPanels.Assemble_c27_4_threehalves_HYBRID_2026_10_19"),
    ("import PF.Analytic.FourierPanels.ResidueBound_c13_2_three_halves_to_5_2026_10_16",
     "import PF.Analytic.FourierPanels.ResidueBound_c27_4_three_halves_to_5_2026_10_19"),
    ("import PF.Analytic.FourierPanels.ResidueBoundTight_c13_2_2026_10_18",
     "import PF.Analytic.FourierPanels.ResidueBoundTight_c27_4_2026_10_19"),
    ("import PF.Analytic.FourierPanels.AnalyticTailBound_c13_2_2026_10_16",
     "import PF.Analytic.FourierPanels.AnalyticTailBound_c27_4_2026_10_19"),
    ("import PF.Analytic.FourierPanels.OmegaTailBound_c13_2_2026_10_16",
     "import PF.Analytic.FourierPanels.OmegaTailBound_c27_4_2026_10_19"),
]
for a, b in IMPORTS:
    assert s.count(a) == 1, a
    s = s.replace(a, b)

# ---- 2. opens ---------------------------------------------------------
OPENS = [
    ("open PrincipiaTractalis.FourierPanels_c13_2.Assemble_threehalves",
     "open PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID"),
    ("open PrincipiaTractalis.PilotR1Box_c13_2_r_pointwise_SCAFFOLD_20261016",
     "open PrincipiaTractalis.PilotR1Box_c27_4_r1_16_HYBRID_20261019"),
]
for a, b in OPENS:
    assert s.count(a) == 1, a
    s = s.replace(a, b)

# ---- 3. headline rationals -> hybrid values ---------------------------
RATS = [("2671109 / 200000000", R_LB),
        ("1339441331 / 80000000000", R_UB),
        ("13277 / 500000000", I_LB),
        ("302372667 / 160000000000", I_UB)]
rat_counts = {}
for a, b in RATS:
    rat_counts[a] = s.count(a)
    assert rat_counts[a] > 0, a
    s = s.replace(a, b)

# ---- 4. enclosure theorem names -> hybrid ----------------------------
for a, b in [("reLambda0_threehalves_lb_ub", "reLambda0_threehalves_hybrid_lb_ub"),
             ("imLambda0_threehalves_lb_ub", "imLambda0_threehalves_hybrid_lb_ub")]:
    assert s.count(a) > 0, a
    s = s.replace(a, b)

# ---- 5. module header name -------------------------------------------
s = s.replace("# PF.Analytic.PilotBoxes.R1_c13_2_r1_16_pointwise_CLOSED_2026_10_16",
              "# PF.Analytic.PilotBoxes.R1_c27_4_r1_16_pointwise_UNCONDITIONAL_2026_10_19", 1)
s = s.replace("namespace PilotR1Box_c13_2_r1_16_pointwise_CLOSED_20261016",
              "namespace PilotR1Box_c27_4_r1_16_pointwise_UNCONDITIONAL_20261019")
s = s.replace("end PilotR1Box_c13_2_r1_16_pointwise_CLOSED_20261016",
              "end PilotR1Box_c27_4_r1_16_pointwise_UNCONDITIONAL_20261019")
s = s.replace("PilotR1Box_c13_2_r1_16_pointwise_CLOSED_20261016",
              "PilotR1Box_c27_4_r1_16_pointwise_UNCONDITIONAL_20261019")

# ---- 6. generic c tokens ---------------------------------------------
NB, NA = r"(?<![0-9.])", r"(?![0-9.])"
n_c13 = s.count("c13_2")
s = s.replace("c13_2", "c27_4")
assert "c13_2" not in s

numeric = [
    (NB + r"3\.25" + NA, "3.375", "phase 3.25 -> 3.375"),
    (NB + r"13/4" + NA, "27/8", "c/2 as a fraction 13/4 -> 27/8"),
    (NB + r"13 / 4" + NA, "27 / 8", "c/2 as a fraction 13 / 4 -> 27 / 8"),
    (NB + r"169/4" + NA, "729/16", "c^2 169/4 -> 729/16"),
    (NB + r"169 / 4" + NA, "729 / 16", "c^2 169 / 4 -> 729 / 16"),
    (NB + r"103/16" + NA, "107/16", "box lower edge"),
    (NB + r"105/16" + NA, "109/16", "box upper edge"),
    (NB + r"13/2" + NA, "27/4", "centre 13/2 -> 27/4"),
    (NB + r"13 / 2" + NA, "27 / 4", "centre 13 / 2 -> 27 / 4"),
]
counts = {}
for pat, rep, desc in numeric:
    s, k = re.subn(pat, rep, s)
    counts[desc] = k

# ---- 7. post-assertions ----------------------------------------------
assert "3.25" not in s, "a 3.25 survived"
assert re.search(NB + r"13/2" + NA, s) is None, "a bare 13/2 survived"
assert re.search(NB + r"169/4" + NA, s) is None, "a bare 169/4 survived"
assert re.search(NB + r"13/4" + NA, s) is None, "a bare 13/4 survived (c/2 fraction)"
assert re.search(NB + r"13 / 4" + NA, s) is None, "a bare 13 / 4 survived"
assert re.search(NB + r"103/16" + NA, s) is None
assert re.search(NB + r"105/16" + NA, s) is None
# epsOm must stay 1/10^21
assert "epsOm : ℝ := 1 / 10 ^ 21" in s, "epsOm was corrupted"
# the add-on constants must be untouched
assert "7/10^7" in s or "7 / 10 ^ 7" in s, "residue constant lost"
assert "12/10^8" in s or "12 / 10 ^ 8" in s, "tail constant lost"
# no damage of the form 3.3755 / 729/164 / 1079/16
for bad in ("3.3755", "3.3375", "729/164", "1079/16", "27/44"):
    assert bad not in s, f"numeric corruption: {bad}"
assert s != orig

# ---- 7b. the final theorem: route through the 2-bound composition -----
TAIL_OLD = """theorem pilot_r1_box_c27_4_r1_16_pointwise_UNCONDITIONAL :
    ∀ t ∈ Icc ((107/16 : ℝ)) (109/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  exact pilot_r1_box_c27_4_r1_16_pointwise_closed
    ((4510553327 / 320000000000 : ℝ) - 7/10^7 - 12/10^8 - epsOm)
    ((4802446903 / 320000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm)
    ((161621101 / 320000000000 : ℝ) - 7/10^7 - 12/10^8 - epsOm)
    ((21496359 / 16000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm)
    re_lambda0_at_c27_4_lb
    re_lambda0_at_c27_4_ub
    im_lambda0_at_c27_4_lb
    im_lambda0_at_c27_4_ub
    gate1_arithmetic"""

TAIL_NEW = """theorem pilot_r1_box_c27_4_r1_16_pointwise_UNCONDITIONAL :
    ∀ t ∈ Icc ((107/16 : ℝ)) (109/16),
      0 < (riemannXiEntire (⟨1, t⟩ : ℂ)).re := by
  have hIcc : Icc ((107/16 : ℝ)) (109/16)
      = Icc ((27/4 : ℝ) - 1/16) ((27/4 : ℝ) + 1/16) := by
    congr 1 <;> norm_num
  rw [hIcc]
  exact pilot_r1_box_c27_4_r1_16_closed
    ((4802446903 / 320000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm)
    ((21496359 / 16000000000 : ℝ) + 7/10^7 + 12/10^8 + epsOm)
    re_lambda0_at_c27_4_ub
    im_lambda0_at_c27_4_ub
    gate1_arithmetic"""
assert s.count(TAIL_OLD) == 1, "tail block not found"
s = s.replace(TAIL_OLD, TAIL_NEW)

# stale box decimals carried over from the 13/2 geometry
# (the edge fractions were already rewritten in step 6; only the decimals remain)
s = s.replace("= [6.4375, 6.5625]", "= [6.6875, 6.8125]")
assert "6.4375" not in s, "a 13/2 box decimal survived"

# ---- 8. provenance ---------------------------------------------------
s = s.replace("SPDX-License-Identifier: Apache-2.0",
              "Ported from the c = 13/2 pilot onto the HYBRID enclosure by\n"
              "codex/port_closed_c27_4.py (2026-10-19). All three add-on constants are\n"
              "c-independent (the phase is only ever bounded by |cos|,|sin| <= 1), so the\n"
              "residue 7/10^7, analytic tail 12/10^8 and omega-gap epsOm carry over\n"
              "unchanged; only the panel enclosure differs, and it is the hybrid one.\n"
              "\nSPDX-License-Identifier: Apache-2.0", 1)

io.open(OUT, "w", encoding="utf-8", newline="\n").write(s)
print(f"{OUT}  ({s.count(chr(10))+1} lines)")
print(f"  c13_2 -> c27_4 : {n_c13}")
for d, k in counts.items():
    if k:
        print(f"  {d} : {k}")
print("  headline rationals replaced:")
for a, b in RATS:
    print(f"    {a}  x{rat_counts[a]}  ->  {b}")
