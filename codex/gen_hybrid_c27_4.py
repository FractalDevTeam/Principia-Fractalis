#!/usr/bin/env python3
"""
Generator for the c = 27/4 HYBRID three-halves assemble.

Segments 1-2 come from the MIDPOINT pack, segments 3-6 from the RANGE-BRICK
pack -- the per-segment-best scheme measured in codex/INTEG_ROADMAP_*.

The one piece of real content is the convention bridge: the midpoint files
state their panel bounds about

    f_plus u = sum_{n<3} fourier_plus_term (27/4) n u

while the range-brick files and every downstream consumer use

    nodeR_fourier_plus_at_c27_4_N3 u.

Since `fourier_plus_term` carries an explicit factor 2,
`f_plus = 2 * nodeR_..._N3`, so the midpoint bounds must be HALVED before they
can be summed alongside range-brick bounds. (Note: the midpoint files'
docstring says "Equal to nodeR_..._N3 u / 2", which is the reciprocal of what
their own inline `h_eq` proofs establish and of what the definitions give.
The factor used here is the one the proofs use.)
"""
import re
import io
from fractions import Fraction as F

D = "c27/"
OUT = "Assemble_c27_4_threehalves_HYBRID_2026_10_19.lean"
ADDON = F(7, 10**7) + F(12, 10**8) + F(1, 10**21)   # residue + tail + epsOm
C = F(27, 4)


def rd(n):
    return io.open(D + n, encoding="utf-8").read()


def dec(fr):
    """Exact decimal string for a terminating fraction."""
    fr = F(fr)
    num, den = fr.numerator, fr.denominator
    d = den
    e2 = e5 = 0
    while d % 2 == 0:
        d //= 2
        e2 += 1
    while d % 5 == 0:
        d //= 5
        e5 += 1
    assert d == 1, f"{fr} is not terminating"
    k = max(e2, e5)
    scaled = num * 10**k // den
    s = str(abs(scaled)).rjust(k + 1, "0")
    out = (s[:-k] + "." + s[-k:]) if k else s
    return ("-" if fr < 0 else "") + out


# ---------------------------------------------------------------- parse
mid = {}
for seg in (1, 2):
    txt = rd(f"Seg0{seg}Midpoint_c27_4_2026_10_17.lean")
    for m in re.finditer(
            r"theorem m0(\d)p(\d)_(plus|minus)_integral_bound\s*:\s*"
            r"\((-?[0-9.]+) : ℝ\)\s*≤\s*\(∫ u in \((-?[0-9.]+) : ℝ\)\.\."
            r"\((-?[0-9.]+) : ℝ\),[^)]*\)\s*∧[^≤]*≤\s*\((-?[0-9.]+) : ℝ\)",
            txt, re.DOTALL):
        s, p, side, lo, a, b, hi = m.groups()
        mid[(int(s), int(p), side)] = dict(lo=lo, hi=hi, a=a, b=b)

rng = {}
for seg in (3, 4, 5, 6):
    txt = rd(f"Seg0{seg}Range_c27_4_2026_10_16.lean")
    for m in re.finditer(
            r"theorem s0(\d)p(\d)_(plus|minus)_integral_bound\s*:(.*?):= by",
            txt, re.DOTALL):
        s, p, side, body = m.groups()
        vals = re.findall(r"\(0\.03125 : ℝ\) \* \((-?[0-9.]+) : ℝ\)", body)
        ivl = re.findall(r"\((-?[0-9.]+) : ℝ\)\.\.\((-?[0-9.]+) : ℝ\)", body)
        assert len(vals) == 2
        rng[(int(s), int(p), side)] = dict(lo=vals[0], hi=vals[1],
                                           a=ivl[0][0], b=ivl[0][1])

assert len(mid) == 32, len(mid)
assert len(rng) == 64, len(rng)

H = F("0.03125")

# ---------------------------------------------------------------- panel list
# (kind, seg, p, a, b) in increasing u order
panels = []
for s in (1, 2):
    for p in range(1, 9):
        e = mid[(s, p, "plus")]
        panels.append(("mid", s, p, F(e["a"]), F(e["b"])))
for s in (3, 4, 5, 6):
    for p in range(8):
        e = rng[(s, p, "plus")]
        panels.append(("rng", s, p, F(e["a"]), F(e["b"])))

assert len(panels) == 48
assert panels[0][3] == 0 and panels[-1][4] == F(3, 2)
for i in range(47):
    assert panels[i][4] == panels[i + 1][3], f"gap at {i}"


def bound(side, kind, s, p, which):
    """Exact Fraction bound on the integral of nodeR over the panel."""
    if kind == "mid":
        return F(mid[(s, p, side)][which]) / 2
    return H * F(rng[(s, p, side)][which])


def total(side, which):
    return sum(bound(side, k, s, p, which) for k, s, p, _, _ in panels)


R_lo, R_hi = total("plus", "lo"), total("plus", "hi")
I_lo, I_hi = total("minus", "lo"), total("minus", "hi")
gate = C * C * (R_hi + ADDON) + C * (I_hi + ADDON)
margin = F(3, 4) - gate

print(f"  plus  [0,3/2] : [{float(R_lo):.10f}, {float(R_hi):.10f}]")
print(f"  minus [0,3/2] : [{float(I_lo):.10f}, {float(I_hi):.10f}]")
print(f"  GATE-1 lhs = {float(gate):.8f}  margin = {float(margin):+.8f}")
assert margin > 0


def frac(fr):
    fr = F(fr)
    return f"{fr.numerator}/{fr.denominator}" if fr.denominator != 1 else str(fr.numerator)


# ---------------------------------------------------------------- emit
L = []
w = L.append

w(f"""/-
# PF.Analytic.FourierPanels.Assemble_c27_4_threehalves_HYBRID_2026_10_19

**The c = 27/4 HYBRID three-halves assemble: midpoint on segments 1-2,
range-brick on segments 3-6.**

Neither scheme closes Gate-1 at `c = 27/4` on its own. Measured on the landed
panel files, against the real Gate-1 inequality
`(729/16)·R_ub + (27/4)·I_ub ≤ 3/4` with add-ons `A = 7/10^7 + 12/10^8 + epsOm`:

| scheme | `(729/16)(R_ub+A) + (27/4)(I_ub+A)` | vs `3/4` |
|---|---|---|
| all range-brick | `0.75566065` | **FAIL by 0.00566** |
| **hybrid (this file)** | **`{float(gate):.8f}`** | **PASS by {float(margin):.5f}** |

The crossover is structural. The midpoint error is `M·h³/24` per panel with `M`
*growing* along `u` (24, 24, 30, 30, 72, 72 over the six segments, since the
derivative bound is taken over the whole segment), while the range-brick spread
*shrinks* as the integrand decays. Midpoint wins segments 1-2 and loses
segment 6 by 863×.

## The convention bridge -- the one piece of real content

The midpoint pack states its panel bounds about

  `f_plus u = ∑ n ∈ range 3, fourier_plus_term (27/4) n u`

while the range-brick pack and every downstream consumer use
`nodeR_fourier_plus_at_c27_4_N3`. `fourier_plus_term` carries an **explicit
factor 2**, so

  `∑ n ∈ range 3, fourier_plus_term (27/4) n u = 2 · nodeR_fourier_plus_at_c27_4_N3 u`

(`fourier_plus_sum_eq` below). Every midpoint panel bound is therefore **halved**
before it joins the range-brick bounds. The two packs are *not*
interchangeable as stated; this is what makes the hybrid a build rather than a
concatenation.

Note for the record: `Seg0{{1,2}}Midpoint_c27_4`'s docstring claims `f_plus` is
*"equal to `nodeR_fourier_plus_at_c27_4_N3 u / 2`"*. That is the reciprocal of
what its own inline `h_eq` proofs establish and of what the definitions give.
The factor proved here (`· 2`) is the one those proofs use, so the docstring is
the defect, not the proofs.

No sorry, native_decide, axiom, Prop := True. autoImplicit off. Additive.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-19.
GENERATED by codex/gen_hybrid_c27_4.py -- edit the generator, not this file.
-/

import PF.Analytic.FourierPanels.Seg01Midpoint_c27_4_2026_10_17
import PF.Analytic.FourierPanels.Seg02Midpoint_c27_4_2026_10_17
import PF.Analytic.FourierPanels.Seg03Range_c27_4_2026_10_16
import PF.Analytic.FourierPanels.Seg04Range_c27_4_2026_10_16
import PF.Analytic.FourierPanels.Seg05Range_c27_4_2026_10_16
import PF.Analytic.FourierPanels.Seg06Range_c27_4_2026_10_16

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000

namespace PrincipiaTractalis
namespace FourierPanels_c27_4
namespace Assemble_threehalves_HYBRID

open MeasureTheory
open PrincipiaTractalis.FourierPanels_c27_4
open PrincipiaTractalis.FourierTermC2
open scoped Real

noncomputable section

/-! ## §1 — Local notation -/

private noncomputable abbrev fP : ℝ → ℝ := nodeR_fourier_plus_at_c27_4_N3
private noncomputable abbrev fM : ℝ → ℝ := nodeR_fourier_minus_at_c27_4_N3

private theorem iiP (a b : ℝ) : IntervalIntegrable fP MeasureTheory.volume a b :=
  Seg03Range.nodeR_fourier_plus_at_c27_4_N3_intervalIntegrable a b

private theorem iiM (a b : ℝ) : IntervalIntegrable fM MeasureTheory.volume a b :=
  Seg03Range.nodeR_fourier_minus_at_c27_4_N3_intervalIntegrable a b

/-! ## §2 — The convention bridge: the midpoint pack's integrand is `2 · fP` -/

/-- `∑ n ∈ range 3, fourier_plus_term (27/4) n u = 2 · nodeR_fourier_plus_at_c27_4_N3 u`.
`fourier_plus_term` carries an explicit factor `2`; `nodeR_..._N3` does not. -/
theorem fourier_plus_sum_eq (u : ℝ) :
    (∑ n ∈ Finset.range 3, fourier_plus_term (27 / 4) n u)
      = 2 * nodeR_fourier_plus_at_c27_4_N3 u := by
  unfold fourier_plus_term nodeR_fourier_plus_at_c27_4_N3 omega_N3_at_exp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
             Nat.cast_zero, Nat.cast_one, zero_add]
  ring_nf

/-- Minus-side counterpart. -/
theorem fourier_minus_sum_eq (u : ℝ) :
    (∑ n ∈ Finset.range 3, fourier_minus_term (27 / 4) n u)
      = 2 * nodeR_fourier_minus_at_c27_4_N3 u := by
  unfold fourier_minus_term nodeR_fourier_minus_at_c27_4_N3 omega_N3_at_exp
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat,
             Nat.cast_zero, Nat.cast_one, zero_add]
  ring_nf

/-- Integrated form of the bridge, plus side. -/
theorem mid_to_node_plus (a b : ℝ) :
    (∫ u in a..b, (∑ n ∈ Finset.range 3, fourier_plus_term (27 / 4) n u))
      = 2 * ∫ u in a..b, fP u := by
  rw [intervalIntegral.integral_congr
        (g := fun u => 2 * nodeR_fourier_plus_at_c27_4_N3 u)
        (fun u _ => fourier_plus_sum_eq u)]
  exact intervalIntegral.integral_const_mul 2 _

/-- Integrated form of the bridge, minus side. -/
theorem mid_to_node_minus (a b : ℝ) :
    (∫ u in a..b, (∑ n ∈ Finset.range 3, fourier_minus_term (27 / 4) n u))
      = 2 * ∫ u in a..b, fM u := by
  rw [intervalIntegral.integral_congr
        (g := fun u => 2 * nodeR_fourier_minus_at_c27_4_N3 u)
        (fun u _ => fourier_minus_sum_eq u)]
  exact intervalIntegral.integral_const_mul 2 _

/-! ## §3 — Midpoint panels, re-expressed on `fP` / `fM` (bounds halved) -/
""")

TERM = {"plus": "fourier_plus_term", "minus": "fourier_minus_term"}
BRIDGE = {"plus": "mid_to_node_plus", "minus": "mid_to_node_minus"}
FN = {"plus": "fP", "minus": "fM"}

for side in ("plus", "minus"):
    for s in (1, 2):
        for p in range(1, 9):
            e = mid[(s, p, side)]
            a, b = e["a"], e["b"]
            lo2, hi2 = dec(F(e["lo"]) / 2), dec(F(e["hi"]) / 2)
            name = f"hm{s}{p}_{side}"
            integ = (f"(∫ u in ({a} : ℝ)..({b} : ℝ),\n"
                     f"             (∑ n ∈ Finset.range 3, "
                     f"{TERM[side]} (27 / 4) n u))")
            w(f"""private lemma {name} :
    ({lo2} : ℝ) ≤ (∫ u in ({a} : ℝ)..({b} : ℝ), {FN[side]} u)
  ∧ (∫ u in ({a} : ℝ)..({b} : ℝ), {FN[side]} u) ≤ ({hi2} : ℝ) := by
  have b : ({e["lo"]} : ℝ) ≤ {integ}
      ∧ {integ} ≤ ({e["hi"]} : ℝ) :=
    Seg0{s}Midpoint.m0{s}p{p}_{side}_integral_bound
  rw [{BRIDGE[side]}] at b
  exact ⟨by linarith [b.1], by linarith [b.2]⟩

""")

# ---------------------------------------------------------------- headline
for side, fn, ii, lo, hi, nm in (
        ("plus", "fP", "iiP", R_lo, R_hi, "reLambda0_threehalves_hybrid_lb_ub"),
        ("minus", "fM", "iiM", I_lo, I_hi, "imLambda0_threehalves_hybrid_lb_ub")):
    w(f"""/-! ## §4 — Headline {side.upper()} hybrid enclosure on `[0, 3/2]` -/

/-- **Hybrid enclosure of `∫₀^{{3/2}} {fn}`** — midpoint on segments 1-2,
range-brick on segments 3-6. -/
theorem {nm} :
    ({frac(lo)} : ℝ) ≤ (∫ u in (0 : ℝ)..(3 / 2 : ℝ), {fn} u)
  ∧ (∫ u in (0 : ℝ)..(3 / 2 : ℝ), {fn} u) ≤ ({frac(hi)} : ℝ) := by
""")
    for i, (kind, s, p, a, b) in enumerate(panels):
        if kind == "mid":
            w(f"  have b{i:02d} := hm{s}{p}_{side}\n")
        else:
            w(f"  have b{i:02d} := Seg0{s}Range.s0{s}p{p}_{side}_integral_bound\n")
    for k in range(1, 48):
        x = panels[k][3]
        y = panels[k][4]
        w(f"""  have h{k:02d} : (∫ u in (0 : ℝ)..({dec(x)} : ℝ), {fn} u)
             + (∫ u in ({dec(x)} : ℝ)..({dec(y)} : ℝ), {fn} u)
           = ∫ u in (0 : ℝ)..({dec(y)} : ℝ), {fn} u :=
    intervalIntegral.integral_add_adjacent_intervals ({ii} _ _) ({ii} _ _)
""")
    lows = ", ".join(f"b{i:02d}.1" for i in range(48))
    his = ", ".join(f"b{i:02d}.2" for i in range(48))
    hs = ", ".join(f"h{k:02d}" for k in range(1, 48))
    w(f"""  refine ⟨?_, ?_⟩
  · linarith [{lows}, {hs}]
  · linarith [{his}, {hs}]

""")

# ---------------------------------------------------------------- gate 1
w(f"""/-! ## §5 — Gate-1 arithmetic at `c = 27/4` -/

/-- **Gate-1 closes at `c = 27/4` under the hybrid scheme.**

`(729/16)·R_ub + (27/4)·I_ub ≤ 3/4`, where `R_ub` and `I_ub` are the hybrid
upper bounds plus the three add-ons (residue `7/10^7`, analytic tail `12/10^8`,
ω-gap `epsOm`). The add-on values are the ones the `c = 13/2` pilot carries;
`epsOm` is passed as a parameter because the `c = 27/4` add-on modules are not
yet built — see the OPEN note in the module docstring.

Margin: `{float(margin):+.8f}`. -/
theorem gate1_arithmetic_c27_4_hybrid {{epsOm : ℝ}} (hEps : epsOm ≤ 1 / 10 ^ 21) :
    (729 / 16 : ℝ) * (({frac(R_hi)} : ℝ) + 7 / 10 ^ 7 + 12 / 10 ^ 8 + epsOm)
      + (27 / 4 : ℝ) * (({frac(I_hi)} : ℝ) + 7 / 10 ^ 7 + 12 / 10 ^ 8 + epsOm)
      ≤ 3 / 4 := by
  nlinarith [hEps]

/-- The margin, stated explicitly: Gate-1 has `{float(margin):.5f}` to spare at
`epsOm = 0`, which is **{float(margin / F("0.0327")):.2f}× the `+0.0327` the roadmap
projected** (the roadmap's figure was computed in an enclosure-width metric;
this is the inequality the pilot scaffold actually requires). -/
theorem gate1_margin_c27_4_hybrid :
    (729 / 16 : ℝ) * (({frac(R_hi)} : ℝ) + 7 / 10 ^ 7 + 12 / 10 ^ 8)
      + (27 / 4 : ℝ) * (({frac(I_hi)} : ℝ) + 7 / 10 ^ 7 + 12 / 10 ^ 8)
      ≤ 3 / 4 - {frac(F(margin).limit_denominator(10**6))} := by
  norm_num

end

end Assemble_threehalves_HYBRID
end FourierPanels_c27_4
end PrincipiaTractalis

/-! ## §Axiom check -/

#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.fourier_plus_sum_eq
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.fourier_minus_sum_eq
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.mid_to_node_plus
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.mid_to_node_minus
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.reLambda0_threehalves_hybrid_lb_ub
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.imLambda0_threehalves_hybrid_lb_ub
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.gate1_arithmetic_c27_4_hybrid
#print axioms PrincipiaTractalis.FourierPanels_c27_4.Assemble_threehalves_HYBRID.gate1_margin_c27_4_hybrid
""")

io.open(OUT, "w", encoding="utf-8", newline="\n").write("".join(L))
n = "".join(L).count("\n") + 1
print(f"  emitted {OUT}: {n} lines")
