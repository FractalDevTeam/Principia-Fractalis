/-
# r335 — §4 RIGIDITY AUDIT COMPLETED: I7, the eighth and last structural law

★ NEGATIVE / STRUCTURAL RESULT 2026-09-07 ★

`AlphaL5PiScalingObstruction_r332` audited **L5**. `AlphaStructuralLawAudit_r334`
audited **L1, L2, L3, L4, I6, I9**. This module audits **I7**, the eighth law:

    I7 :  α_YM = α_Poincaré + 1

With it, **all eight structural laws of `AlphaSkeletonUniqueness_r128` have been
audited under the directive §4 protocol.** The eight-law system is closed.

## I7 is the most cascading law in the system — and by more than was recorded

The 2026-08-24 provenance audit recorded I7 as "most-cascading under drop
(destroys 4 α's)". That undercounts. `α_YM` appears in **four** other laws
(L2, L4, I9, I6), and the values they pin feed L5 and L3 in turn. Releasing
`α_YM = t` propagates as:

    L2 → α_P    = √t          I9 → α_RH  = 3/t
    L4 → α_QG   = √(tπ)       L5 → α_NS  = 3π/t
    I6 → α_BSD  = 3π/t²       L3 → α_NP  = φ + (3/t − 1)/2

**Seven of the nine α-values move.** Only `α_Poincaré` (the anchor) and
`α_Hodge` (pinned by L1 from the anchor alone) stay put. `wo_I7` below is the
witness at `t = 4`, chosen so every displaced value stays rational-or-clean and
the arithmetic is checkable by inspection:

    α_YM = 4,  α_P = 2,  α_RH = 3/4,  α_NS = 3π/4,
    α_BSD = 3π/16,  α_NP = φ − 1/8,  α_QG = √(4π)

All seven remaining laws hold, positivity holds, and the anchor holds.

## I7 is NOT closed by the trace-range obstruction — and neither is I9

r334 closed L1, L2, L3, L4 and I6 because each forces an irrational, and no
irrational is a ratio of `ℤ[1/3]` elements. I7 forces `α_YM = 2`, and **2 is in
`ℤ[1/3]`** (r123 `memZ13_two`). So the obstruction does not touch it.

That completes a clean pattern across the eight laws:

| forced value | in `ℤ[1/3]`? | ratio of `ℤ[1/3]`? | law | closed by the obstruction? |
|---|---|---|---|---|
| `α_YM = 2` | **yes** | yes | I7 | **no** |
| `α_RH = 3/2` | no (prime 2) | **yes** (3/2) | I9 | **no** |
| φ | no | no | L1 | yes |
| √2 | no | no | L2 | yes |
| φ + ¼ | no | no | L3 | yes |
| √(2π) | no | no | L4 | yes |
| 3π/4 | no | no | I6 | yes |
| 3π/2 | no | no | L5 | yes (r332) |

**Exactly the two laws that force substrate-compatible values survive the
obstruction, and they are exactly the two the corpus calls "corpus invariants"
rather than "structural laws".** That is a real regularity, and it is the
sharpest remaining lead: I7 and I9 are the only two places where a substrate
derivation is not already excluded.

It is a lead, not a result. Being *compatible* with the trace range is necessary,
not sufficient. No theorem links the `+1` of I7 or the `3` of I9 to any substrate
structure, and the provenance audit found none: "the `+1` is not a substrate
quantity", and for I9's `3`, "no theorem currently links `3 = base_of_substrate`
to the product `α_RH · α_YM`".

## Verdict: independent

- **not `redundant`** — `wo_I7` refutes it (seven of nine values move).
- **not `derivable`** — no substrate theorem supplies the `+1`.
- **not `circular`** — the statement does not mention `2`.
- **necessary** in the survey sense, and the most cascading of the eight.

## Status

Axiom-free beyond the mathlib three. No `sorry`. `#print axioms` at the end.

SPDX-License-Identifier: Apache-2.0
-/

import PF.AlphaStructuralLawAudit_r334

namespace PrincipiaTractalis
namespace AlphaStructuralLawAuditI7

open PrincipiaTractalis.AlphaSkeletonUniqueness
open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PrincipiaTractalis.AlphaStructuralLawAudit
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open scoped Real

noncomputable section

theorem phiR_gt_one : 1 < phiR := by
  unfold phiR; nlinarith [sq_sqrt5, sqrt5_pos]

theorem sq_sqrt4pi : Real.sqrt (4*Real.pi) * Real.sqrt (4*Real.pi) = 4 * Real.pi :=
  Real.mul_self_sqrt (by positivity)

theorem sqrt4pi_pos : (0:ℝ) < Real.sqrt (4*Real.pi) := Real.sqrt_pos.mpr (by positivity)

/-- Drop **I7**: `α_YM` is released. Witness at `α_YM = 4`. Seven of the nine
values move; only `α_Poincaré` and `α_Hodge` stay put. -/
abbrev wo_I7 : AlphaSkeleton :=
  ⟨1, 3/4, phiR - 1/8, 3*Real.pi/4, 4, 3*Real.pi/16, phiR, Real.sqrt (4*Real.pi), 2⟩

/-- **★★★ r335.A — I7 IS NECESSARY, AND THE MOST CASCADING OF THE EIGHT ★★★**

    A positive skeleton meeting the anchor and the seven laws other than I7,
    differing from `canonical` in **seven** of the nine values. -/
theorem I7_necessary :
    wo_I7.aPoincare = 1 ∧ IsPositive wo_I7 ∧
    -- the seven remaining laws
    wo_I7.aHodge * wo_I7.aHodge = wo_I7.aPoincare * wo_I7.aHodge + wo_I7.aPoincare ∧
    wo_I7.aP * wo_I7.aP = wo_I7.aYM ∧
    wo_I7.aRH * wo_I7.aYM = 3 ∧
    wo_I7.aPoincare + 2 * (wo_I7.aNP - wo_I7.aHodge) = wo_I7.aRH ∧
    wo_I7.aQG * wo_I7.aQG = wo_I7.aYM * Real.pi ∧
    wo_I7.aNS = wo_I7.aRH * Real.pi ∧
    wo_I7.aNS = wo_I7.aYM * wo_I7.aBSD ∧
    -- seven of nine values differ from canonical
    wo_I7.aYM ≠ 2 ∧ wo_I7.aRH ≠ 3/2 ∧ wo_I7.aNS ≠ 3*Real.pi/2 ∧
    wo_I7.aBSD ≠ 3*Real.pi/4 ∧ wo_I7.aNP ≠ phiR + 1/4 ∧
    wo_I7.aP ≠ Real.sqrt 2 ∧ wo_I7.aQG ≠ Real.sqrt (2*Real.pi) :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by show (0:ℝ) < phiR - 1/8; have := phiR_gt_one; linarith,
    by positivity, by norm_num, by positivity, phiR_pos, sqrt4pi_pos, by norm_num⟩,
   phiR_minpoly, by norm_num, by norm_num, by ring, sq_sqrt4pi, by ring, by ring,
   by norm_num,
   by norm_num,
   by show 3*Real.pi/4 ≠ 3*Real.pi/2; intro h; nlinarith [Real.pi_gt_three],
   by show 3*Real.pi/16 ≠ 3*Real.pi/4; intro h; nlinarith [Real.pi_gt_three],
   by show phiR - 1/8 ≠ phiR + 1/4; intro h; linarith,
   by show (2:ℝ) ≠ Real.sqrt 2; intro h; have h2 := sq_sqrt2; rw [← h] at h2; norm_num at h2,
   by show Real.sqrt (4*Real.pi) ≠ Real.sqrt (2*Real.pi)
      intro h
      have h4 := sq_sqrt4pi
      rw [h] at h4
      have h2 : Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi) = 2*Real.pi :=
        Real.mul_self_sqrt (by positivity)
      rw [h2] at h4
      nlinarith [Real.pi_gt_three]⟩

/-! ## §2 — I7 and I9 survive the trace-range obstruction -/

/-- **r335.B — I7's forced value lies IN the substrate trace range.**

    `α_YM = 2 ∈ ℤ[1/3]` (r123). So the obstruction that closes L1, L2, L3, L4,
    I6 (r334) and L5 (r332) does **not** close I7. -/
theorem i7_value_in_trace_range : MemZ13 α_YM := by
  show MemZ13 (2:ℝ)
  exact memZ13_two

/-- **★ r335.C — exactly two of the eight laws survive the obstruction.**

    I7 forces a value *in* `ℤ[1/3]`; I9 forces one *reachable as a ratio* of
    `ℤ[1/3]` elements (r334.I). The other six force irrationals and are closed.

    Compatibility is necessary, not sufficient: no theorem links I7's `+1` or
    I9's `3` to any substrate structure. This records where a derivation is
    still *possible*, not where one exists. -/
theorem exactly_two_laws_survive_the_obstruction :
    -- I7's value is in the trace range
    MemZ13 α_YM ∧
    -- I9's value is a ratio of trace-range elements
    (∃ a b : ℝ, MemZ13 a ∧ MemZ13 b ∧ a ≠ 0 ∧ b / a = α_RH) ∧
    -- the other six force irrationals, so no ratio reaches them
    (∀ a b : ℝ, MemZ13 a → MemZ13 b →
        b / a ≠ α_Hodge ∧ b / a ≠ α_P ∧ b / a ≠ α_NP ∧
        b / a ≠ α_QG ∧ b / a ≠ α_BSD ∧ b / a ≠ α_NS) :=
  ⟨i7_value_in_trace_range,
   i9_value_is_ktheoretic_ratio,
   fun a b ha hb =>
     ⟨no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_Hodge,
      no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_P,
      no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_NP,
      no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_QG,
      no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_BSD,
      no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_NS⟩⟩

/-! ## §3 — Axiom check -/

#print axioms I7_necessary
#print axioms i7_value_in_trace_range
#print axioms exactly_two_laws_survive_the_obstruction

end

end AlphaStructuralLawAuditI7
end PrincipiaTractalis
