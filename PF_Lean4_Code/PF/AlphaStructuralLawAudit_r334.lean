/-
# r334 — §4 RIGIDITY AUDIT: the six remaining structural laws, kernel verdicts

★ NEGATIVE / STRUCTURAL RESULT 2026-09-07 ★

Directive §4 (`codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md`) makes the
α-skeleton rigidity audit the first mathematical gate, and specifies the
per-law protocol: unfold fully; earliest independent source; derivable from
foundations?; imports target?; remove and survey surviving family; countermodel
search; verdict from {necessary, redundant, derivable, independent, circular}.

`AlphaL5PiScalingObstruction_r332` ran that protocol for **L5**. This module runs
it for the remaining six under audit: **L1, L2, L3, L4, I6, I9**. Same method:
reduce each law to the smallest kernel-decidable statement and let Lean issue the
verdict.

(I7, `α_YM = α_Poincaré + 1`, is the eighth law and is NOT in this
authorization. The eight-law system is not fully audited until it is done.)

## §1 — remove-and-survey: all six are NECESSARY, none redundant

For each law X, `wo_X` below is a positive skeleton satisfying the anchor and the
seven laws other than X, and differing from `canonical`. Since `canonical`
satisfies all eight, each witness proves the family strictly grows when X is
dropped. **No law of the six is redundant** — each is the sole (or the binding)
constraint on at least one α.

This is the eight-law analogue of r124's Gröbner result, and it agrees with it:
r124 found I2 and I8 redundant among the *eleven invariants*; among the *eight
structural laws* there is no redundancy left to find.

## §2 — the values the laws force, and where they can come from

Necessity is not provenance. A law can do work and still be an assumption. §3
asks the provenance question the L5 template asks: **is the value a law forces
reachable from the substrate's classifying invariant?**

r123 established the substrate's unique trace carries `K₀(T∞)` onto
`ℤ[1/3] ⊂ ℝ`, and that seven of the nine α-values lie outside it. r332 extended
this from values to *ratios* for π. This module completes the extension: a ratio
of trace-range quantities is rational, so **no irrational value is ratio-reachable
either** (`no_ktheoretic_ratio_is_irrational`).

Consequence, uniform across five of the six laws: the value each forces is
neither in `ℤ[1/3]` nor a ratio of `ℤ[1/3]` elements. **L1, L2, L3, L4 and I6
cannot be substrate consequences.**

## §3 — I9 is the exception, and it is a real one

`I9 : α_RH · α_YM = 3` forces `α_RH = 3/2` at `α_YM = 2`. `3/2 ∉ ℤ[1/3]` (r123,
by the prime 2) — but `3/2` **is** a ratio of trace-range elements: `3` and `2`
are both in `ℤ[1/3]`, and `3/2 = 3/2`. So I9 alone among the six survives the
ratio obstruction (`i9_value_is_ktheoretic_ratio`).

This does **not** make I9 derived. It means the obstruction that closes the other
five does not close I9, and I9's provenance stays open on a narrower question:
whether the substrate forces the specific pair. Recording an exception rather
than a uniform sweep is the point of running the protocol per law.

## Verdicts

| law | remove-and-survey | value forced at anchor | substrate-reachable? | verdict |
|---|---|---|---|---|
| L1 | necessary (frees α_Hodge) | φ | no — irrational | **independent** |
| L2 | necessary (frees α_P) | √2 | no — irrational | **independent** |
| L3 | necessary (frees α_NP) | φ + 1/4 | no — irrational | **independent** |
| L4 | necessary (frees α_QG) | √(2π) | no — irrational | **independent** |
| I6 | necessary (frees α_BSD) | 3π/4 | no — irrational | **independent** |
| I9 | necessary (frees α_RH, and α_NS, α_BSD, α_NP follow) | 3/2 | **YES as a ratio** | **independent** |

**None of the six is `circular`** in the syntactic sense — no law's statement
mentions the value it forces. That is a real distinction from the r301 bundle
(r333), whose premise *is* its conclusion. It is also a distinction from L5,
whose π is now proven unreachable outright (r332).

**None of the six is `derivable`** from the framework's foundations: five are
blocked by the trace-range obstruction, and the sixth (I9) has no substrate
theorem linking `3` to anything.

So all six are **independent**: genuine additional assumptions, each carrying
about one numeral's worth of information, none of them consequences of the
substrate. The "derived constants" claim fails for the α-skeleton not because the
laws are circular but because **they are assumptions**.

## Earliest independent source — the H₃ lead, and why it does not close

`H3CoxeterOrigin.lean` supplies φ genuinely (`sin(π/10) = (√5−1)/4 = 1/(2φ)`,
mathlib-verified) and offers `1/4 = 1/(H₃ exponent gap)` for L3 and
`3/2 = 15/10` for I9. But that file imports **only mathlib**, and states in its
own "What is NOT claimed" section:

  > This file does NOT prove that the framework's H_α operator inherits the H₃
  > Coxeter structure (that would be the operator-theoretic origin of the
  > universal closed form, and is OPEN).

So H₃ is an independent source in *mathematics*, not in *this framework*. φ
existing is not φ being forced. The lead is real and remains open; it is not a
derivation today.

## Status

Axiom-free beyond the mathlib three. No `sorry`. `#print axioms` at the end.

SPDX-License-Identifier: Apache-2.0
-/

import PF.AlphaSkeletonUniqueness_r128
import PF.AlphaL5PiScalingObstruction_r332

namespace PrincipiaTractalis
namespace AlphaStructuralLawAudit

open PrincipiaTractalis.AlphaSkeletonUniqueness
open PrincipiaTractalis.AlphaFromSubstrateKTheory
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open scoped Real

noncomputable section

/-! ## §1 — Remove-and-survey witnesses

Each `wo_X` satisfies the anchor and the seven laws other than `X`, is positive,
and differs from `canonical`. Written out field by field (rather than as a
structure update) so every projection reduces definitionally. -/

/-- φ, spelled as `canonical` spells it. -/
abbrev phiR : ℝ := (1 + Real.sqrt 5) / 2

theorem sqrt5_pos : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
theorem phiR_pos : 0 < phiR := by unfold phiR; have := sqrt5_pos; linarith
theorem sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt2pi_pos : (0:ℝ) < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.mpr (by positivity)
theorem sq_sqrt2pi : Real.sqrt (2*Real.pi) * Real.sqrt (2*Real.pi) = 2 * Real.pi :=
  Real.mul_self_sqrt (by positivity)
theorem phiR_minpoly : phiR * phiR = 1 * phiR + 1 := by
  unfold phiR; nlinarith [sq_sqrt5]

/-- Drop **L1**: `α_Hodge` released (`α_NP` follows, to keep L3). -/
abbrev wo_L1 : AlphaSkeleton :=
  ⟨1, 3/2, 5/4, 3*Real.pi/2, 2, 3*Real.pi/4, 1, Real.sqrt (2*Real.pi), Real.sqrt 2⟩

/-- Drop **L2**: `α_P` released; no other law mentions it. -/
abbrev wo_L2 : AlphaSkeleton :=
  ⟨1, 3/2, phiR + 1/4, 3*Real.pi/2, 2, 3*Real.pi/4, phiR, Real.sqrt (2*Real.pi), 1⟩

/-- Drop **L3**: `α_NP` released; no other law mentions it. -/
abbrev wo_L3 : AlphaSkeleton :=
  ⟨1, 3/2, 1, 3*Real.pi/2, 2, 3*Real.pi/4, phiR, Real.sqrt (2*Real.pi), Real.sqrt 2⟩

/-- Drop **L4**: `α_QG` released; no other law mentions it. -/
abbrev wo_L4 : AlphaSkeleton :=
  ⟨1, 3/2, phiR + 1/4, 3*Real.pi/2, 2, 3*Real.pi/4, phiR, 1, Real.sqrt 2⟩

/-- Drop **I6**: `α_BSD` released. r124's free parameter, inside the eight-law
system. -/
abbrev wo_I6 : AlphaSkeleton :=
  ⟨1, 3/2, phiR + 1/4, 3*Real.pi/2, 2, 1, phiR, Real.sqrt (2*Real.pi), Real.sqrt 2⟩

/-- Drop **I9**: `α_RH` released, and `α_NS`, `α_BSD`, `α_NP` follow through
L5, I6 and L3. Four values move together. -/
abbrev wo_I9 : AlphaSkeleton :=
  ⟨1, 1, phiR, Real.pi, 2, Real.pi/2, phiR, Real.sqrt (2*Real.pi), Real.sqrt 2⟩

/-- **r334.A — L1 is NECESSARY.** A positive skeleton meeting the anchor and the
other seven laws, with `α_Hodge = 1 ≠ φ`. -/
theorem L1_necessary :
    wo_L1.aPoincare = 1 ∧ IsPositive wo_L1 ∧
    wo_L1.aYM = wo_L1.aPoincare + 1 ∧
    wo_L1.aP * wo_L1.aP = wo_L1.aYM ∧
    wo_L1.aRH * wo_L1.aYM = 3 ∧
    wo_L1.aPoincare + 2 * (wo_L1.aNP - wo_L1.aHodge) = wo_L1.aRH ∧
    wo_L1.aQG * wo_L1.aQG = wo_L1.aYM * Real.pi ∧
    wo_L1.aNS = wo_L1.aRH * Real.pi ∧
    wo_L1.aNS = wo_L1.aYM * wo_L1.aBSD ∧
    wo_L1.aHodge ≠ phiR :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by norm_num, by positivity, by norm_num,
    by positivity, by norm_num, sqrt2pi_pos, sqrt2_pos⟩,
   by norm_num, sq_sqrt2, by norm_num, by norm_num, sq_sqrt2pi, by ring, by ring,
   by show (1:ℝ) ≠ phiR; unfold phiR; intro h; nlinarith [sq_sqrt5]⟩

/-- **r334.B — L2 is NECESSARY.** `α_P` released. -/
theorem L2_necessary :
    wo_L2.aPoincare = 1 ∧ IsPositive wo_L2 ∧
    wo_L2.aHodge * wo_L2.aHodge = wo_L2.aPoincare * wo_L2.aHodge + wo_L2.aPoincare ∧
    wo_L2.aYM = wo_L2.aPoincare + 1 ∧
    wo_L2.aRH * wo_L2.aYM = 3 ∧
    wo_L2.aPoincare + 2 * (wo_L2.aNP - wo_L2.aHodge) = wo_L2.aRH ∧
    wo_L2.aQG * wo_L2.aQG = wo_L2.aYM * Real.pi ∧
    wo_L2.aNS = wo_L2.aRH * Real.pi ∧
    wo_L2.aNS = wo_L2.aYM * wo_L2.aBSD ∧
    wo_L2.aP ≠ Real.sqrt 2 :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by show (0:ℝ) < phiR + 1/4; have := phiR_pos; linarith, by positivity,
    by norm_num, by positivity, phiR_pos, sqrt2pi_pos, by norm_num⟩,
   phiR_minpoly, by norm_num, by norm_num, by ring, sq_sqrt2pi, by ring, by ring,
   by intro h; have h2 := sq_sqrt2; rw [← h] at h2; norm_num at h2⟩

/-- **r334.C — L3 is NECESSARY.** `α_NP` released — r124's free offset, inside
the eight-law system. -/
theorem L3_necessary :
    wo_L3.aPoincare = 1 ∧ IsPositive wo_L3 ∧
    wo_L3.aHodge * wo_L3.aHodge = wo_L3.aPoincare * wo_L3.aHodge + wo_L3.aPoincare ∧
    wo_L3.aYM = wo_L3.aPoincare + 1 ∧
    wo_L3.aP * wo_L3.aP = wo_L3.aYM ∧
    wo_L3.aRH * wo_L3.aYM = 3 ∧
    wo_L3.aQG * wo_L3.aQG = wo_L3.aYM * Real.pi ∧
    wo_L3.aNS = wo_L3.aRH * Real.pi ∧
    wo_L3.aNS = wo_L3.aYM * wo_L3.aBSD ∧
    wo_L3.aNP ≠ phiR + 1/4 :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by norm_num, by positivity, by norm_num,
    by positivity, phiR_pos, sqrt2pi_pos, sqrt2_pos⟩,
   phiR_minpoly, by norm_num, sq_sqrt2, by norm_num, sq_sqrt2pi, by ring, by ring,
   by show (1:ℝ) ≠ phiR + 1/4; unfold phiR; intro h; nlinarith [sq_sqrt5]⟩

/-- **r334.D — L4 is NECESSARY.** `α_QG` released. -/
theorem L4_necessary :
    wo_L4.aPoincare = 1 ∧ IsPositive wo_L4 ∧
    wo_L4.aHodge * wo_L4.aHodge = wo_L4.aPoincare * wo_L4.aHodge + wo_L4.aPoincare ∧
    wo_L4.aYM = wo_L4.aPoincare + 1 ∧
    wo_L4.aP * wo_L4.aP = wo_L4.aYM ∧
    wo_L4.aRH * wo_L4.aYM = 3 ∧
    wo_L4.aPoincare + 2 * (wo_L4.aNP - wo_L4.aHodge) = wo_L4.aRH ∧
    wo_L4.aNS = wo_L4.aRH * Real.pi ∧
    wo_L4.aNS = wo_L4.aYM * wo_L4.aBSD ∧
    wo_L4.aQG ≠ Real.sqrt (2*Real.pi) :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by show (0:ℝ) < phiR + 1/4; have := phiR_pos; linarith, by positivity,
    by norm_num, by positivity, phiR_pos, by norm_num, sqrt2_pos⟩,
   phiR_minpoly, by norm_num, sq_sqrt2, by norm_num, by ring, by ring, by ring,
   by intro h; have hq := sq_sqrt2pi; rw [← h] at hq; nlinarith [Real.pi_gt_three]⟩

/-- **r334.E — I6 is NECESSARY.** `α_BSD` released. Exactly r124's
one-parameter family, exhibited in the eight-law system. -/
theorem I6_necessary :
    wo_I6.aPoincare = 1 ∧ IsPositive wo_I6 ∧
    wo_I6.aHodge * wo_I6.aHodge = wo_I6.aPoincare * wo_I6.aHodge + wo_I6.aPoincare ∧
    wo_I6.aYM = wo_I6.aPoincare + 1 ∧
    wo_I6.aP * wo_I6.aP = wo_I6.aYM ∧
    wo_I6.aRH * wo_I6.aYM = 3 ∧
    wo_I6.aPoincare + 2 * (wo_I6.aNP - wo_I6.aHodge) = wo_I6.aRH ∧
    wo_I6.aQG * wo_I6.aQG = wo_I6.aYM * Real.pi ∧
    wo_I6.aNS = wo_I6.aRH * Real.pi ∧
    wo_I6.aBSD ≠ 3*Real.pi/4 :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, by show (0:ℝ) < phiR + 1/4; have := phiR_pos; linarith, by positivity,
    by norm_num, by norm_num, phiR_pos, sqrt2pi_pos, sqrt2_pos⟩,
   phiR_minpoly, by norm_num, sq_sqrt2, by norm_num, by ring, sq_sqrt2pi, by ring,
   by intro h; nlinarith [Real.pi_gt_three]⟩

/-- **r334.F — I9 is NECESSARY, and the most cascading of the six.**
Releasing `α_RH` drags `α_NS`, `α_BSD` and `α_NP` with it through L5, I6, L3.
Four of the nine values move together. -/
theorem I9_necessary :
    wo_I9.aPoincare = 1 ∧ IsPositive wo_I9 ∧
    wo_I9.aHodge * wo_I9.aHodge = wo_I9.aPoincare * wo_I9.aHodge + wo_I9.aPoincare ∧
    wo_I9.aYM = wo_I9.aPoincare + 1 ∧
    wo_I9.aP * wo_I9.aP = wo_I9.aYM ∧
    wo_I9.aPoincare + 2 * (wo_I9.aNP - wo_I9.aHodge) = wo_I9.aRH ∧
    wo_I9.aQG * wo_I9.aQG = wo_I9.aYM * Real.pi ∧
    wo_I9.aNS = wo_I9.aRH * Real.pi ∧
    wo_I9.aNS = wo_I9.aYM * wo_I9.aBSD ∧
    wo_I9.aRH ≠ 3/2 ∧ wo_I9.aNS ≠ 3*Real.pi/2 ∧
    wo_I9.aBSD ≠ 3*Real.pi/4 ∧ wo_I9.aNP ≠ phiR + 1/4 :=
  ⟨rfl,
   ⟨by norm_num, by norm_num, phiR_pos, Real.pi_pos, by norm_num,
    by positivity, phiR_pos, sqrt2pi_pos, sqrt2_pos⟩,
   phiR_minpoly, by norm_num, sq_sqrt2, by ring, sq_sqrt2pi, by ring, by ring,
   by norm_num,
   by intro h; nlinarith [Real.pi_gt_three],
   by intro h; nlinarith [Real.pi_gt_three],
   by intro h; nlinarith⟩

/-! ## §2 — The ratio obstruction, generalized from π to every irrational

r332 proved π is not a ratio of trace-range quantities. The obstruction was
never special to π: `ℤ[1/3] ⊆ ℚ`, so every such ratio is rational. -/

/-- **★★★ r334.G — NO IRRATIONAL IS A RATIO OF SUBSTRATE TRACE-RANGE QUANTITIES ★★★**

    Generalizes `pi_not_ktheoretic_ratio` (r332.A) from π to every irrational.
    This is the uniform obstruction that closes L1, L2, L3, L4 and I6. -/
theorem no_ktheoretic_ratio_is_irrational
    {a b x : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) (hx : Irrational x) :
    b / a ≠ x := by
  intro hEq
  obtain ⟨qa, hqa⟩ := memZ13_isRat ha
  obtain ⟨qb, hqb⟩ := memZ13_isRat hb
  exact hx ⟨qb / qa, by rw [Rat.cast_div, hqa, hqb]; exact hEq⟩

/-- **r334.H — the five closures.** Each of L1, L2, L3, L4, I6 forces a value at
the anchor that is irrational, hence not a ratio of trace-range quantities. The
irrationality facts are r123's. -/
theorem five_laws_force_non_ktheoretic_values
    {a b : ℝ} (ha : MemZ13 a) (hb : MemZ13 b) :
    b / a ≠ α_Hodge ∧      -- L1 forces φ
    b / a ≠ α_P ∧          -- L2 forces √2
    b / a ≠ α_NP ∧         -- L3 forces φ + 1/4
    b / a ≠ α_QG ∧         -- L4 forces √(2π)
    b / a ≠ α_BSD :=       -- I6 forces 3π/4
  ⟨no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_Hodge,
   no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_P,
   no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_NP,
   no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_QG,
   no_ktheoretic_ratio_is_irrational ha hb irrational_alpha_BSD⟩

/-! ## §3 — I9 is the exception -/

/-- **★ r334.I — I9's forced value IS a ratio of trace-range quantities.**

    `α_RH = 3/2`. r123 proves `3/2 ∉ ℤ[1/3]` by the prime 2 — but `3` and `2`
    are both in `ℤ[1/3]`, and `3/2` is their ratio. So the obstruction that
    closes the other five does **not** close I9.

    This does not make I9 derived. It records that I9's provenance stays open on
    a narrower question, and that a uniform sweep would have been wrong. -/
theorem i9_value_is_ktheoretic_ratio :
    ∃ a b : ℝ, MemZ13 a ∧ MemZ13 b ∧ a ≠ 0 ∧ b / a = α_RH := by
  refine ⟨2, 3, memZ13_two, ?_, by norm_num, ?_⟩
  · have := memZ13_intCast 3; simpa using this
  · show (3:ℝ) / 2 = α_RH
    unfold α_RH; norm_num

/-! ## §4 — Axiom check -/

#print axioms L1_necessary
#print axioms L2_necessary
#print axioms L3_necessary
#print axioms L4_necessary
#print axioms I6_necessary
#print axioms I9_necessary
#print axioms no_ktheoretic_ratio_is_irrational
#print axioms five_laws_force_non_ktheoretic_values
#print axioms i9_value_is_ktheoretic_ratio

end

end AlphaStructuralLawAudit
end PrincipiaTractalis
