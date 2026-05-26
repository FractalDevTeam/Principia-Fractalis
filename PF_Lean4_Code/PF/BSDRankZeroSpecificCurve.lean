/-
# BSD on a Specific Rank-0 Elliptic Curve — E: y² = x³ - x

★ 2026-05-25 — First per-curve BSD discharge in the framework ★

## What this file does

The framework's `BSDConjecture` (see `PF/MillenniumSixReductions.lean`,
2026-05-19) quantifies over `WeierstrassCurve ℚ` and is discharged by
`bsd_via_fractal_resonance` from the named hypothesis
`fractalBSDRankEquality` at `α = 3π/4`. Both Lean-side definitions
use the placeholder `BSD_equality_holds _ := True` because mathlib
currently has neither:

  * the Hasse-Weil L-function for elliptic curves `L(E, s)`, nor
  * the Mordell-Weil rank `rank E(ℚ)` as a number.

So the conditional reduction is real (it manipulates a true
`WeierstrassCurve ℚ` quantifier), but its conclusion is symbolic.

This file does what *can* be done with current mathlib: it picks ONE
specific curve, certifies it is an elliptic curve via the discriminant
computation, names it as the framework's first concrete BSD instance,
and connects it to the Ch 24 distinguished eigenvalue `φ/e ≈ 0.595`.

## The curve

We pick `E: y² = x³ - x`, which is the same as the affine model with
Weierstrass parameters `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -1, 0)`.

This is the simplest CM elliptic curve over `ℚ`:
* j-invariant `1728`
* CM by `ℤ[i]` (the Gaussian integers)
* Mordell-Weil group `E(ℚ) ≅ ℤ/2 × ℤ/2` (only the four 2-torsion points
  `O`, `(0,0)`, `(±1, 0)` — known classically, see e.g. Silverman §X.6)
* analytic rank 0 (Kolyvagin / Coates–Wiles for CM curves)
* conductor 32 (= 2⁵)
* LMFDB label `32.a3`

So the BSD claim `rank = ord_{s=1} L(E,s) = 0` is fully known for this
curve. The classical proof:
* rank 0 by 2-descent or by Coates–Wiles (CM ⇒ L(E,1) controls rank).
* `L(E, 1) ≠ 0` via the explicit Hecke-character computation
  (`E` has CM by `ℤ[i]`, so `L(E, s) = L(s, ψ) L(s, ψ̄)` for the
  associated Grossencharacter `ψ`; non-vanishing at `s = 1` is
  the central value of a non-trivial Hecke L-function).

## What we PROVE here (axiom-free in this file)

1. `E_rank_zero_curve : WeierstrassCurve ℚ` — the explicit coefficients.
2. `E_rank_zero_Δ_eq : E_rank_zero_curve.Δ = 64` — explicit discriminant
   computation (axiom-free, `decide`/`norm_num`).
3. `E_rank_zero_Δ_ne_zero` — the discriminant is non-zero in `ℚ`.
4. `E_rank_zero_isElliptic : E_rank_zero_curve.IsElliptic` — registers
   the curve in mathlib's elliptic-curve typeclass.
5. `E_rank_zero_j_eq_1728` — the j-invariant matches the LMFDB value.
6. `BSD_holds_on_E_rank_zero` — the framework's `BSD_equality_holds`
   for this specific curve. (Trivially `True` under the current
   structural placeholder, but quantified at a specific elliptic curve
   in the genuine `WeierstrassCurve ℚ` type rather than universally.)
7. `E_rank_zero_satisfies_BSD_distinguished_bracket` — connects the
   curve to the Ch 24 distinguished eigenvalue `φ/e`:
   the framework's predicted eigenvalue is in `(0.59, 0.60)`, and we
   anchor this *to this specific curve* by witnessing that φ/e lies
   in the bracketed range. (Witness, not a derivation of φ/e from `E`.)

## Honest scope statement

* This file does NOT prove BSD on `E: y² = x³ - x` from first principles
  inside Lean. The Lean-side BSD conjecture predicate is the framework's
  symbolic placeholder; we discharge that placeholder for this one
  concrete curve.
* The classical proof of rank-0 / L(E,1) ≠ 0 for this curve exists in
  the literature (Coates–Wiles 1977 for CM curves, plus explicit
  Hecke-character central-value computations); this file records the
  Lean side of "BSD holds on E_rank_zero_curve" but does not formalize
  Coates–Wiles or the Hecke L-function.
* What is new: prior to this file the framework's BSD discharge ran
  over the universal `WeierstrassCurve ℚ` quantifier with no specific
  curve singled out. This file singles out the first specific curve
  and certifies its membership in mathlib's `IsElliptic` typeclass,
  so that any future strengthening of `BSD_equality_holds` will land
  on a non-trivial first witness.

## Build

ZERO project axioms in this file. Build clean.
-/

import PF.MillenniumSixReductions
import PF.IntervalArithmetic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

namespace PrincipiaTractalis.BSDRankZero

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix

/-! ## The curve `E: y² = x³ - x` -/

/-- The rank-0 CM elliptic curve `E: y² = x³ - x` (LMFDB `32.a3`),
    in Weierstrass form `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, -1, 0)`. -/
def E_rank_zero_curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

/-! ## Discriminant and elliptic-ness (axiom-free) -/

/-- The discriminant of `E: y² = x³ - x` is `64` (= `2⁶`).
    Direct computation: with `b₂=0, b₄=-2, b₆=0, b₈=-1`,
    `Δ = -b₂²·b₈ - 8·b₄³ - 27·b₆² + 9·b₂·b₄·b₆ = -8·(-8) = 64`. -/
@[simp] theorem E_rank_zero_Δ_eq :
    E_rank_zero_curve.Δ = 64 := by
  show E_rank_zero_curve.Δ = (64 : ℚ)
  unfold E_rank_zero_curve
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The discriminant is non-zero in `ℚ`. -/
theorem E_rank_zero_Δ_ne_zero : E_rank_zero_curve.Δ ≠ 0 := by
  rw [E_rank_zero_Δ_eq]
  norm_num

/-- `E_rank_zero_curve` is an elliptic curve over `ℚ` (Mathlib's
    `IsElliptic` typeclass, defined as `IsUnit Δ`). -/
instance E_rank_zero_isElliptic : E_rank_zero_curve.IsElliptic := by
  refine ⟨?_⟩
  rw [E_rank_zero_Δ_eq]
  exact isUnit_of_invertible (64 : ℚ)

/-- The `c₄` coefficient: `c₄ = 48` for this curve. -/
@[simp] theorem E_rank_zero_c₄_eq :
    E_rank_zero_curve.c₄ = 48 := by
  show E_rank_zero_curve.c₄ = (48 : ℚ)
  unfold E_rank_zero_curve
  simp [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

/-- The `c₆` coefficient: `c₆ = 0` for this curve. -/
@[simp] theorem E_rank_zero_c₆_eq :
    E_rank_zero_curve.c₆ = 0 := by
  show E_rank_zero_curve.c₆ = (0 : ℚ)
  unfold E_rank_zero_curve
  simp [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
  ring

/-- The j-invariant is `1728`, matching the LMFDB record for `32.a3`.
    Computation: `j = Δ'⁻¹ · c₄³ = 64⁻¹ · 48³ = 110592/64 = 1728`. -/
theorem E_rank_zero_j_eq_1728 :
    E_rank_zero_curve.j = 1728 := by
  -- j = Δ'⁻¹ * c₄^3, where Δ' is the unit version of Δ
  -- Δ = 64, c₄ = 48, so c₄^3 = 110592, and 110592 / 64 = 1728
  unfold WeierstrassCurve.j
  rw [E_rank_zero_c₄_eq]
  have hΔ : (E_rank_zero_curve.Δ' : ℚ) = 64 := by
    rw [WeierstrassCurve.coe_Δ', E_rank_zero_Δ_eq]
  -- (Δ')⁻¹ * 48^3 should equal 1728 in ℚ. Use Units cast.
  have : ((E_rank_zero_curve.Δ')⁻¹ : ℚˣ) * (48 : ℚˣ)^3 = (1728 : ℚˣ) := by
    apply Units.ext
    show ((E_rank_zero_curve.Δ')⁻¹ : ℚ) * (48 : ℚ)^3 = (1728 : ℚ)
    have hΔ' : ((E_rank_zero_curve.Δ')⁻¹ : ℚ) = (1 : ℚ) / 64 := by
      have : ((E_rank_zero_curve.Δ' : ℚˣ)⁻¹ : ℚ) * (E_rank_zero_curve.Δ' : ℚ) = 1 := by
        rw [← Units.val_mul]; simp
      field_simp at this
      rw [hΔ] at this
      linarith
    rw [hΔ']
    ring
  -- Now `this` says (Δ')⁻¹ * 48^3 = 1728 at the units level; coerce.
  have := congrArg (fun u => (u : ℚ)) this
  simp at this
  -- Unfortunately the goal involves the (·)⁻¹ on the unit; reduce by value
  -- via Units.val_inv_eq_inv_val and rfl on 48^3.
  -- Direct numerical: 48^3 = 110592, 110592 / 64 = 1728.
  have hΔ' : ((E_rank_zero_curve.Δ')⁻¹ : ℚ) = (1 : ℚ) / 64 := by
    have h := Units.mul_inv (E_rank_zero_curve.Δ')
    have hcast : ((E_rank_zero_curve.Δ' * (E_rank_zero_curve.Δ')⁻¹ : ℚˣ) : ℚ) = (1 : ℚ) := by
      rw [h]; rfl
    rw [Units.val_mul, hΔ] at hcast
    have h64 : (64 : ℚ) ≠ 0 := by norm_num
    field_simp at hcast
    linarith
  rw [hΔ']
  norm_num

/-! ## The framework's BSD claim, discharged on this curve -/

/-- **First specific-curve BSD discharge**.

    The framework's `BSD_equality_holds` predicate, evaluated on the
    rank-0 CM curve `E: y² = x³ - x`, holds.

    Under the current Lean encoding (where `BSD_equality_holds _` is
    the structural placeholder `True` awaiting the L-function and
    Mordell-Weil rank in mathlib), this discharge is `trivial`.
    However the witness `E_rank_zero_curve` is a *genuine*
    `WeierstrassCurve ℚ` and (above) a *genuine* elliptic curve in the
    `IsElliptic` typeclass, so this is the first per-curve concrete
    landing of the BSD architecture in the framework. -/
theorem BSD_holds_on_E_rank_zero :
    BSD_equality_holds E_rank_zero_curve := by
  trivial

/-- **Convenience corollary**: the framework's universal `BSDConjecture`,
    restricted to this single curve, holds. -/
theorem BSDConjecture_restricted_to_E_rank_zero :
    BSD_equality_holds E_rank_zero_curve ∧
    E_rank_zero_curve.IsElliptic := by
  exact ⟨BSD_holds_on_E_rank_zero, E_rank_zero_isElliptic⟩

/-! ## Bracket connection to the Ch 24 distinguished eigenvalue φ/e -/

/-- **Sharp bracket on `bsd_distinguished_eigenvalue = φ/e`**:
    `0.59 < φ/e < 0.60` (axiom-free, derived from φ ≤ 1.6180339888 and
    e > 2.718281828). -/
theorem bsd_distinguished_eigenvalue_sharp_bracket :
    (0.59 : ℝ) < bsd_distinguished_eigenvalue ∧
    bsd_distinguished_eigenvalue < (0.60 : ℝ) := by
  unfold bsd_distinguished_eigenvalue
  obtain ⟨hphi_lo, hphi_hi⟩ := phi_in_interval_10digit
  -- We use the standard `Real.exp_one_lt_d9` / `Real.exp_one_gt_d9` bounds:
  -- 2.7182818283 < e < 2.7182818286
  have he_lo : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he_hi : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  refine ⟨?_, ?_⟩
  · -- 0.59 < φ/e: equivalent to 0.59 · e < φ; use φ ≥ 1.6180339887 and e < 2.7182818286
    rw [lt_div_iff₀ he_pos]
    -- 0.59 · e < φ; use upper bound on e (since LHS multiplies by e, an upper bound is needed)
    -- 0.59 · 2.7182818286 = 1.603786279 ... < 1.6180339887 ≤ φ. OK.
    nlinarith [hphi_lo, he_hi]
  · -- φ/e < 0.60: equivalent to φ < 0.60 · e; use φ ≤ 1.6180339888 and e > 2.7182818283
    rw [div_lt_iff₀ he_pos]
    -- 0.60 · 2.7182818283 = 1.630969097 > 1.6180339888 ≥ φ. OK.
    nlinarith [hphi_hi, he_lo]

/-- **Per-curve anchor to the Ch 24 distinguished eigenvalue**.

    Records, *with the explicit witness `E_rank_zero_curve` in scope*,
    that the framework's Ch 24 distinguished eigenvalue `φ/e` sits in
    the bracketed range `(0.59, 0.60)`.

    Manuscript reference `conj:rank-equality-fractal`: the multiplicity
    of `φ/e` in `Spec(T_E)` predicts `rank E(ℚ)`. For this CM rank-0
    curve, the classical answer is `0`; the eigenvalue bracket here
    records the *framework constant* this curve's spectral problem would
    be measured against, once the operator `T_E` is constructed in Lean. -/
theorem E_rank_zero_satisfies_BSD_distinguished_bracket :
    (0.59 : ℝ) < bsd_distinguished_eigenvalue ∧
    bsd_distinguished_eigenvalue < (0.60 : ℝ) ∧
    E_rank_zero_curve.IsElliptic ∧
    BSD_equality_holds E_rank_zero_curve := by
  obtain ⟨h_lo, h_hi⟩ := bsd_distinguished_eigenvalue_sharp_bracket
  exact ⟨h_lo, h_hi, E_rank_zero_isElliptic, BSD_holds_on_E_rank_zero⟩

end PrincipiaTractalis.BSDRankZero
