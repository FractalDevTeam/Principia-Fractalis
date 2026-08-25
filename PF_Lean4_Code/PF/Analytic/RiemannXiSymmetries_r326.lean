/-
# r326: CLASSICAL RIEMANN ξ SYMMETRIES + EXACT BRIDGE TO PF Xi WITNESS

★ 2026-08-25 r326 — symmetries of the entire classical Riemann ξ (r325)
  plus an exact critical-line formula connecting it to PF's certified
  real Xi(t) witness. ★

## What r326 proves

- **A. Functional equation.** `riemannXiEntire (1 - s) = riemannXiEntire s`
  for every `s : ℂ`, unconditionally.  Derived from
  `completedRiemannZeta₀_one_sub` + polynomial algebra `(1-s)(-s) = s(s-1)`.
- **B. Conjugation symmetry.** `riemannXiEntire (conj s) = conj (riemannXiEntire s)`
  for every `s : ℂ`, via mathlib's `completedRiemannZeta₀_conj` (available
  through XiRealWitness) + `conj` ring-hom properties.
- **C. Vertical reflection.** `riemannXiEntire ⟨1 - σ, t⟩ = conj (riemannXiEntire ⟨σ, t⟩)`
  for real `σ, t`, from A + B applied to `⟨1 - σ, t⟩ = 1 - conj ⟨σ, t⟩`.
- **C'. Norm equality.** `‖riemannXiEntire ⟨1 - σ, t⟩‖ = ‖riemannXiEntire ⟨σ, t⟩‖`.
- **D. Critical-line reality.** `(riemannXiEntire ⟨1/2, t⟩).im = 0` — the
  vertical reflection fixes `σ = 1/2`.
- **E. Exact bridge to PF Xi.** For every real `t`,
  `riemannXiEntire ⟨1/2, t⟩ = ((-((1/4 + t²)/2) * Xi t : ℝ) : ℂ)`.
  The prefactor `-((1/4 + t²)/2)` is negative (never zero) since
  `1/4 + t² > 0`.  Uses r325's off-pole factorization + `Xi_eq`.
- **F. Critical-line zero biconditional.**
  `riemannXiEntire ⟨1/2, t⟩ = 0 ↔ Xi t = 0`, from E + nonzero prefactor.
- **G. Certified ξ zero in `(1, 15)`.** Immediate corollary of r324's
  `exists_Xi_zero_between_one_and_fifteen` + F.

Downstream value: functional equation pairs the two vertical sides of any
critical-strip rectangle; conjugation pairs positive/negative imaginary
ordinates; combined vertical reflection halves the top-edge certification
domain (once boundary nonvanishing infrastructure exists).  The critical-
line bridge connects r120/r315/r324's certified Xi machinery directly
to the entire counting object.

## Scope — explicit

* IS: kernel-clean symmetry theorems for r325's `riemannXiEntire`,
  and an exact formula tying it to PF's certified Xi.
* IS: reduction of future boundary-nonvanishing certification domains
  by symmetry pairing.
* NOT: an argument-principle apparatus.
* NOT: any zero count.
* NOT: certified boundary nonvanishing.
* NOT: a finite-height RH theorem.
* NOT: a Millennium result.
* NOT: dependent on the α-skeleton, r128 StructuralLaws, I9, H_3, or T3.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.

Author: Pablo Cohen + Claude Opus 4.7.  2026-08-25.
-/

import PF.Analytic.RiemannXiEntire_r325
import PF.Analytic.RiemannZetaZeroBelow15_r324

namespace PrincipiaTractalis.RiemannXiSymmetries

open Complex
open scoped ComplexConjugate
open PrincipiaTractalis.RiemannXiEntire
open PrincipiaTractalis.XiRealWitness

/-! ## §1 — Global functional equation `ξ(1 - s) = ξ(s)` -/

/-- **A. `riemannXiEntire_one_sub`** — the classical functional equation
`ξ(1 - s) = ξ(s)` holds for EVERY `s : ℂ`, unconditionally (no pole
exclusion needed because `riemannXiEntire` is entire).

Proof: unfold the definition, use `completedRiemannZeta₀_one_sub`
(mathlib) and the polynomial identity `(1-s)((1-s)-1) = s(s-1)`. -/
theorem riemannXiEntire_one_sub (s : ℂ) :
    riemannXiEntire (1 - s) = riemannXiEntire s := by
  unfold riemannXiEntire
  rw [completedRiemannZeta₀_one_sub]
  ring

/-! ## §2 — Global conjugation symmetry -/

/-- **B. `riemannXiEntire_conj`** — `ξ(conj s) = conj (ξ s)` for every
`s : ℂ`.

Proof: unfold, use `completedRiemannZeta₀_conj` (already in the corpus via
XiRealWitness) and the fact that `conj : ℂ → ℂ` is a ring homomorphism
(so distributes over `+`, `-`, `*`, `/` and fixes `1` and the real numeral
`2`). -/
theorem riemannXiEntire_conj (s : ℂ) :
    riemannXiEntire (conj s) = conj (riemannXiEntire s) := by
  unfold riemannXiEntire
  rw [completedRiemannZeta₀_conj s]
  simp only [map_div₀, map_add, map_mul, map_sub, map_one, Complex.conj_ofNat]

/-! ## §3 — Vertical reflection about `Re s = 1/2` -/

/-- **The complex identity underlying vertical reflection.**
`(⟨1 - σ, t⟩ : ℂ) = 1 - conj ⟨σ, t⟩`. -/
lemma one_sub_conj_mk (σ t : ℝ) :
    (⟨1 - σ, t⟩ : ℂ) = 1 - conj (⟨σ, t⟩ : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.one_re, Complex.conj_re]
  · simp [Complex.sub_im, Complex.one_im, Complex.conj_im]

/-- **C. `riemannXiEntire_reflect_vertical`** — vertical reflection of ξ
about the critical line: `ξ⟨1 - σ, t⟩ = conj ξ⟨σ, t⟩`.

Proof: `⟨1 - σ, t⟩ = 1 - conj ⟨σ, t⟩` (via `one_sub_conj_mk`), then
apply functional equation A to `s = conj ⟨σ, t⟩`, then conjugation B. -/
theorem riemannXiEntire_reflect_vertical (σ t : ℝ) :
    riemannXiEntire ⟨1 - σ, t⟩ = conj (riemannXiEntire ⟨σ, t⟩) := by
  rw [one_sub_conj_mk σ t, riemannXiEntire_one_sub, riemannXiEntire_conj]

/-- **C'. `norm_riemannXiEntire_reflect_vertical`** — the norm of ξ is
symmetric under vertical reflection: `‖ξ⟨1 - σ, t⟩‖ = ‖ξ⟨σ, t⟩‖`.

Direct consequence of C + `Complex.norm_conj`. -/
theorem norm_riemannXiEntire_reflect_vertical (σ t : ℝ) :
    ‖riemannXiEntire ⟨1 - σ, t⟩‖ = ‖riemannXiEntire ⟨σ, t⟩‖ := by
  rw [riemannXiEntire_reflect_vertical]
  exact Complex.norm_conj _

/-! ## §4 — Critical-line reality of ξ -/

/-- **D. `riemannXiEntire_critical_self_conj`** — on the critical line
`Re s = 1/2`, ξ takes real values: `conj (ξ⟨1/2, t⟩) = ξ⟨1/2, t⟩`.

Proof: apply the vertical-reflection theorem C at `σ = 1/2`, noting
`⟨1 - 1/2, t⟩ = ⟨1/2, t⟩`. -/
theorem riemannXiEntire_critical_self_conj (t : ℝ) :
    conj (riemannXiEntire ⟨1/2, t⟩) = riemannXiEntire ⟨1/2, t⟩ := by
  have h := riemannXiEntire_reflect_vertical (1/2) t
  have hσ : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [hσ] at h
  exact h.symm

/-- The imaginary part of `ξ⟨1/2, t⟩` vanishes. -/
theorem riemannXiEntire_critical_im_eq_zero (t : ℝ) :
    (riemannXiEntire ⟨1/2, t⟩).im = 0 :=
  Complex.conj_eq_iff_im.mp (riemannXiEntire_critical_self_conj t)

/-! ## §5 — Exact critical-line bridge to PF's Xi -/

/-- **Complex algebra at `s = ⟨1/2, t⟩`.**
`(⟨1/2, t⟩ : ℂ) · (⟨1/2, t⟩ - 1) = ((-(1/4 + t²) : ℝ) : ℂ)`. -/
lemma critical_mul_sub_one (t : ℝ) :
    (⟨1/2, t⟩ : ℂ) * ((⟨1/2, t⟩ : ℂ) - 1) = ((-(1/4 + t^2) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
               Complex.one_im, Complex.ofReal_re]
    ring
  · simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
               Complex.one_im, Complex.ofReal_im]
    ring

/-- **E. `riemannXiEntire_critical_eq_Xi`** — EXACT formula for the
classical entire ξ on the critical line in terms of PF's certified
real witness `Xi`:

    riemannXiEntire ⟨1/2, t⟩ = ((-((1/4 + t^2)/2) * Xi t : ℝ) : ℂ).

Proof: r325's `riemannXiEntire_eq_completed` (needing `⟨1/2,t⟩ ≠ 0, 1`)
gives `ξ = s(s-1)·Λ / 2`; `critical_mul_sub_one` computes
`s(s-1) = -(1/4 + t²)`; `Xi_eq` (from XiRealWitness) gives
`Λ⟨1/2, t⟩ = ((Xi t : ℝ) : ℂ)`. -/
theorem riemannXiEntire_critical_eq_Xi (t : ℝ) :
    riemannXiEntire ⟨1/2, t⟩ = ((-((1/4 + t^2)/2) * Xi t : ℝ) : ℂ) := by
  have hs0 : (⟨1/2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  have hs1 : (⟨1/2, t⟩ : ℂ) ≠ 1 := critical_point_ne_one t
  rw [riemannXiEntire_eq_completed hs0 hs1, Xi_eq t, critical_mul_sub_one t]
  push_cast
  ring

/-! ## §6 — Critical-line zero biconditional -/

/-- **The critical-line prefactor is negative (nonzero) for every real `t`.** -/
lemma neg_quarter_plus_t_sq_div_two_ne_zero (t : ℝ) :
    -((1/4 + t^2)/2) ≠ 0 := by
  have hpos : 0 < 1/4 + t^2 := by nlinarith [sq_nonneg t]
  have hhalf : 0 < (1/4 + t^2)/2 := by linarith
  linarith

/-- **F. `riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero`** — the zeros
of the classical entire ξ on the critical line are EXACTLY the zeros of
PF's certified real witness Xi.

Direct from E + the nonzero prefactor `-((1/4 + t²)/2)`. -/
theorem riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero (t : ℝ) :
    riemannXiEntire ⟨1/2, t⟩ = 0 ↔ Xi t = 0 := by
  rw [riemannXiEntire_critical_eq_Xi t]
  rw [show ((0 : ℂ)) = (((0 : ℝ)) : ℂ) from (Complex.ofReal_zero).symm]
  rw [Complex.ofReal_inj]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (neg_quarter_plus_t_sq_div_two_ne_zero t)
  · intro h
    rw [h, mul_zero]

/-! ## §7 — Certified ξ zero strictly between heights 1 and 15 -/

/-- **G. `exists_riemannXiEntire_zero_between_one_and_fifteen`** — the
entire counting object of r325 has a KERNEL-CERTIFIED zero on the
critical line with ordinate strictly between 1 and 15.

Immediate corollary of r324's `exists_Xi_zero_between_one_and_fifteen`
(via `Xi_one_neg + Xi_15_pos + IVT`) and F. -/
theorem exists_riemannXiEntire_zero_between_one_and_fifteen :
    ∃ t : ℝ, 1 < t ∧ t < 15 ∧ riemannXiEntire ⟨1/2, t⟩ = 0 := by
  obtain ⟨t, h1, h15, hXi_t⟩ :=
    PrincipiaTractalis.RiemannZetaZeroBelow15.exists_Xi_zero_between_one_and_fifteen
  refine ⟨t, h1, h15, ?_⟩
  rw [riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero]
  exact hXi_t

end PrincipiaTractalis.RiemannXiSymmetries

/-! ## §8 — Axiom check -/

#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_one_sub
#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_conj
#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_reflect_vertical
#print axioms PrincipiaTractalis.RiemannXiSymmetries.norm_riemannXiEntire_reflect_vertical
#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_self_conj
#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_im_eq_zero
#print axioms PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_eq_Xi
#print axioms
  PrincipiaTractalis.RiemannXiSymmetries.riemannXiEntire_critical_eq_zero_iff_Xi_eq_zero
#print axioms
  PrincipiaTractalis.RiemannXiSymmetries.exists_riemannXiEntire_zero_between_one_and_fifteen
