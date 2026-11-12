/-
# PF.YangMills.WilsonRPCorollaries_2026_11_11

**Corollaries of `wilson_reflection_positivity_of_continuous`** (r385, 2026-10-29).

The r385 headline is a `Matrix.PosSemidef` statement on the finite-K θ-crossed
Gram matrix of continuous test functions supported on Λ_+ ∪ Λ_0, over an even
periodic lattice. This file surfaces the Hermitian-symmetry consequence
without `Matrix (Fin K)` wrappers, which is the form OS reconstruction will
cite.

**Scope.** This is a presentation lemma, not new mathematics. It follows from
r385's headline by one specialisation through mathlib's
`Matrix.PosSemidef.isHermitian`.

**Still requires `Even L` + `Continuous F` + `supportedOnPlusZero F`.** A
density-based extension to `L²` test functions is scoped in
`codex/MILLENNIUM_STATUS_2026-11-11.md` §3 and remains open.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-11.
-/

import PF.YangMills.WilsonFubiniClosed_r385
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

namespace PF.YangMills

open Complex MeasureTheory
open scoped ComplexOrder

variable {L : ℕ} [NeZero L]

/-! ## §1 — Hermitian symmetry of the Gram matrix (K ≥ 1) -/

/-- **The θ-crossed Gram matrix is Hermitian** (swap indices ⟹ complex conjugate).

Direct from `wilson_reflection_positivity_of_continuous.isHermitian`.  For
any family of continuous test functions supported on `Λ_+ ∪ Λ_0` over an
even periodic lattice, the θ-crossed inner product is a Hermitian sesquilinear
form on the finite-index test-function space. -/
theorem wilson_rp_gram_hermitian (hL : Even L) {K : ℕ} (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF_support : ∀ i : Fin K, supportedOnPlusZero (F i))
    (hF_cont : ∀ i : Fin K, Continuous (F i)) (i j : Fin K) :
    star (∫ U, star (F j (timeReflectionGaugeField U)) * F i U
          ∂(wilsonGibbsMeasure L β))
      = ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
          ∂(wilsonGibbsMeasure L β) := by
  have hPSD := wilson_reflection_positivity_of_continuous (hL := hL) (β := β)
    (K := K) (F := F) (hF_support := hF_support) (hF_cont := hF_cont)
  have hHerm : (Matrix.of (fun i j : Fin K =>
      ∫ U, star (F i (timeReflectionGaugeField U)) * F j U
        ∂(wilsonGibbsMeasure L β))).IsHermitian := hPSD.isHermitian
  have h := congrArg (fun M : Matrix (Fin K) (Fin K) ℂ => M i j) hHerm
  simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using h

/-! ## §2 — scalar reflection positivity (K = 1 case)

Specialise `wilson_reflection_positivity_of_continuous` to `K = 1` with the
one-element family `fun _ => F`.  The Gram matrix is `1 × 1`, its sole entry
is `∫ star(F(θU)) · F(U) dμ_Gibbs`, and `PosSemidef` on a `1 × 1` complex
matrix says the entry is a non-negative real (with respect to the
`ComplexOrder` partial order). -/

/-- **Scalar RP: the θ-crossed single-function Gram entry is a non-negative
complex number** (= real part ≥ 0, imaginary part = 0).

For any continuous `F : GaugeField L → ℂ` supported on `Λ_+ ∪ Λ_0` over an
even periodic lattice. -/
theorem wilson_rp_scalar (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (hF_support : supportedOnPlusZero F)
    (hF_cont : Continuous F) :
    0 ≤ (∫ U, star (F (timeReflectionGaugeField U)) * F U
          ∂(wilsonGibbsMeasure L β)) := by
  have hPSD := wilson_reflection_positivity_of_continuous (hL := hL) (β := β)
    (K := 1) (F := fun _ => F)
    (hF_support := fun _ => hF_support) (hF_cont := fun _ => hF_cont)
  have h := hPSD.2 (fun _ => 1)
  simpa [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.of_apply] using h

/-! ## §3 — real-inequality forms

The `ComplexOrder` partial order couples `0 ≤ z` to `0 ≤ z.re ∧ z.im = 0`.
For downstream callers that prefer real-valued inequalities (and don't want
to import `ComplexOrder`), these spell it out. -/

/-- **Real part of the scalar θ-crossed Gram entry is non-negative.** -/
theorem wilson_rp_scalar_re (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (hF_support : supportedOnPlusZero F)
    (hF_cont : Continuous F) :
    0 ≤ (∫ U, star (F (timeReflectionGaugeField U)) * F U
          ∂(wilsonGibbsMeasure L β)).re :=
  (Complex.nonneg_iff.mp (wilson_rp_scalar hL β F hF_support hF_cont)).1

/-- **Imaginary part of the scalar θ-crossed Gram entry vanishes.** -/
theorem wilson_rp_scalar_im (hL : Even L) (β : ℝ)
    (F : GaugeField L → ℂ) (hF_support : supportedOnPlusZero F)
    (hF_cont : Continuous F) :
    (∫ U, star (F (timeReflectionGaugeField U)) * F U
          ∂(wilsonGibbsMeasure L β)).im = 0 :=
  ((Complex.nonneg_iff.mp (wilson_rp_scalar hL β F hF_support hF_cont)).2).symm

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.wilson_rp_gram_hermitian
#print axioms PF.YangMills.wilson_rp_scalar
#print axioms PF.YangMills.wilson_rp_scalar_re
#print axioms PF.YangMills.wilson_rp_scalar_im
