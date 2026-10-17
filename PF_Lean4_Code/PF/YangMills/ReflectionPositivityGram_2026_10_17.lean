/-
# Yang-Mills — Reflection Positivity Gram PSD (step 3 of Rio's YM plan)

**Rio's YM step 3, 2026-10-17** (codex `f85c078b`). With Haar + Wilson
measure built, the **first genuine Yang-Mills measure theorem** in the
repo: the measure-level Gram matrix on any finite ℂ-valued test family
has PSD-via-non-negative-integrand structure. Composes:

* Waves 48B-52D's algebraic rank-K Gram PSD core
  (`YMReflectionPositivity3plus1DRankKAttempt.lean`, 2026-05-31) —
  `Σ_k v_k · v_kᵀ` is PSD;
* with the Wilson Gibbs measure built this session (commits `a25ca2fa`,
  `e48a03d3`) —

yielding the Bochner-integral version:
`G_ij := ∫ star(F_i) · F_j dμ` is PSD on any test family whose quadratic
form factors through `∫ ‖h(x)‖² dμ(x)`.

### What this file provides

* `gramMatrix_posSemidef_from_quadratic_eq_nonneg` — the general shell
  theorem on an arbitrary measure space. Takes a Hermitian matrix `G`
  and a factorization of its quadratic form through a non-negative,
  integrable real-valued function; concludes `G.PosSemidef`.

* `gram_quadratic_form_eq_integral_norm_sq` — the structural identity
  that for any test family and coefficient vector, the Gram quadratic
  form equals `∫ ‖Σ c_i F_i‖² dμ` (under integrability of the pairwise
  products).

* `gramMatrix_bochner_isHermitian` — Hermiticity of the Bochner Gram
  matrix.

* `gramMatrix_bochner_posSemidef` — the full theorem assembled from the
  three pieces: for any ℂ-valued test family with integrable pairwise
  products, the Gram matrix `G_ij := ∫ star(F_i) · F_j dμ` is PSD.

* `wilson_gramMatrix_posSemidef` — specialization to the Wilson Gibbs
  measure.

* `timeReflectionSite`, `timeReflectionLink`, `timeReflectionGaugeField`
  — the lattice time-reversal involution.

* `wilson_reflection_gram_posSemidef` — the `(F ∘ θ)` Gram PSD.

### Where this lands in the YM program

* **First measure-level PSD theorem in the YM track.** Prior waves
  48B-52D realized the pure linear-algebra core; this is the
  measure-integral lift.
* **Not** the full lattice OS-RP theorem — that requires the Wilson
  action's straddling-plaquette decomposition
  `S_W(U) = S_-(U_-) + S_0(U_0) + S_+(U_+) + S_cross(U_-, U_0, U_+)`
  and factorization through the time-zero slice. Deferred.

### Three-axiom bar

Every declaration kernel-clean `[propext, Classical.choice, Quot.sound]`.
No sorry.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import PF.YangMills.WilsonMeasure_2026_10_17
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false

namespace PF.YangMills

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

/-! ## §1 — Shell PSD theorem: factorization through a non-negative real integral. -/

/-- **Shell Gram PSD** — if a Hermitian ℂ-matrix's quadratic form equals an
integral of a pointwise non-negative, integrable real-valued function, then
the matrix is positive-semidefinite.

Composes directly with any explicit factorization `star c ⬝ᵥ G *ᵥ c =
((∫ f c dμ : ℝ) : ℂ)` — the content of the Bochner-level rank-K Gram PSD. -/
theorem gramMatrix_posSemidef_from_quadratic_eq_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : ℕ} (G : Matrix (Fin K) (Fin K) ℂ)
    (hHerm : G.IsHermitian)
    (f : (Fin K → ℂ) → α → ℝ)
    (h_nn : ∀ c x, 0 ≤ f c x)
    (h_eq : ∀ c : Fin K → ℂ,
      star c ⬝ᵥ (G *ᵥ c) = ((∫ x, f c x ∂μ : ℝ) : ℂ)) :
    G.PosSemidef := by
  refine ⟨hHerm, fun c => ?_⟩
  rw [h_eq]
  exact RCLike.ofReal_nonneg.mpr
    (integral_nonneg_of_ae (Filter.Eventually.of_forall (h_nn c)))

/-! ## §2 — The Hermiticity of the Bochner Gram matrix. -/

/-- **Hermiticity**: `(∫ star(F_i) · F_j dμ)` is Hermitian in `i, j`. Follows
from `integral_conj` and the identity `conj(star(F_i) · F_j) = star(F_j) · F_i`. -/
theorem gramMatrix_bochner_isHermitian
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : ℕ} (F : Fin K → α → ℂ) :
    (Matrix.of (fun i j : Fin K => ∫ x, star (F i x) * F j x ∂μ)).IsHermitian := by
  funext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (starRingEnd ℂ) ((starRingEnd ℂ) (F j x) * F i x)
       = (starRingEnd ℂ) (F i x) * F j x
  rw [map_mul, RCLike.conj_conj]
  ring

/-! ## §3 — The structural identity: quadratic form equals ∫ ‖·‖². -/

/-- **Structural identity for the Gram quadratic form**:
`star c ⬝ᵥ G *ᵥ c = ∫ ‖Σ_i c_i F_i(x)‖² dμ(x)` (as a complex number via
real cast).

Proof: expand the dot-product and mulVec on `Matrix.of`, pull each
coefficient inside the integral via `integral_const_mul`, swap sum
and integral via `integral_finset_sum` (using the integrability
hypothesis on pairwise products), then collect:
`star(c_i · F_i(x)) · (c_j · F_j(x))` summed over `i, j` equals
`star(Σ_i c_i F_i(x)) · (Σ_j c_j F_j(x)) = ‖Σ_i c_i F_i(x)‖²` via
`RCLike.conj_mul`. -/
theorem gram_quadratic_form_eq_integral_norm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : ℕ} (F : Fin K → α → ℂ) (c : Fin K → ℂ)
    (hF : ∀ i j : Fin K, Integrable (fun x => star (F i x) * F j x) μ) :
    (star c) ⬝ᵥ ((Matrix.of
        (fun i j : Fin K => ∫ x, star (F i x) * F j x ∂μ)) *ᵥ c)
      = ((∫ x, ‖∑ i, c i * F i x‖^2 ∂μ : ℝ) : ℂ) := by
  -- Step A: expand LHS as Σ_i Σ_j star(c i) * c j * ∫ star(F i) * F j dμ.
  have hA : (star c) ⬝ᵥ ((Matrix.of
      (fun i j : Fin K => ∫ x, star (F i x) * F j x ∂μ)) *ᵥ c)
    = ∑ i, ∑ j, star (c i) * c j * (∫ x, star (F i x) * F j x ∂μ) := by
    show (∑ i, star (c i) * (∑ j, (∫ x, star (F i x) * F j x ∂μ) * c j)) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hA]
  -- Step B: Each term equals ∫ star(c i * F i x) * (c j * F j x) dμ.
  have hB : ∀ i j, star (c i) * c j * (∫ x, star (F i x) * F j x ∂μ)
    = ∫ x, star (c i * F i x) * (c j * F j x) ∂μ := by
    intros i j
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change star (c i) * c j * (star (F i x) * F j x)
         = star (c i * F i x) * (c j * F j x)
    rw [show star (c i * F i x) = star (F i x) * star (c i) from StarMul.star_mul _ _]
    ring
  simp_rw [hB]
  -- Step C: Swap outer sum and integral.
  rw [show (∑ i, ∑ j, ∫ x, star (c i * F i x) * (c j * F j x) ∂μ)
        = ∑ i, ∫ x, ∑ j, star (c i * F i x) * (c j * F j x) ∂μ from by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_finset_sum]
    intros j _
    exact ((hF i j).const_mul (c j)).const_mul (star (c i)) |>.congr
      (Filter.Eventually.of_forall fun x => by
          change star (c i) * (c j * (star (F i x) * F j x))
               = star (c i * F i x) * (c j * F j x)
          rw [show star (c i * F i x) = star (F i x) * star (c i) from StarMul.star_mul _ _]
          ring)]
  rw [← integral_finset_sum]
  · -- Step D: integrand = ‖Σ c_i F_i‖² (as cast from ℝ)
    have hPoint : ∀ x, (∑ i, ∑ j, star (c i * F i x) * (c j * F j x))
                     = ((‖∑ i, c i * F i x‖^2 : ℝ) : ℂ) := by
      intro x
      rw [show (∑ i, ∑ j, star (c i * F i x) * (c j * F j x))
            = (∑ i, star (c i * F i x)) * (∑ j, c j * F j x) from
          (Fintype.sum_mul_sum _ _).symm]
      rw [show (∑ i, star (c i * F i x))
            = star (∑ i, c i * F i x) from by
          rw [show (star : ℂ → ℂ) = starRingEnd ℂ from rfl]
          exact (map_sum (starRingEnd ℂ) _ _).symm]
      rw [show star (∑ i, c i * F i x) = (starRingEnd ℂ) (∑ i, c i * F i x) from rfl]
      rw [RCLike.conj_mul]
      push_cast
      rfl
    rw [show (fun x => ∑ i, ∑ j, star (c i * F i x) * (c j * F j x))
          = fun x => ((‖∑ i, c i * F i x‖^2 : ℝ) : ℂ) from
        funext hPoint]
    exact integral_ofReal
  · intro i _
    exact integrable_finset_sum _ fun j _ =>
      ((hF i j).const_mul (c j)).const_mul (star (c i)) |>.congr
        (Filter.Eventually.of_forall fun x => by
          change star (c i) * (c j * (star (F i x) * F j x))
               = star (c i * F i x) * (c j * F j x)
          rw [show star (c i * F i x) = star (F i x) * star (c i) from StarMul.star_mul _ _]
          ring)

/-! ## §4 — Full Bochner-integral Gram PSD. -/

/-- **★ Measure-level Gram PSD (Bochner integral form) ★** — the
Bochner-integral lift of the rank-K sum-of-outer-products PSD theorem
(Waves 48B-52D).

For any measure space `(α, μ)`, any `K : ℕ`, and any ℂ-valued test family
`F : Fin K → α → ℂ` with each pairwise product
`star (F_i(x)) · F_j(x)` integrable, the Gram matrix
`G_ij := ∫ star(F_i(x)) · F_j(x) dμ(x)` is positive-semidefinite.

Proof: Hermiticity from `gramMatrix_bochner_isHermitian`. Positivity
from `gram_quadratic_form_eq_integral_norm_sq` + non-negativity of the
integral of `‖·‖²`. -/
theorem gramMatrix_bochner_posSemidef
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : ℕ} (F : Fin K → α → ℂ)
    (hF : ∀ i j : Fin K, Integrable (fun x => star (F i x) * F j x) μ) :
    (Matrix.of (fun i j : Fin K =>
        ∫ x, star (F i x) * F j x ∂μ)).PosSemidef :=
  gramMatrix_posSemidef_from_quadratic_eq_nonneg μ _
    (gramMatrix_bochner_isHermitian μ F)
    (fun c x => ‖∑ i, c i * F i x‖^2)
    (fun _ _ => sq_nonneg _)
    (fun c => gram_quadratic_form_eq_integral_norm_sq μ F c hF)

/-! ## §5 — Specialization to the Wilson Gibbs measure. -/

/-- **Measure-level Gram PSD on Wilson configurations** — the first
genuine measure-theoretic PSD in the YM track. For any finite ℂ-valued
test family on gauge-field configurations with integrable pairwise
products under the Wilson Gibbs measure, the Gram matrix is PSD. -/
theorem wilson_gramMatrix_posSemidef {L K : ℕ} [NeZero L] (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF : ∀ i j : Fin K,
      Integrable (fun U => star (F i U) * F j U) (wilsonGibbsMeasure L β)) :
    (Matrix.of (fun i j : Fin K =>
        ∫ U, star (F i U) * F j U ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  gramMatrix_bochner_posSemidef (wilsonGibbsMeasure L β) F hF

/-! ## §6 — Lattice time reflection. -/

/-- **Time reflection on a lattice site** — flips the 0-coordinate,
leaves spatial coordinates fixed. On `Fin L`, negation is `-k mod L`. -/
def timeReflectionSite {L : ℕ} [NeZero L] (x : LatticeSite L) : LatticeSite L :=
  Function.update x 0 (-(x 0))

/-- **Time reflection on a link**: reflects the base site; keeps direction. -/
def timeReflectionLink {L : ℕ} [NeZero L]
    (ℓ : LatticeLink L) : LatticeLink L :=
  (timeReflectionSite ℓ.1, ℓ.2)

/-- **Time reflection on a gauge field**: pull back the link values. -/
def timeReflectionGaugeField {L : ℕ} [NeZero L]
    (U : GaugeField L) : GaugeField L :=
  fun ℓ => U (timeReflectionLink ℓ)

/-! ## §7 — The θ-reflected Gram matrix PSD. -/

/-- **θ-reflected Gram PSD** — specialization of
`wilson_gramMatrix_posSemidef` to the time-reflected test family
`(F_i ∘ θ)_i`. The Gram matrix
`G_ij := ∫ star(F_i(θU)) · F_j(θU) dμ_β(U)` is PSD.

Note: the full OS-reflection positivity theorem is `G_ij := ∫ star(F_i(θU))
· F_j(U) dμ_β(U)` (NOT both reflected), and depends on the Wilson
action's straddling-plaquette decomposition; the symmetric reflected
version here is the first-pass measure-level theorem. -/
theorem wilson_reflection_gram_posSemidef {L K : ℕ} [NeZero L] (β : ℝ)
    (F : Fin K → GaugeField L → ℂ)
    (hF : ∀ i j : Fin K,
      Integrable (fun U => star (F i (timeReflectionGaugeField U))
                           * F j (timeReflectionGaugeField U))
        (wilsonGibbsMeasure L β)) :
    (Matrix.of (fun i j : Fin K =>
        ∫ U, star (F i (timeReflectionGaugeField U))
             * F j (timeReflectionGaugeField U)
         ∂(wilsonGibbsMeasure L β))).PosSemidef :=
  wilson_gramMatrix_posSemidef β
    (fun i U => F i (timeReflectionGaugeField U)) hF

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.gramMatrix_posSemidef_from_quadratic_eq_nonneg
#print axioms PF.YangMills.gramMatrix_bochner_isHermitian
#print axioms PF.YangMills.gram_quadratic_form_eq_integral_norm_sq
#print axioms PF.YangMills.gramMatrix_bochner_posSemidef
#print axioms PF.YangMills.wilson_gramMatrix_posSemidef
#print axioms PF.YangMills.timeReflectionSite
#print axioms PF.YangMills.timeReflectionLink
#print axioms PF.YangMills.timeReflectionGaugeField
#print axioms PF.YangMills.wilson_reflection_gram_posSemidef
