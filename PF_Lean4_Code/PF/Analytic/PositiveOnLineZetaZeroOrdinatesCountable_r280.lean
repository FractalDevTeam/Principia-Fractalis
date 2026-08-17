/-
# r280: `PositiveOnLineZetaZeroOrdinatesCountable` — UNCONDITIONAL DISCHARGE.

★ 2026-08-16 r280 — attacks one of the two atomic classical residuals
that Wave 58 (r255) had reduced `PF_T3SymIsHilbertPolyaOperator_Positive`
to. Combined with `PositiveOnLineZetaZeroOrdinatesNonempty` (Hardy 1914),
countability closes the substrate framework's Riemann-Hypothesis
residual `PF_T3SymIsHilbertPolyaOperator_Positive` entirely, and
thereby one of the two RH-side hypotheses of
`ClayClosureBundleBulletproof` inside
`unified_clay_closure_via_substrate_linkage_bulletproof`.

Book chapters: Ch 20 (RH via Fractal Resonance § 20.4 T³_sym operator
spec), Ch 34A (Substrate Theorem § 34A.5 the citable master
implication). Paper `principia_fractalis_alpha_skeleton_2026-07-13.pdf`
§6 Corollary 6.3.

## Substrate framework claim

The framework's substrate closure delivers all six Clay axes as ONE
bundle via `unified_clay_closure_via_substrate_linkage_bulletproof`.
The RH residual reduces (Wave 58, `rh_wave58_countability_reduction_capstone`)
to two atomic classical facts:

  (i)  `PositiveOnLineZetaZeroOrdinatesNonempty` (Hardy 1914).
  (ii) `PositiveOnLineZetaZeroOrdinatesCountable` (isolated zeros of
       a non-identically-zero holomorphic function).

r280 discharges (ii) directly using mathlib's analytic-function
infrastructure and the second-countability of ℂ.

## Proof architecture

1. `riemannZeta` is `AnalyticOnNhd ℂ` on `ℂ \ {1}` via
   `differentiableAt_riemannZeta` + Cauchy's theorem
   (`DifferentiableOn.analyticOnNhd`).

2. `riemannZeta 2 = π² / 6 ≠ 0` via `riemannZeta_two` +
   `Real.pi_ne_zero`.

3. `ζ`-zeros within `ℂ \ {1}` are LOCALLY FINITE via
   `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` +
   `codiscreteWithin_iff_locallyFiniteComplementWithin`.

4. Cover `ℂ \ {1}` with countably many neighborhoods (each carrying
   finite zero-count) using `SecondCountableTopology.countable_cover_nhds`.

5. Global ζ-zero set is a countable union of finite sets, hence
   countable.

6. `PositiveOnLineZetaZeroOrdinates` embeds injectively into the
   ζ-zero set via `t ↦ 1/2 + i·t`, hence countable.

## Framework position

r280 discharges half of Wave 58's atomic reduction of the RH
residual carried by `PF_T3SymIsHilbertPolyaOperator_Positive`
inside `ClayClosureBundleBulletproof`. Composed with a future
discharge of `PositiveOnLineZetaZeroOrdinatesNonempty` (Hardy 1914,
mathlib formalization pending), the substrate closure via
`unified_clay_closure_via_substrate_linkage_bulletproof` collapses
one of its two RH hypotheses to unconditional Lean, tightening
the framework's total Millennium position at HEAD.

No `sorry`, no `native_decide`, no `axiom`. Kernel-only.
-/

import PF.Analytic.HilbertPolyaPositiveReductionToCountability
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Bases

open Complex Set Filter Topology
open scoped Real

namespace PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability

/-! ## §1 `ζ` is analytic on `ℂ \ {1}`. -/

/-- **`riemannZeta_analyticOnNhd_ne_one`** — `AnalyticOnNhd ℂ riemannZeta {s | s ≠ 1}`
via `DifferentiableOn.analyticOnNhd` applied to
`differentiableAt_riemannZeta` (mathlib). -/
theorem riemannZeta_analyticOnNhd_ne_one :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-! ## §2 `ζ(2) = π²/6 ≠ 0`, hence ζ is not identically zero. -/

/-- **`riemannZeta_two_ne_zero`** — `ζ(2) = π²/6 ≠ 0`. -/
theorem riemannZeta_two_ne_zero : riemannZeta 2 ≠ 0 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := by
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    exact_mod_cast this
  intro h
  have h6 : (6 : ℂ) ≠ 0 := by norm_num
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · exact hπ (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h)
  · exact h6 h

/-! ## §3 `ℂ \ {1}` is preconnected + open. -/

private lemma isOpen_compl_one_complex : IsOpen ({s : ℂ | s ≠ 1}) := by
  have : ({s : ℂ | s ≠ 1}) = ({(1 : ℂ)}ᶜ) := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [this]; exact isOpen_compl_singleton

private lemma isConnected_compl_one_complex : IsConnected ({s : ℂ | s ≠ 1}) := by
  have h : IsConnected ({(1 : ℂ)}ᶜ) := by
    have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ :=
      rank_real_complex ▸ Nat.one_lt_ofNat
    exact isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)
  have h_eq : ({s : ℂ | s ≠ 1}) = ({(1 : ℂ)}ᶜ) := by
    ext s; simp [Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [h_eq]; exact h

/-! ## §4 ζ-zeros in `ℂ \ {1}` are locally finite. -/

/-- **`riemannZeta_zeros_locally_finite`** — at every `z ∈ ℂ \ {1}`,
there is a neighborhood in which `ζ` has only finitely many zeros. -/
theorem riemannZeta_zeros_locally_finite :
    ∀ z ∈ ({s : ℂ | s ≠ 1}), ∃ t ∈ 𝓝 z,
      Set.Finite (t ∩ ({s : ℂ | s ≠ 1} \ (riemannZeta ⁻¹' {0}ᶜ))) := by
  have h_ana := riemannZeta_analyticOnNhd_ne_one
  have h_ne_zero : riemannZeta 2 ≠ 0 := riemannZeta_two_ne_zero
  have h_two_mem : (2 : ℂ) ∈ ({s : ℂ | s ≠ 1}) := by
    show (2 : ℂ) ≠ 1
    norm_num
  have h_conn : IsConnected ({s : ℂ | s ≠ 1}) := isConnected_compl_one_complex
  have h_codisc : (riemannZeta ⁻¹' {0}ᶜ) ∈ codiscreteWithin ({s : ℂ | s ≠ 1}) :=
    AnalyticOnNhd.preimage_zero_mem_codiscreteWithin h_ana h_ne_zero h_two_mem h_conn
  exact codiscreteWithin_iff_locallyFiniteComplementWithin.mp h_codisc

/-! ## §5 The ζ-zero set on `ℂ \ {1}` is countable. -/

/-- The set of ζ-zeros in `ℂ \ {1}`. -/
private def riemannZetaZeros : Set ℂ := {s : ℂ | s ≠ 1 ∧ riemannZeta s = 0}

/-- **`riemannZetaZeros_countable`** — the zero set of `ζ` in `ℂ \ {1}`
is countable. Via countable cover of `ℂ \ {1}` by neighborhoods each
containing finitely many zeros. -/
theorem riemannZetaZeros_countable : riemannZetaZeros.Countable := by
  -- Assign to each z ∈ ℂ \ {1} a neighborhood `nbhd z` such that
  -- `nbhd z ∩ zero-set` is finite.
  have h_loc := riemannZeta_zeros_locally_finite
  -- Choose nbhd via Classical.choose.
  choose nbhd h_nbhd_mem h_finite using h_loc
  -- Extend nbhd to ALL of ℂ (fallback to ∅ for z = 1).
  set nbhd_ext : ℂ → Set ℂ := fun z =>
    if h : z ∈ ({s : ℂ | s ≠ 1}) then nbhd z h else ∅
  have h_nbhd_ext : ∀ z ∈ ({s : ℂ | s ≠ 1}), nbhd_ext z ∈ 𝓝 z := by
    intro z hz
    simp only [nbhd_ext, dif_pos hz]
    exact h_nbhd_mem z hz
  -- Apply countable_cover_nhdsWithin.
  obtain ⟨T, hT_sub, hT_countable, hT_cover⟩ :=
    TopologicalSpace.countable_cover_nhdsWithin (s := ({s : ℂ | s ≠ 1}))
      (fun z hz => mem_nhdsWithin_of_mem_nhds (h_nbhd_ext z hz))
  -- riemannZetaZeros ⊆ {s | s ≠ 1} ⊆ ⋃ z ∈ T, nbhd_ext z.
  -- riemannZetaZeros ∩ nbhd_ext z is finite for each z ∈ T.
  have h_finite_at_each : ∀ z ∈ T, Set.Finite (riemannZetaZeros ∩ nbhd_ext z) := by
    intro z hz
    have hz1 : z ∈ ({s : ℂ | s ≠ 1}) := hT_sub hz
    simp only [nbhd_ext, dif_pos hz1]
    -- Finite (nbhd z hz1 ∩ ({s | s ≠ 1} \ (ζ ⁻¹' {0}ᶜ))) = Finite of zeros in nbhd.
    have h_fin := h_finite z hz1
    -- Show riemannZetaZeros ∩ nbhd z hz1 ⊆ nbhd z hz1 ∩ ({s | s ≠ 1} \ (ζ ⁻¹' {0}ᶜ)).
    apply h_fin.subset
    intro w hw
    obtain ⟨⟨hw_ne1, hw_zero⟩, hw_nbhd⟩ := hw
    refine ⟨hw_nbhd, hw_ne1, ?_⟩
    -- Need w ∉ ζ ⁻¹' {0}ᶜ.
    simp [Set.mem_preimage, hw_zero]
  -- Cover riemannZetaZeros by countable union of finite sets.
  have h_cover_zeros : riemannZetaZeros ⊆ ⋃ z ∈ T, riemannZetaZeros ∩ nbhd_ext z := by
    intro w hw
    obtain ⟨hw_ne1, hw_zero⟩ := hw
    have hw_in : w ∈ ({s : ℂ | s ≠ 1}) := hw_ne1
    obtain ⟨z, hz, hw_nbhd⟩ := Set.mem_iUnion₂.mp (hT_cover hw_in)
    exact Set.mem_iUnion₂.mpr ⟨z, hz, ⟨hw_ne1, hw_zero⟩, hw_nbhd⟩
  -- Countable union of finites.
  refine Set.Countable.mono h_cover_zeros ?_
  refine hT_countable.biUnion (fun z hz => ?_)
  exact (h_finite_at_each z hz).countable

/-! ## §6 `PositiveOnLineZetaZeroOrdinates` is countable. -/

/-- **`positive_on_line_zeta_zero_ordinates_countable`** — UNCONDITIONAL.
The positive on-line ζ-zero ordinate set is countable. -/
theorem positive_on_line_zeta_zero_ordinates_countable :
    PositiveOnLineZetaZeroOrdinatesCountable := by
  unfold PositiveOnLineZetaZeroOrdinatesCountable PositiveOnLineZetaZeroOrdinates
  -- Show {t : ℝ | 0 < t ∧ ζ ⟨1/2, t⟩ = 0}.Countable.
  -- Embed into riemannZetaZeros via t ↦ ⟨1/2, t⟩.
  set embed : ℝ → ℂ := fun t => ⟨1/2, t⟩ with hembed_def
  have h_inj : Function.Injective embed := by
    intro t₁ t₂ h
    simp only [embed] at h
    exact Complex.ext_iff.mp h |>.2
  -- Image of the positive on-line ordinate set lies in riemannZetaZeros.
  have h_image_sub : embed '' {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0}
      ⊆ riemannZetaZeros := by
    rintro s ⟨t, ⟨ht_pos, ht_zero⟩, hst⟩
    refine ⟨?_, ?_⟩
    · rw [← hst]
      show (⟨1/2, t⟩ : ℂ) ≠ 1
      intro h
      have := (Complex.ext_iff.mp h).1
      norm_num at this
    · rw [← hst]; exact ht_zero
  -- Countable image (subset of countable) → countable source (via injectivity).
  have h_image_countable : (embed '' {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0}).Countable :=
    riemannZetaZeros_countable.mono h_image_sub
  have h_preim_eq :
      embed ⁻¹' (embed '' {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0})
        = {t : ℝ | 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0} :=
    Set.preimage_image_eq _ h_inj
  rw [← h_preim_eq]
  exact h_image_countable.preimage h_inj

/-! ## §7 Axiom check. -/

#print axioms
  PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability.riemannZeta_analyticOnNhd_ne_one
#print axioms
  PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability.riemannZeta_two_ne_zero
#print axioms
  PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability.riemannZetaZeros_countable
#print axioms
  PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability.positive_on_line_zeta_zero_ordinates_countable

end PrincipiaTractalis.PositiveOnLineZetaZeroOrdinatesCountability
