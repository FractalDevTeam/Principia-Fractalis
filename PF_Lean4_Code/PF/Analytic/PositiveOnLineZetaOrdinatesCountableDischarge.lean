/-
# PF.Analytic.PositiveOnLineZetaOrdinatesCountableDischarge

★★★★★ 2026-06-18 — Wave 59 RH brick: UNCONDITIONAL DISCHARGE of the
Wave 58 atomic fact `PositiveOnLineZetaZeroOrdinatesCountable` from
mathlib's analytic identity theorem applied to `riemannZeta`.

## Goal

Wave 58 reduced the framework's HP-positive RH residual to two atomic
facts:

  (a) `PositiveOnLineZetaZeroOrdinatesCountable`
  (b) `PositiveOnLineZetaZeroOrdinatesNonempty`

This file discharges (a) UNCONDITIONALLY using:

  - `differentiableAt_riemannZeta` (ζ differentiable away from `s = 1`)
  - `DifferentiableOn.analyticOnNhd` (complex-differentiable ⇒ analytic)
  - `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`
  - `riemannZeta_zero : riemannZeta 0 = -1/2` (so ζ ≢ 0 on ℂ \ {1})
  - `isPathConnected_compl_singleton_of_one_lt_rank` (ℂ \ {1} preconnected)
  - `discreteTopology_of_codiscreteWithin` (codiscrete ⇒ discrete subspace)
  - `IsLindelof.countable` for discrete Lindelöf subspace of ℂ (second-
    countable ⇒ hereditarily Lindelöf ⇒ subspace Lindelöf)

## Brick value

After this brick the framework's HP-positive RH residual reduces to a
SINGLE remaining atomic fact: `PositiveOnLineZetaZeroOrdinatesNonempty`
(Hardy 1914 in the published literature).

## Axiom budget

Zero project axioms, zero sorries. Theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.Analytic.HilbertPolyaPositiveReductionToCountability
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Compactness.Lindelof

namespace PrincipiaTractalis.PositiveOnLineZetaOrdinatesCountableDischarge

open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HilbertPolyaPositiveImageRigidity
open PrincipiaTractalis.HilbertPolyaPositiveReductionToCountability
open Complex Filter Topology Set

/-! ## §1 — The natural analytic domain `U = ℂ \ {1}` -/

/-- `U` is the natural analytic domain of `riemannZeta`. -/
def U : Set ℂ := {(1 : ℂ)}ᶜ

theorem U_isOpen : IsOpen U :=
  isOpen_compl_iff.mpr isClosed_singleton

theorem zero_mem_U : (0 : ℂ) ∈ U := by
  simp [U]

/-! ## §2 — ζ is analytic on `U` -/

theorem riemannZeta_differentiableOn_U : DifferentiableOn ℂ riemannZeta U :=
  fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt

theorem riemannZeta_analyticOnNhd_U : AnalyticOnNhd ℂ riemannZeta U :=
  riemannZeta_differentiableOn_U.analyticOnNhd U_isOpen

/-! ## §3 — `U = ℂ \ {1}` is preconnected -/

theorem U_isPreconnected : IsPreconnected U := by
  have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  exact (isPathConnected_compl_singleton_of_one_lt_rank h_rank
    (1 : ℂ)).isConnected.isPreconnected

/-! ## §4 — ζ is not identically zero on `U` (since `ζ(0) = -1/2`) -/

theorem riemannZeta_not_eqOn_zero : ¬ Set.EqOn riemannZeta 0 U := by
  intro h_eq
  have h_val : riemannZeta (0 : ℂ) = 0 := h_eq zero_mem_U
  rw [riemannZeta_zero] at h_val
  norm_num at h_val

/-! ## §5 — The non-zero set is codiscrete within `U` -/

theorem riemannZeta_nonzero_codiscreteWithin :
    {x : ℂ | riemannZeta x ≠ 0} ∈ Filter.codiscreteWithin U := by
  have h_alt := riemannZeta_analyticOnNhd_U.eqOn_zero_or_eventually_ne_zero_of_preconnected
    U_isPreconnected
  exact h_alt.resolve_left riemannZeta_not_eqOn_zero

/-! ## §6 — The zero set of ζ inside `U` has discrete topology -/

/-- The zero set of `riemannZeta` restricted to `U = ℂ \ {1}`. -/
def ZetaZeroSetU : Set ℂ := {x | riemannZeta x ≠ 0}ᶜ ∩ U

theorem ZetaZeroSetU_discreteTopology : DiscreteTopology (ZetaZeroSetU : Set ℂ) :=
  discreteTopology_of_codiscreteWithin riemannZeta_nonzero_codiscreteWithin

/-! ## §7 — Countability of the zero set inside `U`

    ℂ is second-countable ⇒ hereditarily Lindelöf ⇒ every subspace is
    LindelöfSpace. Combined with discrete topology on `ZetaZeroSetU`,
    Lindelöf-discrete ⇒ countable. -/

theorem ZetaZeroSetU_lindelofSpace : LindelofSpace (ZetaZeroSetU : Set ℂ) :=
  HereditarilyLindelof.lindelofSpace_subtype (· ∈ ZetaZeroSetU)

theorem ZetaZeroSetU_isLindelof : IsLindelof (ZetaZeroSetU : Set ℂ) :=
  isLindelof_iff_LindelofSpace.mpr ZetaZeroSetU_lindelofSpace

theorem ZetaZeroSetU_countable : (ZetaZeroSetU : Set ℂ).Countable :=
  ZetaZeroSetU_isLindelof.countable ZetaZeroSetU_discreteTopology

/-! ## §8 — Inject `PositiveOnLineZetaZeroOrdinates` into the zero set in `U` -/

/-- The embedding `t ↦ ⟨1/2, t⟩ : ℝ → ℂ` lands in `U` for every `t`. -/
theorem critical_line_in_U (t : ℝ) : (⟨1/2, t⟩ : ℂ) ∈ U := by
  simp only [U, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Every element of `PositiveOnLineZetaZeroOrdinates` lifts (via
    `t ↦ ⟨1/2, t⟩`) into `ZetaZeroSetU`. -/
theorem positive_ordinates_lift_to_ZetaZeroSetU
    (t : ℝ) (ht : t ∈ PositiveOnLineZetaZeroOrdinates) :
    (⟨1/2, t⟩ : ℂ) ∈ ZetaZeroSetU := by
  refine ⟨?_, critical_line_in_U t⟩
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  exact ht.2

/-! ## §9 — UNCONDITIONAL countability discharge -/

/-- **★★★★★ (W59) `PositiveOnLineZetaZeroOrdinatesCountable` is
    UNCONDITIONALLY TRUE ★★★★★** — the atomic fact reduces to
    countability of the zero set of `riemannZeta` inside `U = ℂ \ {1}`,
    which follows from the analytic identity theorem.

    Proof: the map `t ↦ ⟨1/2, t⟩ : ℝ → ℂ` is injective and embeds
    `PositiveOnLineZetaZeroOrdinates` into the countable set `ZetaZeroSetU`.
    Hence the source is countable. -/
theorem positive_on_line_zeta_zero_ordinates_countable_discharged :
    PositiveOnLineZetaZeroOrdinatesCountable := by
  unfold PositiveOnLineZetaZeroOrdinatesCountable
  let ψ : ℝ → ℂ := fun t => ⟨1/2, t⟩
  have ψ_inj : Function.Injective ψ := by
    intro a b hab
    have := congrArg Complex.im hab
    simpa [ψ] using this
  have h_image_subset : ψ '' PositiveOnLineZetaZeroOrdinates ⊆ ZetaZeroSetU := by
    rintro _ ⟨t, ht, rfl⟩
    exact positive_ordinates_lift_to_ZetaZeroSetU t ht
  have h_image_countable : (ψ '' PositiveOnLineZetaZeroOrdinates).Countable :=
    ZetaZeroSetU_countable.mono h_image_subset
  -- Pull image-countability back through injection
  have h_eq : PositiveOnLineZetaZeroOrdinates =
      ψ ⁻¹' (ψ '' PositiveOnLineZetaZeroOrdinates) :=
    (Set.preimage_image_eq PositiveOnLineZetaZeroOrdinates ψ_inj).symm
  rw [h_eq]
  exact h_image_countable.preimage ψ_inj

/-! ## §10 — Wave 59 capstone -/

/-- **★★★★★★ (W59) HP-POSITIVE RH RESIDUAL NARROWED TO ONE
    ATOMIC FACT ★★★★★★** — combining W58's reduction to (countable ∧
    nonempty) with W59's unconditional discharge of countability, the
    framework's HP-positive RH residual reduces to a SINGLE atomic
    fact: `PositiveOnLineZetaZeroOrdinatesNonempty`.

    `PF_T3SymIsHilbertPolyaOperator_Positive`
       ↔ `PositiveOnLineZetaZeroOrdinatesNonempty`. -/
theorem rh_wave59_one_fact_capstone :
    PF_T3SymIsHilbertPolyaOperator_Positive ↔
    PositiveOnLineZetaZeroOrdinatesNonempty := by
  constructor
  · intro h
    exact (hp_positive_iff_countable_nonempty.mp h).2
  · intro h_ne
    exact hp_positive_iff_countable_nonempty.mpr
      ⟨positive_on_line_zeta_zero_ordinates_countable_discharged, h_ne⟩

end PrincipiaTractalis.PositiveOnLineZetaOrdinatesCountableDischarge

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.PositiveOnLineZetaOrdinatesCountableDischarge.ZetaZeroSetU_countable
#print axioms PrincipiaTractalis.PositiveOnLineZetaOrdinatesCountableDischarge.positive_on_line_zeta_zero_ordinates_countable_discharged
#print axioms PrincipiaTractalis.PositiveOnLineZetaOrdinatesCountableDischarge.rh_wave59_one_fact_capstone
