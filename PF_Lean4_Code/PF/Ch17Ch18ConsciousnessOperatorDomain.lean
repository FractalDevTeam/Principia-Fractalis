/-
# Ch 17 / Ch 18 — The Consciousness Operator Has Two Domains, One of Them Empty
(2026-10-05)

## The defect

`ch17_operator_theory.tex` defines the symbol `C` **twice**, 177 lines apart,
over **different domains**, and never reconciles them:

* `ch17:269`, inside the theorem that defines `I_C = Tr(ρ · C)`:

    `C = ∫_{Spec(T_∞)} ch₂(s) dE(s)`

* `ch17:446–453`, the **boxed** definition:

    `C = ∫_{ℜ(s)=1/2} ch₂(s) |s⟩⟨s| ds/2π`

The first integrates over the Gelfand character space of the substrate; the
second over the critical line. These are not the same set and the chapter does
not say which is meant.

`ch18_spectral_measures.tex:121` then opens its measurement theory with
"Recall the consciousness operator from Chapter 17" and uses **the first form**:

    `C = ∫_{Spec(T_∞)} ch₂(s) dE_C(s)`

## Why that matters: the first domain is empty, and the book proves it

`ch16_spectral_foundations.tex:623–637` already carries the proof, in the
chapter's own words, that `Spec(T_∞) = ∅` for the substrate: the kernel of a
nonzero multiplicative functional `φ : T_∞ → ℂ` is a two-sided ideal of
codimension 1; simplicity forces it to be `0` or everything; `φ ≠ 0` rules out
the second; so `T_∞ ≅ ℂ`, contradicting infinite-dimensionality. Machine-checked
as `gelfandSpectrum_eq_empty` in `PF/SubstrateNotCommutative_r217.lean`.

An integral over the empty set is zero (`integral_over_empty_is_zero`).
Therefore, under the form `ch18` actually uses:

* `C = 0`;
* `I_C = Tr(ρ · C) = 0` for **every** state `ρ` (`infoMeasure_vanishes`), so the
  consciousness measure is identically zero rather than state-dependent;
* `‖C‖ = 0`, which contradicts item 3 of `thm:consciousness-operator-properties`
  (`ch17:466`), "**Unbounded**: `‖C‖ = ∞`" — `zero_norm_incompatible_with_unbounded`;
* item 4 of the same theorem (`ch17:467`), "Trace class on finite regions:
  `Tr_Λ(C) < ∞` for compact `Λ ⊂ Spec(T_∞)`", **quantifies over subsets of the
  empty set** and so has no content: the only such `Λ` is `∅` itself
  (`item_four_is_vacuous`). It is true, and it says nothing.

## This was already known one chapter over, and never backported

`ch34A_substrate_theorem.tex:2372–2382` states the consequence outright — "the
character space of the substrate is empty (`gelfandSpectrum_eq_empty`), so any
consciousness operator defined as an integral over `Spec(T_∞)` is the zero
operator." Neither ch17's verification ledger (`:650–657`) nor ch18's
(`:665–671`) mentions it. So the finding here is not the fact; it is that the
fact never reached the two chapters that depend on it most.

## What is NOT claimed

**`C` is not being declared zero outright.** The boxed definition at `ch17:446`
integrates over the critical line, which is not empty, so under *that* reading
`C` need not vanish. The defect is that the chapter carries both definitions and
`ch18` picks the one with the empty domain. Which is intended is an authorial
decision and this file takes no position on it.

Note also that the critical-line reading is itself not yet well-posed: `|s⟩` is
described only as "eigenstates of the 'location on critical line' operator",
which the chapter never defines; and for a continuous spectrum `|s⟩⟨s|` is a
density rather than a projection, so asserting trace-class and unbounded needs
a direct-integral or rigged-Hilbert-space setting that is not supplied. Those
are gaps, not contradictions, and they are recorded rather than formalized.

A third item is worth flagging for whoever repairs this: item 2 of the same
theorem asserts positivity, `⟨ψ|C|ψ⟩ ≥ 0`. Under either reading that needs
`ch₂(s) ≥ 0` along the domain, and the book's only computable formula for `ch₂`
takes values in `[−1/2, 1/2]` (`ch2Matrix_le_half` and
`neg_half_le_ch2Matrix_of_trace_eq_zero` in
`PF/Cosmology/VortexCavitationBridgeChecks.lean`), so positivity is an
additional hypothesis rather than a consequence.

## What a repair must establish

1. **Which domain `C` integrates over.** If `Spec(T_∞)`, then `C = 0` and
   ch18's measurement theory — the PVM `E_C`, its outcomes, state collapse, and
   decoherence suppression — is about the zero operator. If the critical line,
   then `ch17:269` and `ch18:121` must be corrected to match the boxed
   definition and stop naming `Spec(T_∞)`.
2. **The missing operator.** For the critical-line reading, the "location on
   critical line" operator must be defined, with its Hilbert space, domain, and
   the measure on `{ℜ(s) = 1/2}`.
3. **Positivity and boundedness as hypotheses**, not conclusions, unless derived
   from a stated range for `ch₂` on that domain.

## Scope

The domain of one operator and the four properties asserted of it. Nothing here
bears on the Riemann Hypothesis, and no rigor-ledger label outside ch17's
consciousness-operator section and ch18's measurement section moves.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch17Ch18OperatorDomain

open MeasureTheory

/-! ## §1 — An integral over the empty domain is zero -/

/-- **An integral over the empty set vanishes.**

    This is the whole mechanism. `ch18:121` integrates `ch₂` over
    `Spec(T_∞)`, which `ch16:623–637` proves empty and
    `gelfandSpectrum_eq_empty` certifies. -/
theorem integral_over_empty_is_zero
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    ∫ x in (∅ : Set α), f x ∂μ = 0 := by
  simp

/-- The same statement for a complex-valued integrand, which is the case the
    chapters actually use. -/
theorem integral_over_empty_is_zero_complex
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x in (∅ : Set α), f x ∂μ = 0 := by
  simp

/-! ## §2 — Consequences for the asserted properties -/

/-- **`‖C‖ = 0` contradicts "Unbounded: `‖C‖ = ∞`".**

    Stated in `ℝ≥0∞`, where `∞` is an actual element, so the incompatibility is
    a statement about values rather than about notation. -/
theorem zero_norm_incompatible_with_unbounded :
    (0 : ENNReal) ≠ ⊤ := by simp

/-- Stated as the conjunction the chapter asserts, which cannot hold. -/
theorem norm_cannot_be_both (n : ENNReal) : ¬ (n = 0 ∧ n = ⊤) := by
  rintro ⟨h0, htop⟩
  rw [h0] at htop
  exact zero_norm_incompatible_with_unbounded htop

/-- **The information measure vanishes identically.**

    `ch17:265` boxes `I_C = Tr(ρ · C)`. With `C = 0` this is `0` for every
    state `ρ`, so the quantity is not state-dependent at all. Stated for
    matrices, which is the finite-dimensional shadow of the claim. -/
theorem infoMeasure_vanishes {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) :
    (rho * (0 : Matrix n n ℂ)).trace = 0 := by
  simp

/-- **Item 4 quantifies over subsets of the empty set, so it is vacuous.**

    "`Tr_Λ(C) < ∞` for compact `Λ ⊂ Spec(T_∞)`" ranges over a family with one
    member, `∅`. The statement is true and carries no information. -/
theorem item_four_is_vacuous {α : Type*} (Λ : Set α) (h : Λ ⊆ (∅ : Set α)) :
    Λ = ∅ := Set.subset_empty_iff.mp h

/-- Any predicate whatsoever holds of every subset of the empty set once it
    holds of `∅` — the precise sense in which item 4 says nothing. -/
theorem any_predicate_holds_vacuously {α : Type*} (P : Set α → Prop)
    (hP : P ∅) : ∀ Λ : Set α, Λ ⊆ (∅ : Set α) → P Λ := by
  intro Λ hΛ
  rw [Set.subset_empty_iff.mp hΛ]
  exact hP

/-! ## §3 — The two domains are not interchangeable -/

/-- **Two integrals over different domains need not agree**, so carrying both
    definitions of `C` is not a harmless notational variant.

    Witnessed concretely: over `∅` the integral is `0`, while over a set of
    positive measure a positive integrand gives a positive value. -/
theorem different_domains_give_different_integrals :
    ∫ _x in (∅ : Set ℝ), (1 : ℝ) ∂(volume) = 0 ∧
    ∫ _x in (Set.Icc (0:ℝ) 1), (1 : ℝ) ∂(volume) = 1 := by
  refine ⟨by simp, ?_⟩
  simp [Real.volume_Icc]

/-! ## §4 — Capstone -/

/-- **★ Ch 17 / Ch 18 consciousness-operator domain capstone ★**

    An integral over the empty domain is zero; a zero norm cannot also be
    infinite; the information measure then vanishes for every state; item 4's
    quantification over subsets of `∅` is vacuous; and the two domains the
    chapter carries are not interchangeable. -/
theorem Ch17Ch18OperatorDomain_capstone :
    (∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ),
      ∫ x in (∅ : Set α), f x ∂μ = 0) ∧
    (∀ n : ENNReal, ¬ (n = 0 ∧ n = ⊤)) ∧
    (∀ {α : Type*} (Λ : Set α), Λ ⊆ (∅ : Set α) → Λ = ∅) :=
  ⟨fun μ f => integral_over_empty_is_zero μ f,
   norm_cannot_be_both,
   fun Λ h => item_four_is_vacuous Λ h⟩

/-! ## §5 — Non-vacuity -/

/-- Non-vacuity, and it is the pointed kind here: the critical-line domain is
    NOT empty, so the defect is a choice of domain rather than an impossibility.
    `1/2 + i` lies on `ℜ(s) = 1/2`, witnessing that the boxed definition at
    `ch17:446` has a nonempty domain to integrate over. -/
theorem critical_line_is_nonempty :
    ((1 : ℂ) / 2 + Complex.I).re = 1 / 2 := by
  simp

end PrincipiaTractalis.Ch17Ch18OperatorDomain

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.integral_over_empty_is_zero
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.integral_over_empty_is_zero_complex
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.zero_norm_incompatible_with_unbounded
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.norm_cannot_be_both
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.infoMeasure_vanishes
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.item_four_is_vacuous
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.any_predicate_holds_vacuously
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.different_domains_give_different_integrals
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.Ch17Ch18OperatorDomain_capstone
#print axioms PrincipiaTractalis.Ch17Ch18OperatorDomain.critical_line_is_nonempty
