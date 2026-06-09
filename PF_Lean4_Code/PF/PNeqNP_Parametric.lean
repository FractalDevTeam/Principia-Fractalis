/-
# P ≠ NP via the Parametric Substrate (Demonstration of Migration Path)

This file demonstrates how the existing `P_NEQ_NP` proof in
`PF/P_NP_Complete_Proof.lean` can be re-derived using the
`SubstrateAlphaProvider` parametric structure from
`PF/TuringEncoding/AlphaOfClassParametric.lean` instead of the opaque
`alpha_of_class` + `PolylogEigenvalueConjecture` pattern.

## The two formulations side by side

**Existing formulation (opaque-style):**
```lean
theorem P_NEQ_NP (hpoly : PolylogEigenvalueConjecture) : P_neq_NP_def
```
Here `PolylogEigenvalueConjecture` is a Prop that constrains an opaque
`alpha_of_class : Set Language → ℝ` to take values `√2` on `ClassP` and
`φ + 1/4` on `ClassNP`. The proof uses these constraints (extracted
via `alpha_at_ClassP_eq_sqrt2` and `alpha_at_ClassNP_eq_phi_plus_quarter`)
plus arithmetic positivity of the gap.

**Parametric formulation (this file):**
```lean
theorem P_NEQ_NP_param (p : SubstrateAlphaProvider) : P_neq_NP_def
```
Here `SubstrateAlphaProvider` is an explicit structure. The α-values
are derived as theorems (`alpha_P_eq_sqrt2`, `alpha_NP_eq_phi_plus_quarter`).
The same arithmetic positivity argument concludes.

## Why this matters

In the existing chain, `alpha_of_class` is `opaque` — Lean cannot inspect
the function at all. The conjecture pins its values *by external
postulate*. Anyone reading the code must read the conjecture to know
what `alpha_of_class ClassP` is.

In the parametric chain, the substrate's α-providing function is a
structure field, and the constraints are structure invariants. The
α-values are derived theorems, not external postulates. Anyone reading
the code sees, in the theorem signature, that the proof depends on
`SubstrateAlphaProvider` — the substrate's commitment is visible.

## Integration status

This file is NOT imported by `PF.lean`. It is a parallel demonstration
of the migration path. The canonical library's "0 project axioms /
0 sorries / 8360 jobs clean" claim is preserved.
-/

import PF.TuringEncoding.AlphaOfClassParametric
import PF.SpectralGap
import PF.IntervalArithmetic

namespace PrincipiaTractalis

open PrincipiaTractalis.TuringEncoding

/-! ## Parametric spectral gap

    Given a substrate provider, the spectral gap is computable directly:
    `Δ_param p = π/(10·p.alpha ClassP) − π/(10·p.alpha ClassNP)`.
-/

/-- The parametric spectral gap, as a function of the substrate
    provider. Equals the canonical `spectral_gap` because the α-values
    are determined by the substrate's invariants. -/
noncomputable def Δ_param (p : SubstrateAlphaProvider) : ℝ :=
  pi_10 / (p.alpha ClassP) - pi_10 / (p.alpha ClassNP)

/-- The parametric spectral gap equals the canonical (stipulated) one
    because the substrate forces both α-values to their canonical
    forms. -/
theorem Δ_param_eq_spectral_gap (p : SubstrateAlphaProvider) :
    Δ_param p = pi_10 / Real.sqrt 2 - pi_10 / (phi + 1/4) := by
  unfold Δ_param
  rw [SubstrateAlphaProvider.alpha_P_eq_sqrt2 p,
      SubstrateAlphaProvider.alpha_NP_eq_phi_plus_quarter p]

/-- The parametric spectral gap is positive, using `phi_plus_quarter_gt_sqrt2`
    from `IntervalArithmetic`. No `PolylogEigenvalueConjecture` needed;
    the positivity falls out of the substrate's invariants directly. -/
theorem Δ_param_pos (p : SubstrateAlphaProvider) : 0 < Δ_param p := by
  rw [Δ_param_eq_spectral_gap p]
  -- Reduces to: π/(10√2) > π/(10(φ+¼))
  -- Equivalent to: φ + 1/4 > √2 (since both denominators positive and π > 0)
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  have h_pi10_pos : 0 < pi_10 := by unfold pi_10; linarith
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_phi_pos : 0 < phi := by unfold phi; positivity
  have h_phi_plus_pos : 0 < phi + 1/4 := by linarith
  rw [sub_pos]
  apply div_lt_div_of_pos_left h_pi10_pos h_phi_plus_pos
  · positivity
  · exact phi_plus_quarter_gt_sqrt2

/-! ## The parametric P ≠ NP theorem -/

/-- The α-values of the substrate provider are distinct.
    Direct consequence: `p.alpha ClassP = √2` and
    `p.alpha ClassNP = φ + 1/4`, and `√2 < φ + 1/4`. -/
theorem alpha_P_ne_alpha_NP (p : SubstrateAlphaProvider) :
    p.alpha ClassP ≠ p.alpha ClassNP := by
  intro h_eq
  have h_P : p.alpha ClassP = Real.sqrt 2 :=
    SubstrateAlphaProvider.alpha_P_eq_sqrt2 p
  have h_NP : p.alpha ClassNP = phi + 1/4 :=
    SubstrateAlphaProvider.alpha_NP_eq_phi_plus_quarter p
  rw [h_P, h_NP] at h_eq
  -- h_eq : Real.sqrt 2 = phi + 1/4
  -- but phi_plus_quarter_gt_sqrt2 gives the strict inequality
  have h_gt : phi + 1/4 > Real.sqrt 2 := phi_plus_quarter_gt_sqrt2
  linarith

/-- The class-sets `ClassP` and `ClassNP` are distinct, derived from the
    substrate provider's invariants via the same `congrArg alpha_of_class`
    pattern as the existing chain — but now with a non-opaque,
    parameterized α-function. -/
theorem ClassP_ne_ClassNP_param (p : SubstrateAlphaProvider) :
    ClassP ≠ ClassNP := by
  intro h_eq
  -- If the sets are equal, then their α-values are equal (congrArg)
  have h_alpha_eq : p.alpha ClassP = p.alpha ClassNP := by
    rw [h_eq]
  -- But we just proved they are distinct
  exact alpha_P_ne_alpha_NP p h_alpha_eq

/-- The parametric `P ≠ NP` theorem. Given a `SubstrateAlphaProvider`
    (the substrate's α-axiom in explicit form), `P_neq_NP_def` holds.

    This is the migration target of the existing
    `P_NEQ_NP : PolylogEigenvalueConjecture → P_neq_NP_def`.

    **Note**: this theorem inherits all the same caveats as the existing
    one. It is a conditional reduction: `P ≠ NP` follows from the
    substrate's axiom (now packaged as a structure rather than an
    opaque-plus-conjecture). It does NOT discharge `P ≠ NP`
    unconditionally — that would require discharging the substrate's
    axiom itself, which is at least as hard as `P ≠ NP`.

    What this theorem **does** do is make the dependency on the
    substrate's α-axiom **explicit and inspectable** in the theorem
    signature, rather than hidden behind an opaque declaration. -/
theorem P_NEQ_NP_param (p : SubstrateAlphaProvider) :
    P_neq_NP_def := by
  unfold P_neq_NP_def
  intro h_p_eq_np
  -- h_p_eq_np : ∀ L, InClassNP L → InClassP L
  -- This + InClassP ⊆ InClassNP (P_subset_NP) gives ClassP = ClassNP
  have h_NP_subset_P : ClassNP ⊆ ClassP := h_p_eq_np
  have h_classes_eq : ClassP = ClassNP :=
    Set.Subset.antisymm P_subset_NP h_NP_subset_P
  -- But we proved ClassP ≠ ClassNP from the substrate's invariants
  exact ClassP_ne_ClassNP_param p h_classes_eq

/-! ## Summary of the migration

    The existing chain:
      opaque alpha_of_class : Set Language → ℝ
      PolylogEigenvalueConjecture : Prop (constrains values)
      P_NEQ_NP : PolylogEigenvalueConjecture → P_neq_NP_def

    The parametric chain:
      structure SubstrateAlphaProvider where alpha + invariants
      P_NEQ_NP_param : SubstrateAlphaProvider → P_neq_NP_def

    Both are conditional reductions of the same strength. The
    parametric version makes the substrate's α-axiom visible in
    every theorem signature; the opaque version hides it behind a
    declaration that downstream consumers might not inspect.

    Migration step (future): retire the opaque declaration and route
    all P ≠ NP consumers through `SubstrateAlphaProvider`. -/

end PrincipiaTractalis
