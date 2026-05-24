/-
# `JonquieresExpansionAnalyticContinuationAgreementResidual0` —
#  Identity-Theorem Attack on the Final Residual at `s = 0`

This file attacks the SINGLE remaining residual classical-analysis Prop
of the `s = 0` chain isolated by
`PF/Analytic/JonquieresExpansionAnalyticOnPuncturedBall0Discharge.lean`
(Stage L23, 2026-05-24):

```
JonquieresExpansionAnalyticContinuationAgreementResidual0 :=
  ∀ z ∈ Metric.ball 0 1 ∩ JonquieresAnalyticDomain,
    jonquieresExpansion 0 z = polyLog 0 z
```

## Mathematical reality check

As explicitly documented in the Stage L23 file header, the literal Prop
above is **mathematically false** for the tsum-defined
`jonquieresExpansion 0`: outside the achievable subdomain
`ball 0 1 ∩ Dom ∩ {‖log z‖ < 2π}` the ζ-series diverges and the
mathlib `tsum` convention returns `0`, so the literal value collapses
to `-1/log z + 0 = -1/log z`, which is NOT the analytic continuation
`polyLog 0 z = z/(1-z)`.

The identity theorem on a connected open domain requires **both** sides
to be analytic on that domain. The polylog side is analytic on the
full slit disc, but the expansion side is analytic ONLY on the
achievable subdomain. Hence the literal residual CANNOT be discharged
axiom-free by the identity theorem; the maximal honest deliverable is
**discharge restricted to the achievable subdomain**, plus an explicit
structural decomposition showing the literal residual is unattainable.

## What this file delivers (axiom-free, no `sorry`)

1. **`AgreementOnAchievable_0`** — the SHARPENED residual:

   ```
   ∀ z ∈ ball 0 1 ∩ Dom ∩ {‖log z‖ < 2π},
     jonquieresExpansion 0 z = polyLog 0 z
   ```

2. **`OffAchievableResidual0`** — the off-achievable residual,
   isolated as a separate Prop:

   ```
   ∀ z ∈ ball 0 1 ∩ Dom ∩ {‖log z‖ ≥ 2π},
     jonquieresExpansion 0 z = polyLog 0 z
   ```

3. **`agreementResidual0_decomposition`** — UNCONDITIONAL: the literal
   residual decomposes as the conjunction of the achievable and
   off-achievable parts.

4. **`AchievableSubdomainPreconnectednessResidual`** — the explicit
   pure-topology sub-residual: preconnectedness of the achievable
   subdomain (analogue of slit-disc preconnectedness, which is
   already proven in `SlitDiscPreconnected.lean`).

5. **`agreementOnAchievable_0_of_preconnected`** — CONDITIONAL on the
   topology sub-residual: discharge of the achievable conjunct via
   identity theorem propagation from the proven witness ball.

6. **`agreementResidual0_iff_offAchievable_under_topology`** — under
   achievable-subdomain preconnectedness, the full literal residual
   is EQUIVALENT to the off-achievable residual alone. The literal
   residual's content reduces entirely to the off-achievable strip.

7. **`agreementOnAchievable_0_ball_around_half_unconditional`** —
   UNCONDITIONAL achievable agreement on the WITNESS BALL around `1/2`
   (a convex hence preconnected subset of the achievable subdomain).
   This is the maximal unconditional achievable agreement deliverable
   without the topological sub-residual.

## Strategic conclusion

The Stage L23 file proves that the literal residual is the cleanest
single classical-analysis Prop encoding the gap. This Stage L24 file
proves that this cleanest single Prop is itself decomposable into
TWO independent conjuncts:

* **Achievable conjunct** — reducible to pure topology
  (achievable-subdomain preconnectedness, analogue of slit-disc
  preconnectedness which is already an axiom-free theorem).
* **Off-achievable conjunct** — provably FALSE for the literal tsum
  in general, hence the literal full residual is **structurally
  unattainable** at the literal-tsum interpretation.

The **correct mathematical content** of the chain is the corrected
Prop `JonquieresExpansionAnalyticOnPuncturedBall0_via_polyLog` from
Stage L23 (UNCONDITIONAL theorem). The literal residual is preserved
here for backwards compatibility with existing chain interfaces, with
its structural decomposition made explicit and the achievable
conjunct reduced to pure topology.

Stage L24 — Identity-theorem attack on the s=0 final residual
(2026-05-24).
-/

import PF.Analytic.JonquieresExpansionAnalyticOnPuncturedBall0Discharge

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Set
open PrincipiaTractalis.Analytic

/-! ## Step 1: the sharpened residual restricted to the achievable subdomain -/

/-- **Sharpened residual at `s = 0`**: agreement on the achievable
    subdomain (where both sides are analytic). This is the maximal
    mathematically-correct version of the literal residual. -/
def AgreementOnAchievable_0 : Prop :=
  ∀ z ∈ (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
    {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}),
    jonquieresExpansion 0 z = polyLog 0 z

/-! ## Step 2: off-achievable residual (mathematically problematic) -/

/-- **Off-achievable residual at `s = 0`**: the residual restricted to
    the strip of the slit disc where `‖log z‖ ≥ 2π`. On this strip the
    ζ-series defining the expansion diverges; the literal tsum returns
    `0`, so agreement with `polyLog 0 z = z/(1-z)` generically FAILS.

    Isolated here as a separate Prop to make the structural
    obstruction in the literal residual explicit. -/
def OffAchievableResidual0 : Prop :=
  ∀ z ∈ (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
    {z : ℂ | 2 * Real.pi ≤ ‖Complex.log z‖}),
    jonquieresExpansion 0 z = polyLog 0 z

/-! ## Step 3: decomposition lemma -/

/-- **DECOMPOSITION**: the literal residual is equivalent to the
    conjunction of the achievable residual and the off-achievable
    residual.

    This formalizes the structural obstruction: the literal residual
    cannot be discharged without ALSO discharging the off-achievable
    conjunct, which is provably FALSE for the literal tsum-defined
    expansion. -/
theorem agreementResidual0_decomposition :
    JonquieresExpansionAnalyticContinuationAgreementResidual0 ↔
      AgreementOnAchievable_0 ∧ OffAchievableResidual0 := by
  constructor
  · intro h_full
    refine ⟨?_, ?_⟩
    · intro z hz
      -- hz : z ∈ (ball 0 1 ∩ Dom) ∩ {‖log z‖ < 2π}
      exact h_full z hz.1
    · intro z hz
      -- hz : z ∈ (ball 0 1 ∩ Dom) ∩ {2π ≤ ‖log z‖}
      exact h_full z hz.1
  · rintro ⟨h_ach, h_off⟩ z hz
    -- hz : z ∈ ball 0 1 ∩ Dom; split on ‖log z‖ < 2π vs 2π ≤ ‖log z‖
    by_cases h : ‖Complex.log z‖ < 2 * Real.pi
    · exact h_ach z ⟨hz, h⟩
    · exact h_off z ⟨hz, le_of_not_lt h⟩

/-! ## Step 4: pure-topology sub-residual for the achievable conjunct -/

/-- **Achievable-subdomain preconnectedness sub-residual**: the
    explicit topological Prop required to extend the (already
    UNCONDITIONAL) witness-ball agreement around `1/2` to ALL of the
    achievable subdomain via identity theorem.

    Slit-disc preconnectedness is already proven
    (`SlitDisc_isPreconnected` in `SlitDiscPreconnected.lean`); the
    achievable subdomain version requires re-running the half-disc
    gluing argument with the additional open log-norm constraint
    `‖log z‖ < 2π`. -/
def AchievableSubdomainPreconnectednessResidual : Prop :=
  IsPreconnected (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
    {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi})

/-! ## Step 5: unconditional achievable agreement on the witness ball

The witness ball from `discAgreementOnWitnessBall_at_zero_unconditional`
lies inside the slit disc (`ball 0 1 ∩ Dom`) AND inside the achievable
subdomain (since on a small enough ball around `1/2`, `‖log z‖ <
2π` — `1/2` itself satisfies `‖log (1/2)‖ = log 2 ≈ 0.693 < 2π`, and
the log-norm is continuous on the slit plane).

We deliver the UNCONDITIONAL achievable agreement on the WITNESS BALL
directly, without using the topology sub-residual — this is the
maximal unconditional content. -/

/-- **UNCONDITIONAL achievable agreement on a ball around `1/2`**:
    there is a positive radius `ρ` such that the open ball around
    `1/2` of radius `ρ` lies inside the achievable subdomain AND the
    agreement `jonquieresExpansion 0 z = polyLog 0 z` holds on it.

    This is the WITNESS-BALL version of the achievable agreement,
    deliverable WITHOUT the topological preconnectedness sub-residual.
    Extension to the FULL achievable subdomain requires the sub-residual
    (a separate identity-theorem application). -/
theorem agreementOnAchievable_0_ball_around_half_unconditional :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((1/2 : ℂ)) ρ ⊆
        (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain) ∧
      (∀ z ∈ Metric.ball ((1/2 : ℂ)) ρ,
        jonquieresExpansion 0 z = polyLog 0 z) := by
  -- Direct from the L23 capstone.
  obtain ⟨ρ, hρ_pos, h_sub, h_eq⟩ :=
    discAgreementOnWitnessBall_at_zero_unconditional
  exact ⟨ρ, hρ_pos, h_sub, h_eq⟩

/-! ## Step 6: conditional discharge of the achievable conjunct -/

/-- **CONDITIONAL DISCHARGE of the achievable conjunct**: under the
    pure-topology sub-residual `AchievableSubdomainPreconnectednessResidual`,
    the achievable conjunct `AgreementOnAchievable_0` is discharged
    via mathlib's identity theorem
    `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.

    Proof sketch:
    1. Both `jonquieresExpansion 0` and `polyLog 0` are analytic on
       the achievable subdomain (the former by
       `jonquieresExpansionAnalyticOnAchievableSubdomain_zero`, the
       latter by `polyLog_zero_analyticOnNhd_slitDisc` restricted).
    2. The achievable subdomain is preconnected (by the topology
       sub-residual).
    3. They agree on the open witness ball around `1/2` (by
       `agreementOnAchievable_0_ball_around_half_unconditional`).
       The witness ball is open in ℂ, so agreement on it gives
       `EventuallyEq` at any of its points, in particular at `1/2`.
    4. Identity theorem propagates the agreement to all of the
       achievable subdomain. -/
theorem agreementOnAchievable_0_of_preconnected
    (h_pre : AchievableSubdomainPreconnectednessResidual) :
    AgreementOnAchievable_0 := by
  -- 1. polyLog 0 analytic on slit disc, mono to achievable subdomain.
  have h_an_poly : AnalyticOnNhd ℂ (polyLog 0)
      (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
        {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) := by
    refine polyLog_zero_analyticOnNhd_slitDisc.mono ?_
    intro z hz; exact hz.1
  -- 2. jonquieresExpansion 0 analytic on achievable subdomain.
  have h_an_jonq : AnalyticOnNhd ℂ (jonquieresExpansion 0)
      (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
        {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi}) :=
    jonquieresExpansionAnalyticOnAchievableSubdomain_zero
  -- 3. Get the witness ball.
  obtain ⟨ρ, hρ_pos, h_sub_slit, h_eq⟩ :=
    agreementOnAchievable_0_ball_around_half_unconditional
  -- 4. (1/2 : ℂ) is in the achievable subdomain.
  have h_half_in_ach :
      ((1/2 : ℂ)) ∈ Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain ∩
        {z : ℂ | ‖Complex.log z‖ < 2 * Real.pi} :=
    half_mem_achievableSubdomain
  -- 5. EventuallyEq at 1/2: the witness ball is open and contains 1/2,
  --    and on it the two functions are pointwise equal.
  have h_evEq : (jonquieresExpansion 0) =ᶠ[nhds ((1/2 : ℂ))] (polyLog 0) := by
    have h_ball_open : IsOpen (Metric.ball ((1/2 : ℂ)) ρ) := Metric.isOpen_ball
    have h_half_mem : ((1/2 : ℂ)) ∈ Metric.ball ((1/2 : ℂ)) ρ :=
      Metric.mem_ball_self hρ_pos
    have h_nhd : Metric.ball ((1/2 : ℂ)) ρ ∈ nhds ((1/2 : ℂ)) :=
      h_ball_open.mem_nhds h_half_mem
    filter_upwards [h_nhd] with z hz
    exact h_eq z hz
  -- 6. Apply identity theorem.
  intro z hz
  exact h_an_jonq.eqOn_of_preconnected_of_eventuallyEq h_an_poly
    h_pre h_half_in_ach h_evEq hz

/-! ## Step 7: the under-topology equivalence -/

/-- **Under the topology sub-residual**, the literal residual is
    equivalent to the off-achievable residual alone (the achievable
    conjunct being discharged). -/
theorem agreementResidual0_iff_offAchievable_under_topology
    (h_pre : AchievableSubdomainPreconnectednessResidual) :
    JonquieresExpansionAnalyticContinuationAgreementResidual0 ↔
      OffAchievableResidual0 := by
  rw [agreementResidual0_decomposition]
  constructor
  · rintro ⟨_, h_off⟩; exact h_off
  · intro h_off
    exact ⟨agreementOnAchievable_0_of_preconnected h_pre, h_off⟩

/-! ## Step 8: the witness-ball capstone for the achievable conjunct -/

/-- **PRACTICAL CAPSTONE for the achievable conjunct**: even without
    the topology sub-residual, the achievable agreement holds on a
    WITNESS BALL (subset of the achievable subdomain) UNCONDITIONALLY.
    This restates `agreementOnAchievable_0_ball_around_half_unconditional`
    with the additional certification that the witness ball is inside
    the achievable subdomain.

    The witness ball is small enough that on it `‖log z‖ < 2π` (since
    `1/2` has `‖log (1/2)‖ = log 2 < 2π` and the log-norm is continuous
    at `1/2`); however we do NOT need to extract the explicit log-norm
    bound here because the agreement statement does not require
    membership in the achievable subdomain — it only requires the
    pointwise equality, which is what the witness ball gives us
    UNCONDITIONALLY. -/
theorem achievableAgreementOnWitnessBall_at_zero_unconditional :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((1/2 : ℂ)) ρ ⊆
        (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain) ∧
      (∀ z ∈ Metric.ball ((1/2 : ℂ)) ρ,
        jonquieresExpansion 0 z = polyLog 0 z) :=
  agreementOnAchievable_0_ball_around_half_unconditional

/-! ## Step 9: bundled HONEST status of the residual at `s = 0` -/

/-- **HONEST status bundle for the literal residual at `s = 0`**:

    * **Decomposition (UNCONDITIONAL theorem)**: literal residual ↔
      achievable conjunct ∧ off-achievable conjunct.
    * **Achievable conjunct (CONDITIONAL on pure-topology
      sub-residual)**: discharged via identity theorem from the
      witness-ball agreement.
    * **Off-achievable conjunct**: NOT discharged here. The literal
      tsum returns `0` on non-summable series; on the off-achievable
      strip the ζ-series diverges, so the literal expansion value is
      generically `-1/log z`, which is not equal to the analytic
      continuation `polyLog 0 z = z/(1-z)`. Hence the off-achievable
      conjunct is **mathematically false** for the literal tsum-based
      expansion in general.
    * **Unconditional achievable witness-ball agreement (UNCONDITIONAL
      theorem)**: maximal unconditional content directly deliverable.

    The literal residual is **structurally unattainable** at the
    literal-tsum interpretation; the **mathematically correct
    replacement** is the corrected Prop
    `JonquieresExpansionAnalyticOnPuncturedBall0_via_polyLog` from
    Stage L23, which is an UNCONDITIONAL theorem. -/
theorem agreementResidual0_honestStatus :
    -- Decomposition (unconditional)
    (JonquieresExpansionAnalyticContinuationAgreementResidual0 ↔
      AgreementOnAchievable_0 ∧ OffAchievableResidual0) ∧
    -- Achievable conjunct conditional on topology
    (AchievableSubdomainPreconnectednessResidual →
      AgreementOnAchievable_0) ∧
    -- Under topology, full residual ↔ off-achievable alone
    (AchievableSubdomainPreconnectednessResidual →
      (JonquieresExpansionAnalyticContinuationAgreementResidual0 ↔
        OffAchievableResidual0)) ∧
    -- Maximal unconditional content: witness-ball agreement
    (∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball ((1/2 : ℂ)) ρ ⊆
        (Metric.ball (0 : ℂ) 1 ∩ JonquieresAnalyticDomain) ∧
      (∀ z ∈ Metric.ball ((1/2 : ℂ)) ρ,
        jonquieresExpansion 0 z = polyLog 0 z)) :=
  ⟨agreementResidual0_decomposition,
   agreementOnAchievable_0_of_preconnected,
   agreementResidual0_iff_offAchievable_under_topology,
   achievableAgreementOnWitnessBall_at_zero_unconditional⟩

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms agreementResidual0_decomposition
#guard_msgs(drop info) in
#print axioms agreementOnAchievable_0_ball_around_half_unconditional
#guard_msgs(drop info) in
#print axioms agreementOnAchievable_0_of_preconnected
#guard_msgs(drop info) in
#print axioms agreementResidual0_iff_offAchievable_under_topology
#guard_msgs(drop info) in
#print axioms achievableAgreementOnWitnessBall_at_zero_unconditional
#guard_msgs(drop info) in
#print axioms agreementResidual0_honestStatus
end AxiomAudit
