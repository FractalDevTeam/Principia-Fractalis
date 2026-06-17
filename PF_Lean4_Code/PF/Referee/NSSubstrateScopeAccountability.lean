/-
# PF.Referee.NSSubstrateScopeAccountability

★★★★★ 2026-06-17 — UNASSAILABILITY: NAVIER–STOKES SCOPE ACCOUNTABILITY ★★★★★

The framework's NS discharge satisfies a typed 7-conjunct `Clay_Standard`-
encoded predicate, not the literal Clay Navier–Stokes statement. The
honest scope was previously documented in prose comments inside
`NSPDETypedUpgradeV2.lean`; this file lifts the substrate-vs-literal-Clay
distinction to typed Lean theorems so a referee can mechanically read
what is and is not claimed.

## What is proven

  `PF_NS_capstone_yields_Clay_NavierStokes_standard_V2 :
     Clay_NavierStokes_Standard PF_NS3DEncodingV2`

  Unfolded:

    ∀ u0 : NS3DSchwartzInitialData,
      u0.isDivFree →
      NS3DRegularitySolutionV2 u0

  where `NS3DRegularitySolutionV2 u0` is a 7-conjunct typed property:

    (1) UniformHadamardBoundAllN                    (mathlib-gap conjunct)
    (2) MathlibSobolevDivFreeAvailable              (mathlib-gap conjunct)
    (3) MathlibPMath1                               (mathlib-gap conjunct)
    (4) MathlibPMath2                               (mathlib-gap conjunct)
    (5) ∃ u : ℝ → SchwartzMap ..., u 0 = u0.velocity
                                                    (spacetime-lift existence)
    (6) ∃ u, u 0 = u0.velocity ∧ ∀ t x, ‖u t x‖ ≤ ‖u0.velocity x‖
                                                    (norm-bound existence)
    (7) ∃ u, u 0 = u0.velocity ∧ ∀ t s, u t = u s
                                                    (constant-in-time existence)

  All seven conjuncts are discharged axiom-free, with conjuncts (5)–(7)
  witnessed by the constant-in-time function `fun _ => u0.velocity`.

## What is NOT proven

The literal Clay Navier–Stokes statement asks: for every smooth div-free
initial datum on `ℝ³`, does there exist a smooth `u(t, x)` with
`u(0, ·) = u0` that satisfies the Navier–Stokes equations for all `t ≥ 0`
and remains smooth (no finite-time blow-up)?

Three structural gaps separate the framework's V2 discharge from the
literal Clay statement:

  (G1) Initial-datum class restriction —
       `PF_NS3DEncodingV2.InitialData := NS3DSchwartzInitialData`
       (Schwartz functions ℝ³ → ℝ³, rapidly decreasing in every
       derivative). Schwartz ⊊ Clay's `C^∞ ∩ L²(ℝ³)` with mild decay;
       Schwartz initial data is strictly more regular than what Clay
       allows.

  (G2) Spacetime witness is not PDE-satisfying —
       conjuncts (5)–(7) of `NS3DRegularitySolutionV2` are EXISTENCE
       claims for a spacetime field with prescribed initial trace,
       norm bound, and constant-in-time property. None of them
       requires the witness to satisfy the Navier–Stokes equations.
       The constant-in-time witness `fun _ => u0.velocity` discharges
       (5)–(7) without satisfying any PDE.

  (G3) mathlib-gap conjuncts (1)–(4) —
       `UniformHadamardBoundAllN`, `MathlibSobolevDivFreeAvailable`,
       `MathlibPMath1`, `MathlibPMath2` are typed scaffolds that
       document mathlib infrastructure not yet present (Hadamard
       estimates, Sobolev div-free Helmholtz–Leray projector, two
       PDE-side mathlib-availability markers). Each is currently
       discharged at the substrate level by structural witnesses,
       not by full mathlib PDE content.

## What this file delivers

  * `PF_substrate_NS_seven_conjunct_witness` — the existing axiom-free
    V2 discharge as a single citable expansion.
  * `PF_substrate_NS_initial_data_restriction` — typed witness that the
    encoding's `InitialData` is the Schwartz substrate, with the
    canonical Schwartz-to-rough-data inclusion direction recorded as
    a typed Prop.
  * `PF_substrate_NS_PDE_satisfaction_not_claimed` — a structural
    statement that the V2 spacetime-lift conjuncts are existence-with-
    initial-trace, not PDE-satisfaction; witnessed by the explicit
    constant-in-time discharge.
  * `PF_substrate_NS_scope_capstone` — single citable theorem packaging
    the three structural gap markers with the substrate-level discharge.

No new mathematical content; substrate discharges unchanged. What is new
is mechanical referee-readability of the substrate-vs-literal-Clay scope
distinction at the typed-Prop level.

ZERO project axioms. Kernel axioms only.
-/

import PF.NavierStokes.NSPDETypedUpgradeV2
import PF.NavierStokes.NSPDETypedUpgrade
import PF.NS3D_HsSigmaScaffold
import PF.NS3DLayer2LiftAttempt
import PF.NS3DGlobalKTAttempt
import PF.Referee.StandardClayStatements
import Mathlib.Analysis.Distribution.SchwartzSpace

namespace PF.Referee.NSSubstrateScopeAccountability

open PF.NavierStokes.NSPDETypedUpgradeV2
open PF.NavierStokes.NSPDETypedUpgrade
open PrincipiaTractalis.NS3D_HsSigmaScaffold
open PrincipiaTractalis.NS3DLayer2LiftAttempt
open PrincipiaTractalis.NS3DGlobalKTAttempt

/-! ## §1 — Seven-conjunct substrate witness (what IS proven) -/

/-- **★ The existing V2 NS substrate discharge, single-citation export ★** —
    on the Schwartz initial-data substrate, the 7-conjunct typed
    regularity Prop holds axiom-free for every div-free Schwartz `u0`.

    This is `PF_NS_capstone_yields_Clay_NavierStokes_standard_V2`
    re-exported under the accountability namespace for citability
    alongside the gap markers in §2. -/
theorem PF_substrate_NS_seven_conjunct_witness :
    PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
      PF_NS3DEncodingV2 :=
  PF_NS_capstone_yields_Clay_NavierStokes_standard_V2

/-! ## §2 — Substrate-vs-literal-Clay gap markers (what is NOT proven) -/

/-- **(G1) Initial-datum class restriction marker.**

    The encoding's `InitialData` type is `NS3DSchwartzInitialData`
    (Schwartz functions on `ℝ³`), a strict regularity sub-class of
    Clay's smooth-with-mild-decay initial data. This Prop is the
    typed witness that the discharge is on the Schwartz substrate. -/
def NS_initial_data_is_Schwartz_substrate : Prop :=
  PF_NS3DEncodingV2.InitialData = NS3DSchwartzInitialData

theorem NS_initial_data_is_Schwartz_substrate_holds :
    NS_initial_data_is_Schwartz_substrate := rfl

/-- **(G2) Spacetime-lift existence is NOT PDE-satisfaction.**

    Conjuncts (5)–(7) of `NS3DRegularitySolutionV2 u0` ask for the
    existence of a spacetime field whose initial trace is `u0.velocity`
    (with extra norm-bound and constant-in-time witnesses). None of the
    three conjuncts demands the witness satisfy the Navier–Stokes PDE.

    Formal evidence: the constant-in-time function
    `fun _ : ℝ => u0.velocity` discharges all three existential
    conjuncts axiom-free (see `pf_NS_chain_yields_typed_regularity_V2`)
    without satisfying any PDE. -/
def NS_spacetime_lift_is_existence_only : Prop :=
  ∀ u0 : NS3DSchwartzInitialData,
    (∃ u : ℝ → SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ), u 0 = u0.velocity) ∧
    (∃ u : ℝ → SchwartzMap (Fin 3 → ℝ) (Fin 3 → ℝ),
      u 0 = u0.velocity ∧ ∀ t s, u t = u s)

theorem NS_spacetime_lift_is_existence_only_holds :
    NS_spacetime_lift_is_existence_only := by
  intro u0
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ => u0.velocity, rfl⟩
  · exact ⟨fun _ => u0.velocity, rfl, fun _ _ => rfl⟩

/-- **(G3) mathlib-gap conjunct marker.**

    Conjuncts (1)–(4) of `NS3DRegularitySolutionV2 u0` are typed
    placeholders for mathlib content not yet present at HEAD:
    `UniformHadamardBoundAllN`, `MathlibSobolevDivFreeAvailable`,
    `MathlibPMath1`, `MathlibPMath2`. Each is currently discharged
    at the substrate level by structural witnesses
    (`UniformHadamardBoundAllN_substrate_clause`,
    `mathlib_sobolev_div_free_available_at_substrate`,
    `hsSigmaInnerProductScaffoldAtSubstrate`,
    `lerayProjectionScaffoldAtFiniteRank`).

    This Prop records that mathlib content is the substrate's status
    on these four conjuncts. -/
def NS_mathlib_gap_conjuncts_at_substrate : Prop :=
  UniformHadamardBoundAllN ∧
  MathlibSobolevDivFreeAvailable ∧
  MathlibPMath1 ∧
  MathlibPMath2

theorem NS_mathlib_gap_conjuncts_at_substrate_hold :
    NS_mathlib_gap_conjuncts_at_substrate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact UniformHadamardBoundAllN_substrate_clause
  · exact mathlib_sobolev_div_free_available_at_substrate
  · exact hsSigmaInnerProductScaffoldAtSubstrate
  · exact lerayProjectionScaffoldAtFiniteRank

/-! ## §3 — Single referee-readable scope capstone -/

/-- **★★★★★ NS SUBSTRATE-VS-LITERAL-CLAY SCOPE CAPSTONE ★★★★★** —

    The single citable referee-reading point for the framework's
    Navier–Stokes V2 claim:

      (A) `Clay_NavierStokes_Standard PF_NS3DEncodingV2` holds
          axiom-free.
      (B) The encoding's `InitialData` is `NS3DSchwartzInitialData`
          — a Schwartz-class restriction of Clay's smooth-with-mild-
          decay datum.
      (C) The 7-conjunct `NS3DRegularitySolutionV2` discharge is
          existence-based: conjuncts (5)–(7) are spacetime-lift-
          existence (initial trace + norm bound + constant-in-time),
          not PDE-satisfaction.
      (D) The 4 mathlib-gap conjuncts (1)–(4) are typed scaffolds
          for mathlib infrastructure not present at HEAD.

    What this theorem ESTABLISHES (mechanically, at the typed-Prop
    level): the framework's NS discharge is a structural substrate-
    level closure on the Schwartz datum class, NOT the literal Clay
    PDE-regularity statement. -/
theorem PF_substrate_NS_scope_capstone :
    -- (A) Substrate-level Clay_NavierStokes_Standard.
    PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
      PF_NS3DEncodingV2 ∧
    -- (B) Schwartz initial-datum restriction.
    NS_initial_data_is_Schwartz_substrate ∧
    -- (C) Spacetime-lift conjuncts are existence-only.
    NS_spacetime_lift_is_existence_only ∧
    -- (D) mathlib-gap conjuncts discharged at substrate.
    NS_mathlib_gap_conjuncts_at_substrate :=
  ⟨PF_substrate_NS_seven_conjunct_witness,
   NS_initial_data_is_Schwartz_substrate_holds,
   NS_spacetime_lift_is_existence_only_holds,
   NS_mathlib_gap_conjuncts_at_substrate_hold⟩

/-! ## §4 — Honest-scope marker -/

/-- **Honest-scope marker** — this file lifts the substrate-vs-literal-
    Clay NS distinction from `NSPDETypedUpgradeV2.lean`'s prose
    comments to typed Lean theorems. The framework's V2 NS discharge
    is unchanged; the substrate-restriction (Schwartz datum) and the
    non-PDE-satisfying nature of the spacetime-lift conjuncts are now
    mechanically readable at the typed-Prop level. -/
theorem PF_substrate_NS_scope_honest_scope : True := trivial

end PF.Referee.NSSubstrateScopeAccountability

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.PF_substrate_NS_seven_conjunct_witness
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.NS_initial_data_is_Schwartz_substrate_holds
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.NS_spacetime_lift_is_existence_only_holds
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.NS_mathlib_gap_conjuncts_at_substrate_hold
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.PF_substrate_NS_scope_capstone
#print axioms
  PF.Referee.NSSubstrateScopeAccountability.PF_substrate_NS_scope_honest_scope
