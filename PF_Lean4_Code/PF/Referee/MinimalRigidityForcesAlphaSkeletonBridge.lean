/-
# PF.Referee.MinimalRigidityForcesAlphaSkeletonBridge

★★★★★★ 2026-11-04 — THE ASSIGNMENT-TO-FRAMEWORK α BRIDGE ★★★★★★

## Why this file exists

`OCIRC_RESWEEP_2026-11-03.md` measured the project's own premise auditor
(`PF/Audit/PremiseAudit.lean`) over the full 1,552-module closure and found
**17 theorems named `unified_minimal_forces_*` whose minimal-rigidity
hypothesis is dead** — the binder is literally `_hM`, and the proof term is
the corresponding unconditional theorem.

The cause is a property of the *statements*, not of the proofs. Each of those
17 concluded a **closed** sentence: one about the framework's global
α-constants (`α_Hodge`, `α_QG`, …, defined in
`PF/CrossMillenniumSharedInvariants.lean`) or about a derived physical
constant. No proof of a closed sentence can consume a hypothesis about `u`,
so no proof-side repair exists. The adjudicated repair — route the conclusion
through `unified_alpha_skeleton_forced_by_minimal_invariants` — can only reach
a theorem **whose conclusion mentions `u`**.

Pablo's decision, 2026-11-04: **restate them so the conclusion mentions `u`.**

## What this file provides

The one lemma that makes that restatement mechanical and honest:

  under substrate-rigidity, `u`'s *own* α-fields **are** the framework's
  global α-constants.

With it, a theorem that asserted `P(α_Hodge, α_QG, …)` is restated as
`P(u.sector2.a_Hodge, u.sector2.a_QG, …)` — the same mathematical content,
now predicated of the substrate assignment — and proved by rewriting along
this bridge and appealing to the original unconditional theorem.

## Why the restatement is strictly stronger, not a relabelling

The restated conclusions are **false for a general `u`**: an assignment with
`a_Hodge = 1` satisfies neither `a_Hodge ^ 2 = a_Hodge + 1` nor any of the
brackets. They become true only once minimal rigidity pins the nine axes. So
`hM` is load-bearing in the restated statements in the strongest available
sense — delete it and the theorem is not merely unproved, it is **false**.
That is what makes the name `unified_minimal_forces_…` true of the statement
it labels, which is what the auditor was objecting to.

This is the author's own repair pattern, adjudicated 2026-10-01 at
`MinimalRigidityForcesNonClayAlphasExtended.lean:114` and applied again at
`MinimalRigidityForcesH3CombinatorialStructure.lean:117`.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 5. 2026-11-04.
-/

import PF.Referee.MinimalSubstrateRigidityUnified
import PF.CrossMillenniumSharedInvariants

namespace PF.Referee.MinimalRigidityForcesAlphaSkeletonBridge

open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PF.Referee.MinimalSubstrateRigidityUnified

/-! ## §1 — The bridge -/

/-- **★★★★★★ SUBSTRATE-RIGIDITY IDENTIFIES `u`'s α-FIELDS WITH THE
    FRAMEWORK'S GLOBAL α-CONSTANTS ★★★★★★** —
    `unified_minimal_forces_assignment_eq_framework_alphas`.

    Under the substrate-rigidity hypothesis set, eight of the nine α-axes of
    the assignment `u` equal the framework's correspondingly-named global
    constant (the ninth, Poincaré, is the hypothesis itself — see the note at
    the end):

      `u.sector1.a_RH       = α_RH`         (both `3/2`)
      `u.sector1.a_YM       = α_YM`         (both `2`)
      `u.sector1.a_BSD      = α_BSD`        (both `3π/4`)
      `u.sector1.a_NS       = α_NS`         (both `3π/2`)
      `u.sector2.a_P        = α_P`          (both `√2`)
      `u.sector2.a_Hodge    = α_Hodge`      (both `φ`)
      `u.sector2.a_NP       = α_NP`         (both `φ + 1/4`)
      `u.sector2.a_QG       = α_QG`         (both `√(2π)`)

    Every component is `unified_alpha_skeleton_forced_by_minimal_invariants`
    composed with the definitional value of the global constant. The
    hypotheses are therefore load-bearing throughout: without them no
    component holds, since `u` is otherwise an arbitrary assignment.

    This is the rewriting device for the 2026-11-04 restatement campaign. Any
    closed theorem about the global α-constants lifts to a theorem about the
    substrate assignment by rewriting along these eight equalities.

    **Why there is no `a_Poincare` conjunct.** `α_Poincare` is `1` by
    definition, so `u.sector1.a_Poincare = α_Poincare` is definitionally the
    hypothesis `h_P` itself. Including it made the auditor report the bridge
    CONTAINED — correctly — so it is omitted. A caller that needs the Poincaré
    axis derives it in one line from `h_P`; see the restated theorems. -/
theorem unified_minimal_forces_assignment_eq_framework_alphas
    (u : UnifiedAlphaAssignment)
    (hM : UnifiedMinimalInvariants u)
    (h_P : u.sector1.a_Poincare = 1)
    (h_P_pos : 0 < u.sector2.a_P)
    (h_Hodge_pos : 0 < u.sector2.a_Hodge)
    (h_QG_pos : 0 < u.sector2.a_QG) :
    u.sector1.a_RH = α_RH ∧
    u.sector1.a_YM = α_YM ∧
    u.sector1.a_BSD = α_BSD ∧
    u.sector1.a_NS = α_NS ∧
    u.sector2.a_P = α_P ∧
    u.sector2.a_Hodge = α_Hodge ∧
    u.sector2.a_NP = α_NP ∧
    u.sector2.a_QG = α_QG := by
  obtain ⟨_hP, hRH, hYM, hBSD, hNS, _hPvNP, hP2, hHodge, hNP, hQG⟩ :=
    unified_alpha_skeleton_forced_by_minimal_invariants
      u hM h_P h_P_pos h_Hodge_pos h_QG_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRH]; unfold α_RH; ring
  · rw [hYM]; unfold α_YM; ring
  · rw [hBSD]; unfold α_BSD; ring
  · rw [hNS]; unfold α_NS; ring
  · rw [hP2]; unfold α_P; ring
  · rw [hHodge]; unfold α_Hodge PrincipiaTractalis.phi; ring
  · rw [hNP]; unfold α_NP PrincipiaTractalis.phi; ring
  · rw [hQG]; unfold α_QG; ring

/-! ## §2 — Negative control: the bridge is not vacuous

The bridge would be worthless if its conclusion held for every assignment.
It does not: a concrete assignment violating the forced Hodge value refutes
the corresponding component, so the rigidity hypotheses are doing the work.
This is recorded as a theorem rather than a comment so that it is checked by
the kernel on every build. -/

/-- **The bridge's conclusion is not a tautology.** For the assignment whose
    every axis is `0`, the `a_Hodge` component of the bridge fails, because
    `α_Hodge = φ ≠ 0`. Hence no proof of the bridge can avoid consuming the
    minimal-rigidity hypotheses. -/
theorem bridge_conclusion_fails_without_rigidity :
    ¬ ((⟨⟨0, 0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩ :
          UnifiedAlphaAssignment).sector2.a_Hodge = α_Hodge) := by
  show ¬ ((0 : ℝ) = α_Hodge)
  unfold α_Hodge PrincipiaTractalis.phi
  intro h
  -- `0 = (1 + √5)/2` forces `√5 = -1`, contradicting `0 ≤ √5`.
  have h5 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [h, h5]

end PF.Referee.MinimalRigidityForcesAlphaSkeletonBridge

#print axioms
  PF.Referee.MinimalRigidityForcesAlphaSkeletonBridge.unified_minimal_forces_assignment_eq_framework_alphas
#print axioms
  PF.Referee.MinimalRigidityForcesAlphaSkeletonBridge.bridge_conclusion_fails_without_rigidity
