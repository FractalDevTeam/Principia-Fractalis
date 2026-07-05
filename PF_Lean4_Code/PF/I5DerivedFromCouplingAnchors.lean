/-
# I5 (vortex-doubling α_NS = 2·α_BSD) as a Derived Theorem, Not a Declaration

★ 2026-07-05 (r21 follow-up) — closing the invariant-vs-derivation gap
external reviewer identified in Agent 15's report ★

## Why this file exists

`MinimalSubstrateRigidity.MinimalSatisfiesInvariants` currently declares
`inv_NS_BSD : a.a_NS = 2 * a.a_BSD` as invariant M4 (a required field of
any α-assignment satisfying the minimal-invariants structure).  For the
substrate's canonical `framework_alpha`, this invariant is proved by ring
on the definitional values α_NS = 3π/2 and α_BSD = 3π/4.

BUT — those definitional values are themselves declared.  Agent 15's
external-reviewer-refinement finding: the corpus already has two coupling
anchors (kernel-only) in `AlphaBasisGenerators.lean` that make I5 fall out
in one line WITHOUT needing MinimalSubstrateRigidity's declaration:

  * `alpha_NS_eq_pi_times_alpha_RH   : α_NS = π · α_RH`     (line 191)
  * `alpha_BSD_eq_pi_half_times_alpha_RH : α_BSD = (π/2) · α_RH`   (line 184)

Composing: α_NS = π · α_RH = 2 · ((π/2) · α_RH) = 2 · α_BSD.  Kernel-only.

## What this file establishes (all axiom-free)

  * `I5_alpha_NS_eq_two_alpha_BSD_from_coupling_anchors` — the substrate
    identity α_NS = 2·α_BSD is a one-line consequence of the two coupling
    anchors, WITHOUT reliance on MinimalSubstrateRigidity's declaration.

  * `I5_reformulation_capstone` — packages both coupling anchors + the
    derivation into a single citable bundle documenting that I5 is now a
    derived theorem (from coupling anchors), no longer requiring a
    declared invariant.

## Honest scope

This file DOES NOT eliminate the coupling anchors themselves — they remain
substrate-declared facts about the framework's canonical α-assignment.
What it DOES eliminate is the redundant declaration of I5 as an
independent invariant on top of those anchors.  Effective free-parameter
count of the α-skeleton derivation drops by one (I5 is now a theorem, not
a hypothesis).

The genuine PDE-side derivation of I5 from Navier-Stokes vortex-stretching
term `ω·∇u` on the base-3 fractal lattice remains open (see OPEN_PROBLEMS.md
Priority 2).  This file addresses the algebraic-side layer only.

Stage 2026-07-05 r21 follow-up — closes the invariant-vs-derivation gap
Agent 15 identified.
-/

import PF.AlphaBasisGenerators
import PF.MillenniumSixReductions
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace I5DerivedFromCouplingAnchors

open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis

/-- **★★★ I5 AS A DERIVED THEOREM ★★★** — α_NS = 2·α_BSD is a
    one-line consequence of the two coupling anchors in
    `AlphaBasisGenerators.lean`, without invoking any declared
    invariant on top of them.

    Proof: substitute both coupling identities and simplify
    (2 · (π/2) · α_RH = π · α_RH). -/
theorem I5_alpha_NS_eq_two_alpha_BSD_from_coupling_anchors :
    alpha_value AlphaClass8.NS = 2 * alpha_value AlphaClass8.BSD := by
  rw [alpha_NS_eq_pi_times_alpha_RH, alpha_BSD_eq_pi_half_times_alpha_RH]
  ring

/-- **★★ I5 REFORMULATION CAPSTONE ★★** — package the two coupling
    anchors + the composed derivation as a single citable bundle
    documenting that I5 is a derived theorem, not a declared invariant.

    (H1) α_BSD = (π/2) · α_RH        [from `alpha_BSD_eq_pi_half_times_alpha_RH`]
    (H2) α_NS  = π · α_RH             [from `alpha_NS_eq_pi_times_alpha_RH`]
    (I5) α_NS  = 2 · α_BSD             [derived one-line from (H1)+(H2)]

    This file's contribution is the composition; the anchors themselves
    are from `AlphaBasisGenerators.lean`. -/
theorem I5_reformulation_capstone :
    -- (H1) α_BSD coupling anchor
    alpha_value AlphaClass8.BSD = (Real.pi / 2) * alpha_value AlphaClass8.RH ∧
    -- (H2) α_NS coupling anchor
    alpha_value AlphaClass8.NS = Real.pi * alpha_value AlphaClass8.RH ∧
    -- (I5) derived from (H1)+(H2)
    alpha_value AlphaClass8.NS = 2 * alpha_value AlphaClass8.BSD :=
  ⟨alpha_BSD_eq_pi_half_times_alpha_RH,
   alpha_NS_eq_pi_times_alpha_RH,
   I5_alpha_NS_eq_two_alpha_BSD_from_coupling_anchors⟩

/-! ## Honest scope: what this file DOES and DOES NOT do

**DOES**:
  * Prove I5 as a one-line consequence of the corpus's existing two
    coupling anchors, without invoking any declared invariant.
  * Provide a citable capstone bundling coupling anchors + derivation.
  * Upgrade the α-skeleton derivation count by one: I5 is now a theorem
    that follows from the two coupling anchors, not an independent
    invariant declared on top of them.

**DOES NOT**:
  * Derive the coupling anchors themselves from more basic substrate
    content. They remain declared framework definitions of the
    canonical α_NS = 3π/2 and α_BSD = 3π/4.
  * Bridge to Navier-Stokes vortex-stretching term `ω·∇u`. The PDE-side
    first-principles derivation of I5 from vortex dynamics remains
    genuinely open (see OPEN_PROBLEMS.md Priority 2).
  * Change `MinimalSubstrateRigidity.MinimalSatisfiesInvariants`'s
    structure. That structure's `inv_NS_BSD` field remains as-declared;
    this file provides an alternative kernel-only route to the same
    identity via the coupling anchors, showing the invariant is
    redundant given the anchors.
-/

end I5DerivedFromCouplingAnchors
end PrincipiaTractalis
