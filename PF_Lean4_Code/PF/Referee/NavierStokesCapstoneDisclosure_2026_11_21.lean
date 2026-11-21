/-
# NS capstone: disclosure of the substrate encoding, and the faithful one

**Date**: 2026-11-21 (Legion).

`PF/PrincipiaFractalisToEMetaCapstone_2026_11_16.lean` conjunct (7)
asserts `Clay_NavierStokes_Standard PF_NSEncodingSubstrate`, described
in its comment as "reproduces classical NS result at Clay-standard
form". That theorem is true, and it asserts nothing about
Navier-Stokes. This file proves that, and supplies the encoding that
does carry the content.

## The defect, in three layers

```lean
def PF_NSEncodingSubstrate : StandardNS3DEncoding where
  Velocity := Unit
  InitialData := Unit
  isSchwartzDivFree _ := True
  hasGlobalSmoothSolution _ := UniformVortexStretchingBoundAllN 1 1
```

* the velocity and initial-data carriers are **`Unit`** — a single point;
* `isSchwartzDivFree` is **`True`** — the admissibility hypothesis
  constrains nothing;
* `hasGlobalSmoothSolution` is pinned to a **free** algebraic bound.
  `UniformVortexStretchingBoundAllN 1 1` holds because the Hadamard
  product is submultiplicative — proved for every `n` as
  `vortex_stretching_bounded_all_n`, and free for the genuine `(ω·∇)u`
  too by the operator-norm inequality
  (`norm_vortexStretchingFaithful_le`).

Since `Clay_NavierStokes_Standard E` unfolds to
`∀ u0, E.isSchwartzDivFree u0 → E.hasGlobalSmoothSolution u0`, conjunct
(7) unfolds to `∀ (_ : Unit), True → <free bound>`.

This is structurally the same defect as the P-vs-NP V2 vacuity
(`computability := True`), which the capstone already discloses as
`¬ Literal_P_neq_NP_V2`. The repair here follows that precedent exactly:
**keep the superseded object, prove its vacuity, state the faithful
target.** Nothing is deleted.

## What is proved

* `clay_standard_substrate_is_vacuous` — the substrate contract is
  equivalent to `True`. The gravestone, machine-checked.
* `PF_NSEncodingFaithful` — the encoding over the real carriers:
  space-time velocity fields, Schwartz initial data, `AdmissibleDatum`
  for admissibility, `HasGlobalSolution` for global smoothness.
* `clay_standard_faithful_iff` — the Clay contract on *that* encoding is
  **equivalent to Fefferman's faithful statement**. So the faithful
  encoding is the right one, and the contract over it is the open Clay
  problem.

**`Clay_NavierStokes_Standard PF_NSEncodingFaithful` is not proved here
or anywhere.** It is the Clay problem.
-/

import PF.Referee.NavierStokesCapstoneTypedBridgeSubstrate
import PF.NavierStokes.Fefferman2000_Faithful_ForcingAdmissible_2026_11_21

namespace PF.Referee.NavierStokesCapstoneDisclosure

open PF.Referee.StandardClayStatements
open PF.Referee.NavierStokesCapstoneTypedBridgeSubstrate (PF_NSEncodingSubstrate)
open PF.NavierStokes.FeffermanFaithful

/-! ## §1 — The disclosure -/

/-- **★ The substrate NS contract is vacuous.**

    `Clay_NavierStokes_Standard PF_NSEncodingSubstrate ↔ True`.

    Its hypothesis is `True` on a one-point carrier and its conclusion is
    a free algebraic bound, so the contract constrains nothing. The
    forward direction is immediate; the backward direction is exactly the
    discharge the capstone already uses, which is what shows the
    conclusion was free all along.

    Conjunct (7) of the ToE meta-capstone is therefore not evidence about
    Navier-Stokes. Stating this as a theorem — rather than a comment —
    is the point: the vacuity is now machine-checked and cannot drift
    back into a claim. -/
theorem clay_standard_substrate_is_vacuous :
    Clay_NavierStokes_Standard PF_NSEncodingSubstrate ↔ True := by
  constructor
  · intro _; trivial
  · intro _
    exact PF.Referee.NavierStokesCapstoneTypedBridgeSubstrate.PF_NS_capstone_substrate_yields_Clay_NavierStokes_standard

/-! ## §2 — The faithful encoding -/

/-- **The NS encoding over real carriers.**

    Velocity: space-time vector fields `V × ℝ → V`. Initial data:
    Schwartz maps, Fefferman's decay condition (4). Admissibility:
    `AdmissibleDatum`, a genuine `fderiv`-computed divergence
    constraint. Global smoothness: `HasGlobalSolution`, which carries
    joint `C^∞`, the initial condition, incompressibility, the full
    momentum equation and bounded energy.

    Nothing here is `Unit` and nothing is `True`. -/
def PF_NSEncodingFaithful : StandardNS3DEncoding where
  Velocity := V × ℝ → V
  InitialData := SchwartzMap V V
  isSchwartzDivFree := AdmissibleDatum
  hasGlobalSmoothSolution := HasGlobalSolution

/-- **★ The Clay contract over the faithful encoding IS Fefferman's
    statement.**

    So the faithful encoding is the correct one: discharging the typed
    contract over it would be discharging the Clay problem, and
    discharging it over `PF_NSEncodingSubstrate` is discharging nothing.

    **This proves the equivalence, not the statement.** Neither side is
    asserted. -/
theorem clay_standard_faithful_iff :
    Clay_NavierStokes_Standard PF_NSEncodingFaithful
      ↔ Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful := by
  constructor
  · intro h
    exact clay_of_global_solutions (fun u0 hu0 => h u0 hu0)
  · intro h u0 hu0
    obtain ⟨U, P, ν, hν, hU, hP, hinit, hdiv, hmom, hE⟩ := h u0 hu0
    exact ⟨ν, U, P, hν, ⟨hU, hP, fun x t ht => hdiv x t ht,
      fun x t ht => hmom x t ht⟩, hinit, hE⟩

/-- The two encodings are not interchangeable: the substrate contract is
    vacuous while the faithful contract is the Clay problem. Recorded so
    that a reader who meets conjunct (7) is pointed at the real target. -/
theorem substrate_contract_does_not_give_faithful
    (h : Clay_NavierStokes_Standard PF_NSEncodingSubstrate) :
    ¬ (Clay_NavierStokes_Standard PF_NSEncodingSubstrate →
        Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful)
      ∨ Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful := by
  by_cases hc : Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful
  · exact Or.inr hc
  · exact Or.inl (fun himp => hc (himp h))

#print axioms clay_standard_substrate_is_vacuous
#print axioms clay_standard_faithful_iff
#print axioms substrate_contract_does_not_give_faithful

end PF.Referee.NavierStokesCapstoneDisclosure
