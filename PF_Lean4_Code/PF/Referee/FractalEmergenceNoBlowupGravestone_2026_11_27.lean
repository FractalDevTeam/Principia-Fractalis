/-
# `fractalEmergenceNoBlowup` — the gravestone, and the faithful target

**Date**: 2026-11-27 (Legion).

Two of the NS axis's three framework Props were repointed to faithful carriers
in November, both using the same discipline — keep the old object under a
`_SUPERSEDED` name, prove its collapse, and let the original name mean the real
statement:

* `NavierStokesGlobalSmoothness` (2026-11-20) now **is**
  `Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful`, with
  `NavierStokesGlobalSmoothness_unitPlaceholder_collapses` as its gravestone.
* `NoBlowup3D` (2026-11-21) now **is**
  `PF.NavierStokes.FeffermanFaithful.VorticityAPrioriBound` — slot 3, a
  vorticity bound uniform in the time horizon — with
  `NoBlowup3D_unitPlaceholder_collapses` as its gravestone, and
  `no_blowup_3D_implies_clay` doing the genuine conditional work.

The third never got the treatment. `MillenniumSixReductions.lean:183`:

```lean
def fractalEmergenceNoBlowup (α : ℝ) : Prop :=
  α = 3 * Real.pi / 2 →
  ∀ (vortex_data : Unit), ∃ (emergence_resolution : Unit), True
```

`NSCascadeCrowBound.lean:394` records the decision not to touch it — *"We do
NOT modify `fractalEmergenceNoBlowup` (still a Unit-typed …)"* — but the
vacuity was left as a comment. §1 makes it a theorem of the corpus, which is
the standard this axis already holds itself to elsewhere.

## Why the repoint is not done here

`fractalEmergenceNoBlowup_discharged` (`NSBase3SelfSimilarity.lean:296`) is
consumed at **eleven** sites:

| file | sites |
|---|---|
| `CrossProblemEquivalenceAttack.lean` | 165, 221, 234, 340, 419, 463 |
| `NSCascadeCrowBound.lean` | 429 |
| `NS_SubstrateBulletproofClosure.lean` | 102 |
| `NSBase3SelfSimilarity.lean` | 323 |
| `NS3DVortexStretchingObstruction.lean` | 524, 606, 753 |
| `NS2DGlobalRegularity.lean` | 402, 476 |
| `NS3DLocalRegularityViaBKM.lean` | 262, 334 |

Every one of them *discharges* the Prop. The faithful target cannot be
discharged — it is the open Clay estimate — so repointing the name in place
would break all of them, and correctly so. The repoint is therefore a
deliberate refactor with a known radius, exactly as `NoBlowup3D`'s was, and it
belongs in its own operation rather than hidden inside this file. What this
file does is remove the excuse for delay: the vacuity is now machine-checked,
and the faithful target is named and reachable.

Nothing upstream is renamed, reworded or deleted.
-/
import PF.NS3DVortexStretchingObstruction

set_option autoImplicit false

namespace PF.Referee.FractalEmergenceNoBlowupGravestone

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis.NS3DVortexStretchingObstruction

/-! ## §1 — The gravestone -/

/-- **★ `fractalEmergenceNoBlowup` is equivalent to `True`, at every `α`.**

    Its consequent is `∀ _ : Unit, ∃ _ : Unit, True`, so the implication holds
    outright. No discharge of it was ever evidence about finite-time
    singularities of Navier–Stokes. -/
theorem fractalEmergenceNoBlowup_collapses (α : ℝ) :
    fractalEmergenceNoBlowup_unitPlaceholder_SUPERSEDED α ↔ True := by
  constructor
  · intro _
    trivial
  · intro _ _ _
    exact ⟨(), trivial⟩

/-- **And the `α`-condition does no work either.**

    The Prop is the same at every `α`, so the hypothesis `α = 3π/2` that gives
    it its name selects nothing. A reader meeting
    `fractalEmergenceNoBlowup (alpha_at_enum .NS)` should know the NS
    `α`-value is not participating. -/
theorem fractalEmergenceNoBlowup_independent_of_alpha (α β : ℝ) :
    fractalEmergenceNoBlowup_unitPlaceholder_SUPERSEDED α ↔
      fractalEmergenceNoBlowup_unitPlaceholder_SUPERSEDED β := by
  rw [fractalEmergenceNoBlowup_collapses, fractalEmergenceNoBlowup_collapses]

/-! ## §2 — It transports nothing -/

/-- **★★ Assuming it and concluding the real estimate is the same as
    concluding the real estimate.**

    So the Prop cannot be a step toward `NoBlowup3D`: anything derivable with
    it as a hypothesis was derivable without it. This is the same instrument
    the corpus uses on free-antecedent bridges elsewhere, and it is the precise
    sense in which the framework's no-blowup conjunct is not load-bearing. -/
theorem fractalEmergence_transports_nothing (α : ℝ) :
    (fractalEmergenceNoBlowup_unitPlaceholder_SUPERSEDED α → NoBlowup3D) ↔ NoBlowup3D := by
  constructor
  · intro h
    exact h ((fractalEmergenceNoBlowup_collapses α).mpr trivial)
  · intro h _
    exact h

/-! ## §3 — The faithful target, named -/

/-- `NoBlowup3D` is slot 3 of the faithful reduction: a vorticity bound
    uniform in the time horizon. Unfolding only. -/
theorem noBlowup3D_is_the_apriori_bound :
    NoBlowup3D = PF.NavierStokes.FeffermanFaithful.VorticityAPrioriBound := rfl

/-- **The conditional that does carry content**, re-exported so a reader
    arriving at the vacuous Prop is pointed at the real reduction: given the
    two classical inputs, the a-priori vorticity bound yields Fefferman's
    statement. Every premise is a hypothesis; nothing is discharged. -/
theorem faithful_route_to_clay
    (h1 : PF.NavierStokes.FeffermanFaithful.FujitaKato_Faithful)
    (h2 : PF.NavierStokes.FeffermanFaithful.BKMContinuation_Faithful)
    (h3 : NoBlowup3D) :
    PF.NavierStokes.FeffermanFaithful.Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful :=
  no_blowup_3D_implies_clay h1 h2 h3

/-- **The non-claim, stated.** Nothing here proves or disproves the a-priori
    bound, and nothing here bears on the Clay statement. Recorded so §2 cannot
    be read as a refutation of the NS axis rather than a measurement of one
    Prop on it. -/
theorem no_verdict_on_the_apriori_bound :
    NoBlowup3D ∨ ¬ NoBlowup3D :=
  em NoBlowup3D

end PF.Referee.FractalEmergenceNoBlowupGravestone
