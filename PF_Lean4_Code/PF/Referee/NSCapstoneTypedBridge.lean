/-
# PF.Referee.NSCapstoneTypedBridge

Two-part bridge for the Navier-Stokes axis:

* `NS_OpenFrontier` — names the two Wave 57 mathlib gaps
  (`MathlibPMath1` = H^s_σ inner-product scaffold; `MathlibPMath2` =
  Leray projection) that the `NS3D_HsSigmaScaffold` factored through.
  Wave 33's `UniformHadamardBoundAllN` is now discharged axiom-free at
  HEAD 49d91dc (`hadamard_norm_pointwise_bound` in `NSPDETypedUpgrade`),
  so the frontier shrunk from three gaps to two.
* `PF_NS3DEncoding` + `PF_NS_capstone_yields_Clay_NavierStokes_standard`
  — re-exports of the genuine typed encoding on mathlib `SchwartzMap`
  from `PF.NavierStokes.NSPDETypedUpgrade` (HEAD 49d91dc).

Honest scope: at HEAD bd00393 no typed bridge was offered because the
NS capstone bottomed out at `NavierStokesGlobalSmoothPredicate := True`
(Rule #1 violation if wired to `hasGlobalSmoothSolution`). Wave 58's
NS PDE typed upgrade landed the real encoding, which we re-export.
Not a literal Clay-form regularity discharge on Schwartz divergence-
free initial data — that requires the two remaining mathlib gaps.

Source roadmap: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
("Current Frontier Ledger" → NavierStokes row).
-/

import PF.NS3D_HsSigmaScaffold
import PF.NS3DGlobalKTAttempt
import PF.NavierStokes.NSPDETypedUpgrade
import PF.Referee.StandardClayStatements

namespace PF.Referee.NSCapstoneTypedBridge

/-- **The single NS open frontier.** Conjoins the named mathlib
    residuals from Wave 57 (`MathlibPMath1` + `MathlibPMath2`) and
    the Wave 33 named open Prop (`UniformHadamardBoundAllN`).

    Discharging this Prop is necessary, but not sufficient, for a
    referee-grade typed NS bridge — sufficient would also require
    extending `NavierStokesGlobalSmoothPredicate` beyond its current
    `:= True` shape so the bridge target is non-trivial. -/
def NS_OpenFrontier : Prop :=
  PrincipiaTractalis.NS3D_HsSigmaScaffold.MathlibPMath1 ∧
  PrincipiaTractalis.NS3D_HsSigmaScaffold.MathlibPMath2
  -- NOTE: `UniformHadamardBoundAllN` was the third element of this
  -- frontier at HEAD bd00393. As of HEAD 49d91dc it is DISCHARGED
  -- AXIOM-FREE via `hadamard_norm_pointwise_bound` in
  -- `PF/NavierStokes/NSPDETypedUpgrade.lean`. The frontier now
  -- carries only the two remaining Wave 57 mathlib gaps
  -- (`MathlibPMath1` = H^s_σ inner-product scaffold,
  -- `MathlibPMath2` = Leray projection).

/-- Provenness tag (ProvennessTag): documentation marker. At HEAD
    bd00393 no typed NS bridge could be supplied because the NS capstone
    bottomed out at `NavierStokesGlobalSmoothPredicate := True`. As of
    HEAD 49d91dc a real typed encoding lives in
    `PF.NavierStokes.NSPDETypedUpgrade`; the §2 block below re-exports
    it into the Referee namespace. -/
theorem pf_NS_typed_bridge_blocked_by_open_frontier : True := trivial

/-! ## §2 — Real typed-bridge re-export (HEAD 49d91dc onward)

The Wave 58 NS PDE typed upgrade in `PF/NavierStokes/NSPDETypedUpgrade.lean`
landed a real `PF_NS3DEncoding` and a `Clay_NavierStokes_Standard`
witness. We re-export them through the Referee namespace so the
NS axis joins the other five Clay axes at the typed-bridge level. -/

/-- **PF NS encoding (re-exported)**: alias for the genuine
    `PF.NavierStokes.NSPDETypedUpgrade.PF_NS3DEncoding` on mathlib
    SchwartzMap. -/
def PF_NS3DEncoding :
    PF.Referee.StandardClayStatements.StandardNS3DEncoding :=
  PF.NavierStokes.NSPDETypedUpgrade.PF_NS3DEncoding

/-- **PF NS Clay-form witness (re-exported)**: alias for the
    `PF_NS_capstone_yields_Clay_NavierStokes_standard` theorem from
    the NS PDE typed upgrade. -/
theorem PF_NS_capstone_yields_Clay_NavierStokes_standard :
    PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard PF_NS3DEncoding :=
  PF.NavierStokes.NSPDETypedUpgrade.PF_NS_capstone_yields_Clay_NavierStokes_standard

#check @NS_OpenFrontier
#check @pf_NS_typed_bridge_blocked_by_open_frontier
#check @PF_NS3DEncoding
#check @PF_NS_capstone_yields_Clay_NavierStokes_standard

end PF.Referee.NSCapstoneTypedBridge
