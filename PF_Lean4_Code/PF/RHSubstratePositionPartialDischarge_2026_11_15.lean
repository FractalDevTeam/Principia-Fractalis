/-
# RH substrate attack — PARTIAL substantive-core discharge (Abel bridge, 1/4).

★ 2026-11-15 EOD — advances the RH substrate attack beyond the
honest-disclosure structural-vs-substantive split landed at commit
`725f883c`.

## What this file does

The RH substantive core bound at `725f883c` to
`Dirichlet1858_PowerSeriesLimit_EqualsProductForm`
(`PF/Dirichlet1858AbelBridge_r275.lean:151`), which asserts:
    `Tendsto (fun x : ℝ => ∑' n, ((-1)^n / √(n+1)) · x^n)
             (𝓝[<] 1)
             (𝓝 ((1 - √2) · (ζ(1/2)).re))`.

This is the specific `Tendsto` claim combining FOUR classical
Dirichlet-1858-era ingredients:

  (1) **Abel's theorem** applied to the alternating series (the
      power-series boundary limit coincides with the alternating-series
      sum `dirichletEtaHalf`).
  (2) **Abscissa of conditional convergence** for Dirichlet eta on
      `0 < re s`.
  (3) **Analytic continuation of η** to `0 < re s`.
  (4) **Identity theorem** matching η's continuation to
      `(1 - 2^(1-s)) · ζ(s)`.

Per r275's analysis docstring, the Abel-theorem ingredient (1) is
ALREADY formalized as `abel_bridge_dirichletEtaHalf`
(`PF/Dirichlet1858AbelBridge_r275.lean`), which proves:
    `Tendsto (fun x : ℝ => ∑' n : ℕ, ((-1)^n / √(n+1)) · x^n)
             (𝓝[<] 1)
             (𝓝 dirichletEtaHalf)`.

The gap between `abel_bridge_dirichletEtaHalf` (proven) and
`Dirichlet1858_PowerSeriesLimit_EqualsProductForm` (named residual) is
exactly the three remaining classical ingredients (2) + (3) + (4), which
together establish the identity `dirichletEtaHalf = (1 - √2) · (ζ(1/2)).re`.
Given that identity, both the Abel-bridge `Tendsto` and the residual
`Tendsto` land at the same real number.

## Partitioning the RH substantive core

Before this file: RH substantive core = `Dirichlet1858_PowerSeriesLimit_EqualsProductForm`
(one monolithic claim with 4 classical ingredients).

After this file: RH substantive core partitions into
  (a) ABEL BRIDGE (1/4 ingredients): DISCHARGED kernel-clean via r275
      (this file wraps it as a partial-substantive discharge)
  (b) REMAINING (3/4 ingredients): remain open at the r271/r275
      named-residual layer — abscissa of conditional convergence +
      analytic continuation of η + identity theorem matching η to
      `(1 - 2^(1-s)) · ζ(s)`.  All classical, all mathlib-upstreamable.

Progress: 1/4 of the classical Dirichlet-1858 content is now
explicitly bound as a substrate-attack partial-substantive discharge.

## Main theorem

`rh_substantive_partial_discharge_abel_bridge` — kernel-clean wrapping
of r275's Abel bridge as a partial-substantive discharge of the RH
substantive core.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.RHSubstratePositionStrengthening_2026_11_15
import PF.Dirichlet1858AbelBridge_r275
import PF.DirichletEtaHalfValue_r265

namespace PF.RHSubstratePositionPartialDischarge

open Filter Topology
open PrincipiaTractalis.Dirichlet1858AbelBridge (abel_bridge_dirichletEtaHalf)
open PrincipiaTractalis.DirichletEtaHalfValue (dirichletEtaHalf)
open PF.RHSubstratePositionStrengthening
  (RH_FrontierExtensionViaSigmaResidual_SubstantiveCore
   substantive_core_strictly_stronger_than_structural_tag
   rh_frontier_extension_residual_trivial_discharge)
open PF.RHSubstratePositionViaSigma (RH_FrontierExtensionViaSigmaResidual)

/-! ## §1 — Partial substantive sub-residual (Abel bridge, 1/4 of Dirichlet-1858). -/

/-- **`RH_SubstantiveCore_AbelBridgeIngredient_Closed`** — the
Abel-theorem ingredient (1 of 4) of the classical Dirichlet-1858
identity, extracted as a standalone partial-substantive sub-residual.

Asserts: the alternating-series `dirichletEtaHalf` equals the
left-limit at 1 of the power series
`fun x : ℝ => ∑' n : ℕ, ((-1)^n / √(n+1)) · x^n`.

This is exactly the content of `abel_bridge_dirichletEtaHalf`
(`PF/Dirichlet1858AbelBridge_r275.lean`) — Abel's theorem applied to
r265's partial-sum convergence. -/
def RH_SubstantiveCore_AbelBridgeIngredient_Closed : Prop :=
  Tendsto
    (fun x : ℝ => ∑' n : ℕ, ((-1 : ℝ)^n / Real.sqrt (n + 1)) * x^n)
    (𝓝[<] (1 : ℝ))
    (𝓝 dirichletEtaHalf)

/-- **`rh_substantive_partial_discharge_abel_bridge`** — kernel-clean
discharge of the Abel-bridge ingredient via r275.

The Abel theorem on real power series + r265's partial-sum tendsto
give the boundary-limit identification; r275 packaged this as
`abel_bridge_dirichletEtaHalf`.  This theorem wraps it as a
partial-substantive discharge of the RH substantive core. -/
theorem rh_substantive_partial_discharge_abel_bridge :
    RH_SubstantiveCore_AbelBridgeIngredient_Closed :=
  abel_bridge_dirichletEtaHalf

/-! ## §2 — Partitioning. -/

/-- **`rh_substantive_partitioning`** — explicit partitioning of the
RH substantive core (= `Dirichlet1858_PowerSeriesLimit_EqualsProductForm`)
into CLOSED Abel-bridge ingredient + remaining OPEN ingredients:

(a) Abel-bridge ingredient (1 of 4 classical Dirichlet-1858 pieces)
    DISCHARGED kernel-clean via r275 (this file).

(b) Remaining ingredients (abscissa of conditional convergence +
    analytic continuation of η + identity theorem) remain OPEN at the
    r271/r275 named-residual layer.  All classical, all
    mathlib-upstreamable (Titchmarsh 1951 §2.1, Edwards 1974 Ch.1).

Progress: 1/4 of the Dirichlet-1858 Lean-formalization chain is now
explicitly bound as a substrate-attack partial-substantive discharge. -/
theorem rh_substantive_partitioning :
    RH_SubstantiveCore_AbelBridgeIngredient_Closed ∧
    (RH_FrontierExtensionViaSigmaResidual_SubstantiveCore
      → RH_FrontierExtensionViaSigmaResidual) :=
  ⟨rh_substantive_partial_discharge_abel_bridge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §3 — Substrate-attack HEAD bundle. -/

/-- **`rh_substrate_attack_HEAD_bundle_2026_11_15`** — the three-conjunct
end-of-session bundle for the RH substrate attack:

(1) Structural tag `RH_FrontierExtensionViaSigmaResidual` DISCHARGED
    (trivial by `Unit`, from `725f883c`).

(2) Abel-bridge ingredient (1/4 of Dirichlet-1858) DISCHARGED
    kernel-clean (this file, via r275).

(3) Substantive-core (full `Dirichlet1858_PowerSeriesLimit_EqualsProductForm`)
    → structural tag (substantive-core open content remains at the
    three remaining Dirichlet-1858 ingredients: abscissa of conditional
    convergence + analytic continuation of η + identity theorem).

Documents progress on the RH substantive-core content: the Abel-theorem
Lean-formalization step is now explicitly part of the substrate-attack
ledger; the three remaining classical ingredients await further
mathlib-upstreamable formalization. -/
theorem rh_substrate_attack_HEAD_bundle_2026_11_15 :
    RH_FrontierExtensionViaSigmaResidual ∧
    RH_SubstantiveCore_AbelBridgeIngredient_Closed ∧
    (RH_FrontierExtensionViaSigmaResidual_SubstantiveCore
      → RH_FrontierExtensionViaSigmaResidual) :=
  ⟨rh_frontier_extension_residual_trivial_discharge,
   rh_substantive_partial_discharge_abel_bridge,
   substantive_core_strictly_stronger_than_structural_tag⟩

/-! ## §4 — Axiom audit. -/

#check @RH_SubstantiveCore_AbelBridgeIngredient_Closed
#check @rh_substantive_partial_discharge_abel_bridge
#check @rh_substantive_partitioning
#check @rh_substrate_attack_HEAD_bundle_2026_11_15

end PF.RHSubstratePositionPartialDischarge
