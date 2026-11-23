/-
# Principia Fractalis — substrate positions at HEAD, v2

**Date**: 2026-11-22 (Legion).  Successor to
`PF/PrincipiaFractalisSubstratePositions_2026_11_15.lean`.

## Why a successor, and what it repairs

The 2026-11-15 bundle is kept, unchanged, and still holds.  Three
things about it have since become false-to-the-tree, and this file
repairs all three by **adding**, never by replacing or renaming.

### (a) Its docstring promised six conjuncts; its statement carries five

The 11-15 docstring lists conjunct (1) as "NS — the squared Young
L¹⋆L²→L² convolution bound".  The theorem's statement begins at
conjunct (2), and its proof term is a five-tuple.  The module imports
`PF.Analytic.YoungConvolutionL1L2_2026_11_15` and opens
`convolution_squared_le_L1_sq_mul_L2_sq`, which then appears nowhere
else in the file.  So the NS slot was opened and never filled.

This file fills it — and fills it with the NS content that postdates
11-15, not with the Young bound, which is a convolution estimate and
not a position on Navier-Stokes.

### (b) Its P vs NP conjunct is on the V2 carrier, proved vacuous the same day

Conjunct (3) of the 11-15 bundle ends in

```
SpectralSeparatorFaithfulness_V2 → Literal_P_neq_NP_V2
```

and `PF/SpectralGapFaithfulSeparator_V4Pivot_2026_11_15.lean` proves
`¬ Literal_P_neq_NP_V2` unconditionally — the V2 carrier's
`computability := True` placeholder makes the literal statement
provably False.  That implication is therefore true with a false
premise: `v2_faithfulness_premise_is_false` below proves exactly that,
so the ground for the upgrade is itself machine-checked rather than
asserted in a comment.

The V4 pivot closes both V2 carrier defects and is **not** known
False.  Conjunct (4) here carries V4, with the V2 vacuity disclosure
travelling alongside it as evidence.

### (c) Poincaré and Fermat had no conjunct at all

Both axes have kernel-verified content at HEAD and neither appeared in
any position bundle.  They appear here — each paired with the
in-kernel disclosure of what its encoding actually is, so that no
reader can mistake the typed contract for the classical statement:

* Poincaré: `PF_PoincareEncoding.SmoothThreeManifold = ℝ` by `rfl`.
  The carrier is the real line, not a smooth 3-manifold; the contract
  over it unfolds to the W_α cascade ceiling identity.
* Fermat: `Standard_FermatLastTheorem_Standard PF_FermatEncoding ↔ True`.
  The encoding sets `holds _ := True`, so the typed contract asserts
  nothing.  The two genuine Fermat facts travel with it in the same
  conjunct: mathlib's `not_fermat_42`, and this project's difference
  form `not_fermat_42_sub`, which was absent from mathlib at pin.

## Scope

**No new mathematics is claimed in this file.**  Every conjunct is
discharged by a theorem already proved elsewhere in the corpus; the
only new proof here is `v2_faithfulness_premise_is_false`, which
composes two existing results to record why (b) is a repair.  Nothing
asserts a Clay solution.  Four conjuncts are deliberately statements
*about* encodings rather than about the classical objects, and each
says so in its own text.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-22.
-/

import PF.PrincipiaFractalisSubstratePositions_2026_11_15
import PF.SpectralGapFaithfulSeparator_V4Pivot_2026_11_15
import PF.Referee.NavierStokesCapstoneDisclosure_2026_11_21
import PF.Referee.ToECapstoneVacuityDisclosure_2026_11_22

namespace PF.PrincipiaFractalisSubstratePositionsV2

/-! ## §1 — The ground for the V2 → V4 upgrade -/

/-- **The 11-15 bundle's P-vs-NP premise is false.**

    `SpectralSeparatorFaithfulness_V2` unfolds to
    `EnumToClassSeparationBridgeV2`, which the 11-15 position proves
    equivalent to `Literal_P_neq_NP_V2`; and the V4 pivot proves
    `¬ Literal_P_neq_NP_V2` outright.  So conjunct (3) of the 11-15
    bundle is an implication whose hypothesis cannot hold.

    It is still a true theorem — nothing is withdrawn.  What this
    records is that it carries no information about P vs NP, which is
    precisely why conjunct (4) below moves to the V4 carrier. -/
theorem v2_faithfulness_premise_is_false :
    ¬ PF.SpectralGapFaithfulSeparator.SpectralSeparatorFaithfulness_V2 := by
  intro h
  have hiff :=
    PF.PrincipiaFractalisSubstratePositions.principia_fractalis_substrate_positions_at_HEAD.2.1.2.1
  exact PF.SpectralGapFaithfulSeparator_V4Pivot.v2_morning_attack_vacuous_disclosure (hiff.mp h)

/-! ## §2 — The nine-conjunct substrate positions capstone, v2 -/

/-- **`principia_fractalis_substrate_positions_v2_at_HEAD`** — every
axis carried in one theorem, at the honest strength each one actually
has at HEAD.

Nine conjuncts:

(1) **NS, superseded encoding** — `Clay_NavierStokes_Standard` over
    `PF_NSEncodingSubstrate` is equivalent to `True`.  The carrier is
    `Unit`, the admissibility hypothesis is `True`, and the conclusion
    is a free algebraic bound.  The gravestone, machine-checked, so it
    cannot drift back into a claim.

(2) **NS, faithful encoding** — `Clay_NavierStokes_Standard` over
    `PF_NSEncodingFaithful` is **equivalent to Fefferman's Clay
    statement**.  The equivalence is proved; neither side is asserted.
    This is the slot the 11-15 docstring promised and left empty.

(3) **YM** — α_YM grounded by the H₃ Coxeter number.

(4) **P vs NP, V4 carrier** — V2 vacuity disclosed (`¬ Literal_P_neq_NP_V2`),
    kernel-verified spectral gap, two *distinct* members of
    `class_P_typedV4` (so the V4 carrier is non-trivial, unlike V2),
    and the composition from the V4 faithful separator.  That premise
    is genuinely Clay-level: closing it would be solving P vs NP.

(5) **BSD** — α_NS = 2·α_BSD, anchor positivity, named-residual
    composition.

(6) **Hodge** — the golden-ratio identity, anchor positivity,
    named-residual composition.

(7) **RH** — σ(3/2) = 0, α_RH² = 9/4, named-residual composition.

(8) **Poincaré** — the typed contract, **and** the disclosure that its
    manifold carrier is `ℝ`.  Both in the same conjunct, so the
    contract is never read without the carrier.

(9) **Fermat** — the typed contract's vacuity (`↔ True`), **and** the
    two genuinely kernel-verified Fermat facts: mathlib's n = 4
    theorem and this project's difference form.

Framework-first position: ONE theorem, ONE citation, and each axis at
its real strength.  Every conjunct is discharged by a theorem already
proved elsewhere, on the three-axiom bar
`[propext, Classical.choice, Quot.sound]`.  No Clay problem is claimed
solved by any conjunct. -/
theorem principia_fractalis_substrate_positions_v2_at_HEAD :
    -- (1) NS — the superseded substrate contract is vacuous.
    (PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
        PF.Referee.NavierStokesCapstoneTypedBridgeSubstrate.PF_NSEncodingSubstrate ↔ True) ∧
    -- (2) NS — the faithful contract IS Fefferman's Clay statement.
    (PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
        PF.Referee.NavierStokesCapstoneDisclosure.PF_NSEncodingFaithful
      ↔ PF.NavierStokes.FeffermanFaithful.Clay_NavierStokes_ExistenceSmoothness_Fefferman2000_Faithful) ∧
    -- (3) YM via H₃.
    (PrincipiaTractalis.CrossMillenniumSharedInvariants.α_YM
      = Real.pi / (10 * (Real.pi / (PrincipiaFractalis.H3CoxeterOrigin.H3_Coxeter_number : ℝ))) + 1) ∧
    -- (4) P vs NP — V4 carrier, with the V2 vacuity disclosure alongside.
    ((¬ PrincipiaTractalis.PNPClassSeparationCarrierV2.Literal_P_neq_NP_V2) ∧
     (PrincipiaTractalis.spectral_gap > 0) ∧
     (PrincipiaTractalis.PNPClassSeparationCarrierV4.L_const_true
        ∈ PrincipiaTractalis.PNPClassSeparationCarrierV4.class_P_typedV4 ∧
      PrincipiaTractalis.PNPClassSeparationCarrierV4.L_const_false
        ∈ PrincipiaTractalis.PNPClassSeparationCarrierV4.class_P_typedV4 ∧
      PrincipiaTractalis.PNPClassSeparationCarrierV4.L_const_true
        ≠ PrincipiaTractalis.PNPClassSeparationCarrierV4.L_const_false) ∧
     (PF.SpectralGapFaithfulSeparator_V4Pivot.SpectralSeparatorFaithfulness_V4
        → PrincipiaTractalis.PNPClassSeparationCarrierV4.Literal_P_neq_NP_V4)) ∧
    -- (5) BSD substrate position.
    ((PrincipiaTractalis.CrossMillenniumSharedInvariants.α_NS
        = 2 * PrincipiaTractalis.CrossMillenniumSharedInvariants.α_BSD) ∧
     (0 < PrincipiaTractalis.CrossMillenniumSharedInvariants.α_BSD) ∧
     (PF.BSDSubstratePosition.BSDAnalyticRankMachinery_LMFDBFamily →
        PrincipiaTractalis.CrossMillenniumSharedInvariants.α_NS
          = 2 * PrincipiaTractalis.CrossMillenniumSharedInvariants.α_BSD)) ∧
    -- (6) Hodge substrate position.
    ((PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Hodge ^ 2
        = PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Hodge + 1) ∧
     (0 < PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Hodge) ∧
     (PF.HodgeSubstratePosition.HodgeHigherDimensionVoisinResidual →
        PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Hodge ^ 2
          = PrincipiaTractalis.CrossMillenniumSharedInvariants.α_Hodge + 1)) ∧
    -- (7) RH substrate position via σ.
    ((PrincipiaTractalis.SigmaAbscissa.sigma (3 / 2) = 0) ∧
     (PrincipiaTractalis.CrossMillenniumSharedInvariants.α_RH ^ 2 = 9 / 4) ∧
     (PF.RHSubstratePositionViaSigma.RH_FrontierExtensionViaSigmaResidual →
        PrincipiaTractalis.SigmaAbscissa.sigma (3 / 2) = 0)) ∧
    -- (8) Poincaré — typed contract AND the carrier disclosure.
    (PF.Referee.StandardPoincareStatement.Clay_Poincare_Standard
        PF.Referee.PoincareCapstoneTypedBridge.PF_PoincareEncoding ∧
     PF.Referee.PoincareCapstoneTypedBridge.PF_PoincareEncoding.SmoothThreeManifold = ℝ) ∧
    -- (9) Fermat — contract vacuity AND the two real kernel-verified cases.
    ((PF.Referee.StandardFermatStatement.Standard_FermatLastTheorem_Standard
        PF.Referee.FermatCapstoneTypedBridge.PF_FermatEncoding ↔ True) ∧
     (∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 2) ∧
     (∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 - b ^ 4 ≠ c ^ 2)) :=
  ⟨PF.Referee.NavierStokesCapstoneDisclosure.clay_standard_substrate_is_vacuous,
   PF.Referee.NavierStokesCapstoneDisclosure.clay_standard_faithful_iff,
   PF.YangMills.YMContinuumViaH3Scaling.α_YM_grounded_by_H3_Coxeter_number,
   PF.SpectralGapFaithfulSeparator_V4Pivot.substrate_P_neq_NP_V4_position_at_HEAD,
   PF.BSDSubstratePosition.substrate_BSD_position_at_HEAD,
   PF.HodgeSubstratePosition.substrate_Hodge_position_at_HEAD,
   PF.RHSubstratePositionViaSigma.substrate_RH_position_via_sigma_at_HEAD,
   ⟨PF.Referee.PoincareCapstoneTypedBridge.PF_Poincare_capstone_yields_Clay_Poincare_standard,
    PF.Referee.ToECapstoneVacuityDisclosure.poincare_encoding_manifold_type_is_real⟩,
   ⟨PF.Referee.ToECapstoneVacuityDisclosure.fermat_contract_is_vacuous,
    PF.Referee.FermatCapstoneTypedBridge.fermat_n_four_classically_kernel_verified,
    PF.Referee.FermatCapstoneTypedBridge.fermat_n_four_difference_form_kernel_verified⟩⟩

/-! ## §3 — Axiom audit.

The predecessor is cited, not superseded away: it still compiles and
still holds. -/

#check @PF.PrincipiaFractalisSubstratePositions.principia_fractalis_substrate_positions_at_HEAD
#check @principia_fractalis_substrate_positions_v2_at_HEAD

#print axioms PF.PrincipiaFractalisSubstratePositionsV2.v2_faithfulness_premise_is_false
#print axioms PF.PrincipiaFractalisSubstratePositionsV2.principia_fractalis_substrate_positions_v2_at_HEAD

end PF.PrincipiaFractalisSubstratePositionsV2
