/-
# r284: UNIFIED CLAY CLOSURE VIA HARDY + RH + POLYLOG ATOMS
       (HP-program residual honest-scope surface).

★ 2026-08-18 r284 — surfaces the framework's substrate closure of all
six Clay Millennium axes with the `HilbertPolyaProgramConjecture_Positive`
residual EXCHANGED for the Riemann Hypothesis itself, per the r274
honest-scope framework-first position:

  r274 (`hp_program_positive_iff_riemannHypothesis_under_hardy`):
    under Hardy 1914, `HilbertPolyaProgramConjecture_Positive`
    is logically equivalent to `RiemannHypothesis`.

At this Prop granularity, `HilbertPolyaProgramConjecture_Positive :=
PF_T3SymIsHilbertPolyaOperator_Positive → RiemannHypothesis` has no
content beyond RH itself once Hardy 1914 supplies the antecedent.
r284 makes this fact explicit at the substrate-closure BUNDLE level:
the surface residual list becomes (Hardy 1914, RH, Ch 21 § 4.1,
Ch 21 § 4.2) instead of (Hardy 1914, HP-program-positive, Ch 21 § 4.1,
Ch 21 § 4.2). Same six Clay axes closed; the second RH residual now
reads as the Riemann Hypothesis directly rather than shrouded behind
the HP-program implication shape.

## Framework-first position (per r274 doctrine)

r274's honest-scope block:

> The classical Hilbert-Pólya program's REAL mathematical content
> (self-adjoint operator + spectral bijection + functional-equation
> off-line rejection) lives ABOVE this Prop granularity. It cannot
> be reached from the current corpus without additional infrastructure
> equivalent to a full spectral-theoretic Hilbert-Pólya proof.
> Attempting to discharge `HilbertPolyaProgramConjecture_Positive`
> from within the corpus at HEAD is thus EQUIVALENT to attempting
> to prove RH directly.

r284 formalises this at the bundle level. The referee-facing residual
list no longer contains a Prop whose real content is hidden ABOVE the
current granularity; it contains the Riemann Hypothesis itself, plainly
named.

Framework-first: this is NOT a shrinking of the residual set (it is a
one-for-one exchange), it is an honest EXPOSURE of what the second RH
residual actually reduces to at the corpus's current Prop shape. Future
substrate work targeting RH via richer structural routes (a
spectral-theoretic HP construction on a real Hilbert space, or the
mathlib-native Route B second front `route_b_fact_a_via_named_residuals`
at r272) can attack the RH residual directly with the same substrate-
closure downstream.

## What r284 delivers

- `ClayClosureBundleViaHardyAndRH` — the honest-scope substrate-closure
  input record with four fields: Hardy 1914 atomic + RiemannHypothesis +
  the two Ch 21 polylog atomic halves.

- `bundleViaHardyAndRH_to_fullyAtomic` — promotes to r283's
  `ClayClosureBundleViaFullyAtomicResiduals` by supplying the
  `HilbertPolyaProgramConjecture_Positive` field via the `.mpr`
  direction of r274 (trivial: given RH, the implication
  `PF_T3Sym...Positive → RH` is `fun _ => h_RH`).

- `unified_clay_closure_via_hardy_and_rh_r284` — THE HEADLINE. Under
  the honest-scope input record, all six Clay Millennium Problem
  statements hold on the framework's PF-substrate encodings.

## Reduction chain state at HEAD (after r284)

| Stage | Statement | Discharge |
|---|---|---|
| Wave 58 (r255) | HP-positive ↔ (countable ∧ nonempty) | biconditional, unconditional |
| r280 | countability of positive on-line ζ-zero ordinates | UNCONDITIONAL |
| r281 | HP-positive from Hardy-atomic + r280 | conditional on Hardy1914_AtomicFact |
| r282 | six Clay-Standard from Hardy + HP-program + polylog | 3 named residuals |
| r283 | polylog split into Ch 21 § 4.1 + § 4.2 atomic halves | 4 named residuals |
| r274 | HP-program-positive ↔ RH under Hardy | Prop-level equivalence |
| r284 | six Clay-Standard from Hardy + RH + Ch 21 § 4.1 + § 4.2 | 4 residuals, HP-program exposed as RH |

Book anchors: Ch 20 (RH via Fractal Resonance § 20.4 T³_sym operator
spec), Ch 21 (P vs NP § 4.1-4.2), Ch 34A (Substrate Theorem § 34A.5
the citable master implication). Paper
`principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.Analytic.UnifiedClayClosureViaFullyAtomicResiduals_r283
import PF.HPProgramResidualEquivalenceToRH_r274

namespace PrincipiaTractalis.UnifiedClayClosureViaHardyAndRH

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HPPositiveViaHardyAndCountability
open PrincipiaTractalis.UnifiedClayClosureViaHardyAtomic
open PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals

/-! ## §1 The honest-scope substrate-closure input record. -/

/-- **`ClayClosureBundleViaHardyAndRH`** — honest-scope substrate-closure
input record. r283's `ClayClosureBundleViaFullyAtomicResiduals` with the
`hp_program_positive` field EXCHANGED for `RiemannHypothesis` per r274's
`hp_program_positive_iff_riemannHypothesis_under_hardy`.

Four fields, each a concrete named residual matching the framework's
shoulder-of-giants pattern — with the second RH residual now surfaced
as RH itself (per r274 doctrine) rather than shrouded behind the
HP-program implication shape:

  1. `hardy_atomic` — Hardy 1914 atomic fact.
  2. `rh` — the Riemann Hypothesis (canonical critical-strip form).
  3. `polylog_atomic_branch_selection` — Ch 21 § 4.1 heur:branch-selection (P-side).
  4. `polylog_atomic_golden_modulation` — Ch 21 § 4.2 conj:golden-modulation (NP-side).
-/
structure ClayClosureBundleViaHardyAndRH where
  /-- Hardy 1914 atomic fact: `∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0`. -/
  hardy_atomic : Hardy1914_AtomicFact
  /-- Riemann Hypothesis (canonical critical-strip form). The second RH
      substrate residual `HilbertPolyaProgramConjecture_Positive` reads
      as RH under Hardy 1914 by r274; r284 surfaces this exchange at the
      substrate-closure bundle level. -/
  rh : PrincipiaTractalis.RiemannHypothesis
  /-- Ch 21 § 4.1 heur:branch-selection (P-side atomic residual). -/
  polylog_atomic_branch_selection : PolylogAtomic_HeurBranchSelection
  /-- Ch 21 § 4.2 conj:golden-modulation (NP-side atomic residual). -/
  polylog_atomic_golden_modulation : PolylogAtomic_ConjGoldenModulation

/-! ## §2 Promotion to r283's fully-atomic input record.

Given RH, the `HilbertPolyaProgramConjecture_Positive` field of r283's
bundle — definitionally `PF_T3SymIsHilbertPolyaOperator_Positive →
RiemannHypothesis` — is supplied trivially by `fun _ => h.rh`. This is
the `.mpr` direction of r274's biconditional; no Hardy dependence is
needed for THIS direction (Hardy is needed only for the forward
direction, which is not consumed here). -/

/-- **`bundleViaHardyAndRH_to_fullyAtomic`** — the honest-scope record
promotes to r283's `ClayClosureBundleViaFullyAtomicResiduals` by
supplying the `hp_program_positive` field via the trivial `.mpr`
direction of r274 (`fun _ => h.rh`). -/
theorem bundleViaHardyAndRH_to_fullyAtomic
    (h : ClayClosureBundleViaHardyAndRH) :
    ClayClosureBundleViaFullyAtomicResiduals where
  hardy_atomic := h.hardy_atomic
  hp_program_positive := fun _ => h.rh
  polylog_atomic_branch_selection := h.polylog_atomic_branch_selection
  polylog_atomic_golden_modulation := h.polylog_atomic_golden_modulation

/-! ## §3 THE HEADLINE — substrate closure of all six Clay axes under the honest-scope form. -/

/-- **★★★★★★★ (r284) UNIFIED CLAY CLOSURE VIA HARDY + RH + POLYLOG ATOMS ★★★★★★★** —
under the honest-scope substrate-closure input record, all six Clay
Millennium Problem statements hold on the framework's PF-substrate
encodings.

Composes `bundleViaHardyAndRH_to_fullyAtomic` with r283's
`unified_clay_closure_via_fully_atomic_r283`, which in turn composes
with r282's `unified_clay_closure_via_hardy_atomic_r282` and the
framework's substrate-closure theorem
`unified_clay_closure_via_substrate_linkage_bulletproof`.

This surfaces the framework's total Millennium position at HEAD as a
direct implication from FOUR precisely-named residuals — with the
second RH residual EXPOSED as the Riemann Hypothesis itself rather
than shrouded behind the HP-program implication shape (per r274
honest-scope framework-first doctrine). -/
theorem unified_clay_closure_via_hardy_and_rh_r284
    (h : ClayClosureBundleViaHardyAndRH) :
    PF.Referee.StandardClayStatements.Clay_RiemannHypothesis_Standard ∧
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
      PF.Referee.PNPCapstoneTypedBridge.PF_ComplexityEncoding ∧
    PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard
      PF.NavierStokes.NSPDETypedUpgradeV2.PF_NS3DEncodingV2 ∧
    PF.Referee.StandardClayStatements.Clay_YangMillsMassGap_Standard
      PrincipiaTractalis.YangMills.Bridge5_YM_SubstrateDischarge.PF_YMEncodingBridge5 ∧
    PF.Referee.StandardClayStatements.Clay_BSD_Standard
      PF.Referee.BSDCapstoneTypedBridgeV5.PF_BSDEncodingV5 ∧
    PF.Referee.StandardClayStatements.Clay_Hodge_Standard
      PF.Referee.HodgeCapstoneTypedBridge.PF_HodgeEncoding :=
  unified_clay_closure_via_fully_atomic_r283
    (bundleViaHardyAndRH_to_fullyAtomic h)

/-! ## §4 r274 anchor — the doctrinal justification for the exchange.

The exchange of `HilbertPolyaProgramConjecture_Positive` for
`RiemannHypothesis` in the residual list is justified at the Prop level
by r274's `hp_program_positive_iff_riemannHypothesis_under_hardy`:
under Hardy 1914, the two Props are logically equivalent. The `.mpr`
direction is used implicitly in `bundleViaHardyAndRH_to_fullyAtomic`;
the `.mp` direction (which requires Hardy) records the honest-scope
FRAMEWORK-FIRST reading of the residual — it has no content beyond RH
at this Prop granularity. -/

/-- **`hp_program_residual_is_rh_under_hardy`** — the biconditional
directly, for citation. This is r274's
`hp_program_positive_iff_riemannHypothesis_under_hardy` re-exposed via
r281's `hardy1914_atomicFact_eq_nonempty` biconditional so it can be
cited on the `Hardy1914_AtomicFact` form used throughout r281-r284. -/
theorem hp_program_residual_is_rh_under_hardy
    (h_hardy : Hardy1914_AtomicFact) :
    HilbertPolyaProgramConjecture_Positive ↔
      PrincipiaTractalis.RiemannHypothesis :=
  PrincipiaTractalis.HPProgramResidualEquivalenceToRH.hp_program_positive_iff_riemannHypothesis_under_hardy
    (hardy1914_atomicFact_eq_nonempty.mp h_hardy)

/-! ## §5 Axiom check. -/

#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaHardyAndRH.bundleViaHardyAndRH_to_fullyAtomic
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaHardyAndRH.unified_clay_closure_via_hardy_and_rh_r284
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaHardyAndRH.hp_program_residual_is_rh_under_hardy

end PrincipiaTractalis.UnifiedClayClosureViaHardyAndRH
