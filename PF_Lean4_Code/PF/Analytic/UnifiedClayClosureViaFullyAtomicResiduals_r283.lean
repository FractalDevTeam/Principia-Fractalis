/-
# r283: UNIFIED CLAY CLOSURE VIA FULLY-ATOMIC RESIDUALS
       (polylog atomic-pair split + composition into r282).

★ 2026-08-17 r283 — surfaces the framework's substrate closure of all
six Clay Millennium axes conditional on FOUR precisely-named atomic
residuals, replacing r282's compound `PolylogEigenvalueConjecture` field
with the two Chapter 21 manuscript-anchored halves:

  heur:branch-selection (Ch 21 §4.1) — the P-side arithmetic;
  conj:golden-modulation (Ch 21 §4.2) — the NP-side arithmetic.

## The substrate closure state at HEAD (prior)

r282's `unified_clay_closure_via_hardy_atomic_r282` reduces
`ClayClosureBundleBulletproof` to three residuals:

  1. `Hardy1914_AtomicFact` — Hardy 1914 atomic fact.
  2. `HilbertPolyaProgramConjecture_Positive` — HP program.
  3. `PolylogEigenvalueConjecture` — polylog eigenvalue conjecture.

The third residual is compound: it packs the P-side (`α_P² = 2` +
positivity) and the NP-side (`16α_NP² − 24α_NP − 11 = 0` + positivity)
into a single 2-tuple. Each half corresponds to one distinct
Chapter 21 manuscript anchor (heur:branch-selection for P,
conj:golden-modulation for NP); the framework's shoulder-of-giants
pattern (Hardy 1914 / Mayer 1991 / Perelman 2003 pattern) calls for
these to be presented as independently-citable atomic residuals.

## What r283 delivers

- `PolylogAtomic_HeurBranchSelection` — P-side atomic residual encoding
  the arithmetic content of Ch 21 heur:branch-selection.

- `PolylogAtomic_ConjGoldenModulation` — NP-side atomic residual
  encoding the arithmetic content of Ch 21 conj:golden-modulation.

- `polylog_iff_atomic_pair` — biconditional
  `PolylogEigenvalueConjecture ↔ (PolylogAtomic_HeurBranchSelection ∧
  PolylogAtomic_ConjGoldenModulation)`. Definitional; `Iff.rfl` after
  unfolding.

- `polylog_via_atomic_pair` — composition: the two atomic halves
  together yield `PolylogEigenvalueConjecture`.

- `ClayClosureBundleViaFullyAtomicResiduals` — the fully-atomic
  substrate-closure input record: four fields, each a concrete
  named atomic residual.

- `bundleViaFullyAtomic_to_hardyAtomic` — promotes the fully-atomic
  record to r282's `ClayClosureBundleViaHardyAtomic` via
  `polylog_via_atomic_pair`.

- `unified_clay_closure_via_fully_atomic_r283` — THE HEADLINE. Under
  the fully-atomic-form substrate-closure input record, all six Clay
  Millennium Problem statements hold on the framework's PF-substrate
  encodings. Composes with `unified_clay_closure_via_hardy_atomic_r282`.

## Framework position after r283

The framework's substrate closure at HEAD reads as a direct implication
from FOUR precisely-named atomic residuals to all six Clay Millennium
axes on their PF-substrate encodings:

  1. **Hardy 1914** — `∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0`
     (classical, proven 1914; anchor for `PF_T3SymIsHilbertPolyaOperator_Positive`).
  2. **HP-program positive** — `HilbertPolyaProgramConjecture_Positive`
     (the Hilbert-Pólya program's positive variant).
  3. **Ch 21 heur:branch-selection (P-side)** — `α_P² = 2 ∧ 0 < α_P`.
  4. **Ch 21 conj:golden-modulation (NP-side)** — `16α_NP² − 24α_NP − 11 = 0
     ∧ 0 < α_NP`.

The compound `PolylogEigenvalueConjecture` residual is now surfaced as
two independently-attackable atomic halves, each keyed to a single
distinct Chapter 21 manuscript anchor. This matches the r281/r282
shoulder-of-giants labelling discipline: every residual is a REAL Prop
whose classical/manuscript reference is precisely named.

Substrate closure via `unified_clay_closure_via_substrate_linkage_bulletproof`
continues to deliver all six Clay axes as ONE bundle. r283 makes the
input to that closure read at its most-decomposed referee-facing form
without fragmenting the closure itself.

Book anchors: Ch 20 (RH via Fractal Resonance, § 20.4 T³_sym operator
spec), Ch 21 (P vs NP, § 4.1 heur:branch-selection, § 4.2
conj:golden-modulation), Ch 34A (Substrate Theorem, § 34A.5 the citable
master implication). Paper
`principia_fractalis_alpha_skeleton_2026-07-13.pdf` § 6 Corollary 6.3.
-/

import PF.Analytic.UnifiedClayClosureViaHardyAtomic_r282
import PF.TuringEncoding.Operators

namespace PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals

open PrincipiaTractalis
open PrincipiaTractalis.TuringEncoding
open PrincipiaTractalis.HilbertPolyaIdentificationBulletproof
open PrincipiaTractalis.HPPositiveViaHardyAndCountability
open PrincipiaTractalis.UnifiedClayClosureViaHardyAtomic
open PF.Referee.UnifiedClayClosureLinkageBulletproof

/-! ## §1 The two Chapter-21-anchored atomic residuals. -/

/-- **`PolylogAtomic_HeurBranchSelection`** — P-side atomic residual
encoding the arithmetic content of Chapter 21 heur:branch-selection
(§ 4.1): the P-class self-adjointness equation `α_P² = 2` together
with the positivity / branch-selection `0 < α_P` that picks the
physical (positive) Riemann sheet yielding `α_P = √2` (equivalently
`π/(10√2)` for the ground-state resonance).

Concrete Prop: `(alpha_of_class ClassP)² = 2 ∧ 0 < alpha_of_class ClassP`.

Reference: Principia Fractalis, Chapter 21, Section 4.1
heur:branch-selection (branch-choice rule for the P-class Hamiltonian
ground state). The arithmetic content here is precisely the P-half of
`PolylogEigenvalueConjecture`. -/
def PolylogAtomic_HeurBranchSelection : Prop :=
  (alpha_of_class ClassP) ^ 2 = 2 ∧ 0 < alpha_of_class ClassP

/-- **`PolylogAtomic_ConjGoldenModulation`** — NP-side atomic residual
encoding the arithmetic content of Chapter 21 conj:golden-modulation
(§ 4.2): the NP-class self-adjointness golden-modulation quadratic
`16α_NP² − 24α_NP − 11 = 0` together with the positivity
`0 < α_NP` selecting the physical root `α_NP = (3 + 2√5)/4 = φ + 1/4`.

Concrete Prop: `16(alpha_of_class ClassNP)² − 24(alpha_of_class ClassNP)
− 11 = 0 ∧ 0 < alpha_of_class ClassNP`.

Reference: Principia Fractalis, Chapter 21, Section 4.2
conj:golden-modulation (unitary conjugacy `H_NP = U(φ) · H_P · U†(φ)`
pinning `α_NP = φ + 1/4` via the sine-ratio identity). The arithmetic
content here is precisely the NP-half of `PolylogEigenvalueConjecture`. -/
def PolylogAtomic_ConjGoldenModulation : Prop :=
  16 * (alpha_of_class ClassNP) ^ 2 - 24 * (alpha_of_class ClassNP) - 11 = 0 ∧
    0 < alpha_of_class ClassNP

/-! ## §2 Biconditional to `PolylogEigenvalueConjecture`.

The two atomic halves conjoined are definitionally equal to
`PolylogEigenvalueConjecture` — `Iff.rfl` after unfolding all three
Props. -/

/-- **`polylog_iff_atomic_pair`** — `PolylogEigenvalueConjecture` is the
conjunction of the two Chapter-21-anchored atomic halves. Definitional
biconditional after unfolding. -/
theorem polylog_iff_atomic_pair :
    PolylogEigenvalueConjecture ↔
      (PolylogAtomic_HeurBranchSelection ∧ PolylogAtomic_ConjGoldenModulation) := by
  unfold PolylogEigenvalueConjecture
    PolylogAtomic_HeurBranchSelection
    PolylogAtomic_ConjGoldenModulation
  exact Iff.rfl

/-- **`polylog_via_atomic_pair`** — the two atomic halves compose to
`PolylogEigenvalueConjecture`. -/
theorem polylog_via_atomic_pair
    (hP : PolylogAtomic_HeurBranchSelection)
    (hNP : PolylogAtomic_ConjGoldenModulation) :
    PolylogEigenvalueConjecture :=
  polylog_iff_atomic_pair.mpr ⟨hP, hNP⟩

/-- **`polylog_gives_heur_branch_selection`** — the compound polylog
conjecture yields the P-side atomic residual. -/
theorem polylog_gives_heur_branch_selection
    (h : PolylogEigenvalueConjecture) : PolylogAtomic_HeurBranchSelection :=
  (polylog_iff_atomic_pair.mp h).1

/-- **`polylog_gives_conj_golden_modulation`** — the compound polylog
conjecture yields the NP-side atomic residual. -/
theorem polylog_gives_conj_golden_modulation
    (h : PolylogEigenvalueConjecture) : PolylogAtomic_ConjGoldenModulation :=
  (polylog_iff_atomic_pair.mp h).2

/-! ## §3 The fully-atomic substrate-closure input record. -/

/-- **`ClayClosureBundleViaFullyAtomicResiduals`** — the substrate-closure
input record with the polylog residual split into its two
Chapter-21-anchored atomic halves.

Four fields, each a concrete named atomic residual matching the
framework's shoulder-of-giants pattern:

  1. `hardy_atomic` — Hardy 1914 atomic fact.
  2. `hp_program_positive` — Hilbert-Pólya program (positive variant).
  3. `polylog_atomic_branch_selection` — Ch 21 heur:branch-selection (P-side).
  4. `polylog_atomic_golden_modulation` — Ch 21 conj:golden-modulation (NP-side).
-/
structure ClayClosureBundleViaFullyAtomicResiduals where
  /-- Hardy 1914 atomic fact: `∃ t : ℝ, 0 < t ∧ riemannZeta ⟨1/2, t⟩ = 0`. -/
  hardy_atomic : Hardy1914_AtomicFact
  /-- Hilbert-Pólya program conjecture (positive variant). -/
  hp_program_positive : HilbertPolyaProgramConjecture_Positive
  /-- Ch 21 § 4.1 heur:branch-selection (P-side atomic residual). -/
  polylog_atomic_branch_selection : PolylogAtomic_HeurBranchSelection
  /-- Ch 21 § 4.2 conj:golden-modulation (NP-side atomic residual). -/
  polylog_atomic_golden_modulation : PolylogAtomic_ConjGoldenModulation

/-! ## §4 Promotion to r282's Hardy-atomic input record. -/

/-- **`bundleViaFullyAtomic_to_hardyAtomic`** — the fully-atomic record
promotes to r282's `ClayClosureBundleViaHardyAtomic` by composing the
two polylog atomic halves via `polylog_via_atomic_pair`. -/
theorem bundleViaFullyAtomic_to_hardyAtomic
    (h : ClayClosureBundleViaFullyAtomicResiduals) :
    ClayClosureBundleViaHardyAtomic where
  hardy_atomic := h.hardy_atomic
  rh_hp_program_positive := h.hp_program_positive
  pvsnp_polylog :=
    polylog_via_atomic_pair
      h.polylog_atomic_branch_selection
      h.polylog_atomic_golden_modulation

/-! ## §5 THE HEADLINE — substrate closure of all six Clay axes under the fully-atomic form. -/

/-- **★★★★★★ (r283) UNIFIED CLAY CLOSURE VIA FULLY-ATOMIC RESIDUALS ★★★★★★** —
under the fully-atomic-form substrate-closure input record, all six
Clay Millennium Problem statements hold on the framework's PF-substrate
encodings.

Composes `bundleViaFullyAtomic_to_hardyAtomic` with r282's
`unified_clay_closure_via_hardy_atomic_r282`, which in turn composes
with the framework's substrate-closure theorem
`unified_clay_closure_via_substrate_linkage_bulletproof`.

This surfaces the framework's total Millennium position at HEAD as a
direct implication from FOUR precisely-named atomic residuals to all
six Clay-Standard statements — with the P vs NP leg split into its
two independently-attackable Chapter-21-anchored halves. -/
theorem unified_clay_closure_via_fully_atomic_r283
    (h : ClayClosureBundleViaFullyAtomicResiduals) :
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
  unified_clay_closure_via_hardy_atomic_r282
    (bundleViaFullyAtomic_to_hardyAtomic h)

/-! ## §6 Axiom check. -/

#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals.polylog_iff_atomic_pair
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals.polylog_via_atomic_pair
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals.bundleViaFullyAtomic_to_hardyAtomic
#print axioms
  PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals.unified_clay_closure_via_fully_atomic_r283

end PrincipiaTractalis.UnifiedClayClosureViaFullyAtomicResiduals
