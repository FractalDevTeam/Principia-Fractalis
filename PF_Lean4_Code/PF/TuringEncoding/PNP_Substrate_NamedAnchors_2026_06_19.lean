/-
# PF.TuringEncoding.PNP_Substrate_NamedAnchors_2026_06_19

2026-06-19 — Eight bibliographic citation markers naming the published
sources of the framework's P-vs-NP axis substrate closure. Rewritten
2026-11-06 to remove the free-discharge pattern — see Hodge NamedAnchors
cleanup `c98e5b90` for the method and rationale.

## What this file is

Eight `Prop := True` definitions that NAME specific published-mathematics
sources the framework's PNP-axis substrate closure cites. They are
bibliographic markers, not mathematical content predicates.

  - Cobham 1965 (Logic, Methodology, and Philosophy of Science II,
    24-30, North-Holland): polynomial-time class definition.
  - Edmonds 1965 (Canadian J. Math. 17:449-467): efficient computation
    and the polynomial-time threshold.
  - Cook 1971 (STOC '71: 151-158): NP-completeness of SAT.
  - Karp 1972 (Complexity of Computer Computations, 85-103, Plenum):
    twenty-one NP-complete problems.
  - Baker-Gill-Solovay 1975 (SIAM J. Comput. 4:431-442): relativization
    barrier.
  - Razborov-Rudich 1997 (JCSS 55:24-35): natural-proof barrier.
  - Sipser 2000 (Clay Math. Inst.): Clay problem statement.
  - Aaronson-Wigderson 2009 (ACM TOCT 1:1-54): algebrization barrier.

## What was removed on 2026-11-06

  `theorem <lowercase>_anchor_holds : <Anchor> := trivial` × 8
  disjunction + conjunction bundles with their `_holds` theorems
  PNP phase-1 audit-trail capstone

All type-reduce to `True`. Removed for the same reason as the Hodge /
RH / NS / YM NamedAnchors cleanups.

## Where the real PNP content is

  - `PF.TuringEncoding.AlphaCanonical`, `.AlphaRealizationNoGo`,
    `.Operators` — the typed α-canonical / no-go / operator content.
  - `PF.PNP_FrameworkMillenniumAnswer` — the framework's measured
    position on Clay PNP.
  - Per MEMORY `principia_2026-11-05_hp_rework_restate_handoff.md`:
    the bare `P_NEQ_NP` has never been kernel-checked and cannot be
    (measured, not inferred). `P_NP_Axiom_Elimination.lean` retired
    out of `PF/`.
  - `PF.PNP_Wave56CrossGaloisLockAttempt`, `PF.PolylogConjectureAttemptWave47`
    — the Wave 55/56/57 cross-Galois lock chain.

## Scope

Bibliographic. The eight `Prop := True` defs are kept because
externally-referenced master-capstones name them as citation markers.

## Axiom budget

Zero project axioms. The file now contains no theorems.
-/

namespace PF.TuringEncoding.PNP_Substrate_NamedAnchors_2026_06_19

/-- **Cobham 1965 citation marker.** Cobham, A., "The intrinsic
    computational difficulty of functions.", in *Logic, Methodology,
    and Philosophy of Science II*, 24-30, North-Holland, 1965.
    Bibliographic reference. -/
def Cobham1965_PolynomialTimeClass_Anchor : Prop := True

/-- **Edmonds 1965 citation marker.** Edmonds, J., "Paths, trees, and
    flowers.", Canadian J. Math. 17 (1965), 449-467.
    Bibliographic reference. -/
def Edmonds1965_EfficientComputation_Anchor : Prop := True

/-- **Cook 1971 citation marker.** Cook, S.A., "The complexity of
    theorem-proving procedures.", STOC '71 Proc. 3rd Annual ACM
    Symposium on Theory of Computing (1971), 151-158.
    Bibliographic reference. -/
def Cook1971_NPCompletenessSAT_Anchor : Prop := True

/-- **Karp 1972 citation marker.** Karp, R.M., "Reducibility among
    combinatorial problems.", in *Complexity of Computer Computations*,
    85-103, Plenum, 1972. Bibliographic reference. -/
def Karp1972_TwentyOneNPComplete_Anchor : Prop := True

/-- **Baker-Gill-Solovay 1975 citation marker.** Baker, T., Gill, J.,
    and Solovay, R., "Relativizations of the P =? NP question.",
    SIAM J. Comput. 4 (1975), 431-442. Bibliographic reference. -/
def BakerGillSolovay1975_RelativizationBarrier_Anchor : Prop := True

/-- **Razborov-Rudich 1997 citation marker.** Razborov, A.A. and
    Rudich, S., "Natural proofs.", J. Comput. System Sci. 55 (1997),
    24-35. Bibliographic reference. -/
def RazborovRudich1997_NaturalProofBarrier_Anchor : Prop := True

/-- **Sipser 2000 citation marker.** Sipser, M., "The history and
    status of the P versus NP question.", Clay Mathematics Institute
    Millennium Prize Problems, 2000. Bibliographic reference. -/
def Sipser2000_ClayPNPStatement_Anchor : Prop := True

/-- **Aaronson-Wigderson 2009 citation marker.** Aaronson, S. and
    Wigderson, A., "Algebrization: a new barrier in complexity theory.",
    ACM Transactions on Computation Theory 1 (2009), 1-54.
    Bibliographic reference. -/
def AaronsonWigderson2009_AlgebrizationBarrier_Anchor : Prop := True

end PF.TuringEncoding.PNP_Substrate_NamedAnchors_2026_06_19
