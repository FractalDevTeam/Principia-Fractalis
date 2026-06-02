/-
# PF.Referee.PNPCapstoneTypedBridge

**Date**: 2026-06-02
**Status**: typed-contract bridge for the P vs NP axis. No new analytic content.
**Anchor commit**: 7ee849e (parent d23b465 + a2fb8d2 + ee51039).
**Source roadmap**: `codex/MILLENNIUM_REFEREE_ROADMAP_2026-06-02.md`
"First Proof Attack: P vs NP" + "The Universal Proof Shape".

## Purpose

The 2026-06-02 referee roadmap names P vs NP as the flagship first
target:

> The best first target is P vs NP if the `alpha_of_class` semantics
> can be made standard and noncircular.

This module supplies the *wiring* between the existing PF capstone
`P_neq_NP_via_spectral_gap` and the typed standard Clay contract
`Clay_PvsNP_Standard`. The wiring is exact: this file constructs a
concrete `StandardComplexityEncoding` (`PF_ComplexityEncoding`) from
PF's Turing-machine-based `ClassP`/`ClassNP`, and shows that the PF
capstone's conclusion `P_neq_NP_def` is **logically equivalent** to
`Clay_PvsNP_Standard PF_ComplexityEncoding`.

This does NOT close the `alpha_of_class` opacity gap that the Wave 57
sharpness certificate identifies as Clay-equivalent. It makes the
shape standard so future work targeting `alpha_of_class` produces the
typed contract directly.

## What this module produces

* `PF_ComplexityEncoding : StandardComplexityEncoding` — the concrete
  PF encoding built from `↥TuringEncoding.ClassP` / `↥TuringEncoding.ClassNP`
  with the inclusion derived from `TuringEncoding.P_subset_NP`.
* `pf_pneqnp_iff_clay_pneqnp_standard` — `P_neq_NP_def ↔
  Clay_PvsNP_Standard PF_ComplexityEncoding`.
* `PF_PNP_capstone_yields_Clay_PvsNP_standard` — given the open
  `PolylogEigenvalueConjecture`, `Clay_PvsNP_Standard PF_ComplexityEncoding`
  holds.

## Honest scope

This module does NOT discharge P vs NP. The hypothesis
`PolylogEigenvalueConjecture` remains open and (per the Wave 57
sharpness certificate) closing it is equivalent to closing P vs NP.
The bridge only retypes the conclusion of the existing PF capstone to
the typed Clay contract.
-/

import PF.P_NP_Complete_Proof
import PF.P_NP_Equivalence
import PF.TuringEncoding.Complexity
import PF.Referee.StandardClayStatements

namespace PF.Referee.PNPCapstoneTypedBridge

open PrincipiaTractalis

/-! ## §1 — A concrete standard-encoding instance from PF's Turing-machine types -/

/-- The standard complexity encoding constructed from PF's
    `TuringEncoding.ClassP` / `ClassNP`. `ClassP` and `ClassNP` are
    realized as subtypes of `TuringEncoding.Language`, and the
    inclusion is the natural P ⊆ NP coercion derived from
    `TuringEncoding.P_subset_NP` (Cook 1971 Theorem 2.1: a P decider
    yields an NP verifier by ignoring the certificate). -/
def PF_ComplexityEncoding :
    PF.Referee.StandardClayStatements.StandardComplexityEncoding where
  ClassP  := ↥TuringEncoding.ClassP
  ClassNP := ↥TuringEncoding.ClassNP
  inclusion := fun ⟨L, hP⟩ => ⟨L, TuringEncoding.P_subset_NP hP⟩

/-! ## §2 — Equivalence of PF's `P_neq_NP_def` and the typed Clay contract -/

/-- **P_neq_NP_def ↔ Clay_PvsNP_Standard PF_ComplexityEncoding.**

    PF's `P_neq_NP_def := ¬ (∀ L, InClassNP L → InClassP L)` is the
    standard "P ≠ NP" statement: there exists a language in NP not in P.

    The typed Clay statement
    `Clay_PvsNP_Standard PF_ComplexityEncoding :=`
    `¬ Function.Surjective PF_ComplexityEncoding.inclusion` is
    logically equivalent because:

    * Surjectivity of the inclusion subtype map ↔ every NP language
      sits in P ↔ `P_equals_NP_def`.
    * Negation matches `P_neq_NP_def`.

    Hence the typed Clay form is **the same Clay statement** as PF's
    internal `P_neq_NP_def`, just re-encoded against an external
    encoding. No `alpha_of_class` content moves through this iff. -/
theorem pf_pneqnp_iff_clay_pneqnp_standard :
    P_neq_NP_def ↔
      PF.Referee.StandardClayStatements.Clay_PvsNP_Standard PF_ComplexityEncoding := by
  unfold P_neq_NP_def P_equals_NP_def
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
  constructor
  · -- (→) ¬(∀L, InNP L → InP L) → ¬Surjective
    intro h_notInclusion h_surj
    apply h_notInclusion
    -- Show ∀ L, InClassNP L → InClassP L using surjectivity.
    intro L h_NP
    -- ⟨L, h_NP⟩ : ↥ClassNP. Find preimage in ↥ClassP.
    obtain ⟨⟨L', h_P⟩, h_eq⟩ := h_surj ⟨L, h_NP⟩
    -- h_eq : inclusion ⟨L', h_P⟩ = ⟨L, h_NP⟩
    -- inclusion just preserves the underlying Language, so L' = L.
    have h_under : L' = L := by
      have := congrArg Subtype.val h_eq
      exact this
    -- Now h_P : L' ∈ ClassP, and L' = L, so L ∈ ClassP, i.e. InClassP L.
    have : L ∈ TuringEncoding.ClassP := h_under ▸ h_P
    exact this
  · -- (←) ¬Surjective → ¬(∀L, InNP L → InP L)
    intro h_notSurj h_inclusion
    apply h_notSurj
    -- Build surjectivity from the inclusion ∀ L, InNP L → InP L.
    intro ⟨L, h_NP⟩
    -- h_inclusion : ∀ L, InClassNP L → InClassP L, so h_inclusion L h_NP gives InClassP L.
    have h_P : L ∈ TuringEncoding.ClassP := h_inclusion L h_NP
    refine ⟨⟨L, h_P⟩, ?_⟩
    -- Show PF_ComplexityEncoding.inclusion ⟨L, h_P⟩ = ⟨L, h_NP⟩.
    -- By Subtype.ext, suffices the underlying values agree, which they do.
    apply Subtype.ext
    rfl

/-! ## §3 — Capstone: typed bridge for the existing PF P≠NP capstone -/

/-- **PF P ≠ NP capstone yields the typed standard Clay contract.**

    Identical hypothesis to `P_neq_NP_via_spectral_gap`
    (PF/P_NP_Complete_Proof.lean): the
    `PolylogEigenvalueConjecture` named open Prop. Conclusion is
    `Clay_PvsNP_Standard PF_ComplexityEncoding` instead of
    `P_neq_NP_def`. Proof is the existing capstone applied followed
    by the iff. -/
theorem PF_PNP_capstone_yields_Clay_PvsNP_standard
    (hpoly : TuringEncoding.PolylogEigenvalueConjecture) :
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard PF_ComplexityEncoding :=
  pf_pneqnp_iff_clay_pneqnp_standard.mp (P_neq_NP_via_spectral_gap hpoly)

/-- **The single open analytic frontier (Wave 57 sharpness).** Names
    the hypothesis of the above capstone that remains open at HEAD
    7ee849e: `TuringEncoding.PolylogEigenvalueConjecture`. Per Wave 57,
    discharging this Prop is equivalent to deciding P vs NP. -/
def PNP_OpenFrontier : Prop :=
  TuringEncoding.PolylogEigenvalueConjecture

#check @PF_ComplexityEncoding
#check @pf_pneqnp_iff_clay_pneqnp_standard
#check @PF_PNP_capstone_yields_Clay_PvsNP_standard
#check @PNP_OpenFrontier

end PF.Referee.PNPCapstoneTypedBridge
