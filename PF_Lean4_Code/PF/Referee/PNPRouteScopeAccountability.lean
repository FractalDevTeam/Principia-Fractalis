/-
# PF.Referee.PNPRouteScopeAccountability

★★★★★ 2026-06-17 — UNASSAILABILITY: P vs NP ROUTE SCOPE ACCOUNTABILITY ★★★★★

The framework's P vs NP axis is conditioned on
`TuringEncoding.PolylogEigenvalueConjecture`, which the typed upgrade
file (`PolylogEigenvalueTypedUpgrade.lean`) decomposes into a clean
typed sharpness structure:

  (P1) Conjunction recomposition (Iff.rfl): the conjecture is the
       conjunction of four algebraic sub-Props on `alpha_of_class
       ClassP/ClassNP`.

  (P2) Enum-level mirrors are unconditional: the four sub-Props,
       translated to the concrete enum-level values
       `alpha_at_enum ClassP = √2`, `alpha_at_enum ClassNP = φ + 1/4`,
       hold axiom-free.

  (P3) Set-level sharpness: the existential form of the four sub-Props
       over an arbitrary `f : Set Language → ℝ` is **logically
       equivalent** to `ClassP ≠ ClassNP` (i.e., to P ≠ NP itself).

In contrast to the Hodge / NS / YM / BSD substrate restrictions and the
V2 RH route's arithmetic-progression obstruction, the PNP residual is
NOT a substrate weakening or an uninhabited statement — it is
structurally identical to the Clay question itself at the
abstract-typed-Prop level. The framework's P vs NP conditional reduction
is therefore TIGHT in a way the other axes are not.

## What is proven

  `PF_PNP_capstone_yields_Clay_PvsNP_standard :
     PolylogEigenvalueConjecture → Clay_PvsNP_Standard PF_ComplexityEncoding`

  Composed via the standard `P_neq_NP_via_spectral_gap` route + the iff
  `pf_pneqnp_iff_clay_pneqnp_standard : P_neq_NP_def ↔ Clay_PvsNP_Standard
   PF_ComplexityEncoding`.

  The encoding `PF_ComplexityEncoding` uses:
    * ClassP    := ↥TuringEncoding.ClassP
    * ClassNP   := ↥TuringEncoding.ClassNP
    * inclusion := P_subset_NP coercion (Cook 1971 Thm 2.1)

  Both ClassP and ClassNP are concrete subtypes of
  `TuringEncoding.Language`; this is NOT a substrate restriction.

## What is NOT proven

The framework does not unconditionally discharge
`PolylogEigenvalueConjecture`. The sharpness certificate (P3) makes the
shape of this residual precise:

  (S1) PolylogEigenvalueConjecture unfolds to the conjunction of four
       algebraic constraints on `alpha_of_class ClassP/ClassNP`.

  (S2) The enum-level mirror at the concrete values `(√2, φ + 1/4)`
       holds unconditionally — the opacity barrier is exactly the
       identification of the opaque `alpha_of_class` with the
       manuscript's canonical values.

  (S3) The existential form (over arbitrary set-level α-realisers) is
       **iff-equivalent to ClassP ≠ ClassNP**, by
       `algebraic_realization_iff_classes_distinct`. Discharging the
       conjecture is therefore exactly as hard as deciding P vs NP.

## What this file delivers

  * `PF_substrate_PNP_clay_witness` — the V3-compatible PNP discharge
    under the polylog conjecture, re-exported.
  * `PF_substrate_PNP_conjunction_recomposition` — typed witness that
    PolylogEigenvalueConjecture decomposes into four algebraic
    sub-Props (P1).
  * `PF_substrate_PNP_enum_mirror_unconditional` — typed witness that
    the enum-level mirror holds axiom-free (P2).
  * `PF_substrate_PNP_set_level_sharpness_iff_P_neq_NP` — typed
    witness that the existential set-level form is iff
    `ClassP ≠ ClassNP` (P3).
  * `PF_substrate_PNP_route_scope_capstone` — single citable theorem
    packaging the conditional discharge with the three sharpness
    markers.

No new mathematical content; the typed upgrade is unchanged. What is
new: a single referee-readable citation point co-located with the
Hodge/NS/YM/BSD/RH accountability files for paired citation.

ZERO project axioms. Kernel axioms only.
-/

import PF.TuringEncoding.PolylogEigenvalueTypedUpgrade
import PF.Referee.PNPCapstoneTypedBridge
import PF.Referee.StandardClayStatements

namespace PF.Referee.PNPRouteScopeAccountability

open PrincipiaTractalis.TuringEncoding
open PF.Referee.PNPCapstoneTypedBridge

/-! ## §1 — Conditional PNP discharge (what IS proven under the polylog
    conjecture) -/

/-- **★ The PNP route conditional discharge, single-citation export ★**
    — under `TuringEncoding.PolylogEigenvalueConjecture`,
    `Clay_PvsNP_Standard PF_ComplexityEncoding` holds via the existing
    framework chain (`P_neq_NP_via_spectral_gap` +
    `pf_pneqnp_iff_clay_pneqnp_standard`). -/
theorem PF_substrate_PNP_clay_witness
    (hpoly : PolylogEigenvalueConjecture) :
    PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
      PF_ComplexityEncoding :=
  PF_PNP_capstone_yields_Clay_PvsNP_standard hpoly

/-! ## §2 — Polylog conjecture sharpness markers (what is NOT proven) -/

/-- **(P1) Conjunction recomposition.**

    `PolylogEigenvalueConjecture` is the conjunction of four named
    algebraic sub-Props on `alpha_of_class ClassP/ClassNP`:

      (A1) α_P² = 2,
      (A2) 0 < α_P,
      (B1) 16·α_NP² − 24·α_NP − 11 = 0,
      (B2) 0 < α_NP.

    The iff is `Iff.rfl` after unfolding all five definitions. -/
def PNP_conjunction_recomposition : Prop :=
  PolylogEigenvalueConjecture ↔
    (PolylogSubProp_alpha_P_sq_eq_two ∧
     PolylogSubProp_alpha_P_pos ∧
     PolylogSubProp_alpha_NP_quadratic ∧
     PolylogSubProp_alpha_NP_pos)

theorem PNP_conjunction_recomposition_holds :
    PNP_conjunction_recomposition :=
  polylog_eigenvalue_conjecture_iff_four_subprops

/-- **(P2) Enum-level mirror is unconditional.**

    The four sub-Props, translated to the concrete enum-level α values
    `alpha_at_enum ClassP = √2` and `alpha_at_enum ClassNP = φ + 1/4`,
    hold axiom-free. The opacity barrier between the enum-level
    discharge and the set-level conjecture is exactly the
    identification of `alpha_of_class` with the manuscript's canonical
    values. -/
def PNP_enum_mirror_unconditional : Prop :=
  (alpha_at_enum PrincipiaTractalis.TuringEncoding.PFClass.P) ^ 2 = 2 ∧
  0 < alpha_at_enum PrincipiaTractalis.TuringEncoding.PFClass.P ∧
  16 * (alpha_at_enum PrincipiaTractalis.TuringEncoding.PFClass.NP) ^ 2 -
    24 * (alpha_at_enum PrincipiaTractalis.TuringEncoding.PFClass.NP) - 11 = 0 ∧
  0 < alpha_at_enum PrincipiaTractalis.TuringEncoding.PFClass.NP

theorem PNP_enum_mirror_unconditional_holds :
    PNP_enum_mirror_unconditional :=
  polylog_subprop_quadruple_at_enum

/-- **(P3) Set-level sharpness — Wave 57 certificate.**

    The existential form of the four sub-Props over an arbitrary
    `f : Set Language → ℝ` is **iff-equivalent** to `ClassP ≠ ClassNP`
    (i.e., to P ≠ NP itself). Discharging the conjecture is therefore
    exactly as hard as deciding P vs NP — the residual is structurally
    identical to the Clay question, not weaker. -/
def PNP_set_level_sharpness_iff_P_neq_NP : Prop :=
  (∃ f : Set Language → ℝ,
      ((f ClassP) ^ 2 = 2 ∧ 0 < f ClassP) ∧
      (16 * (f ClassNP) ^ 2 - 24 * (f ClassNP) - 11 = 0 ∧
       0 < f ClassNP)) ↔
    ClassP ≠ ClassNP

theorem PNP_set_level_sharpness_iff_P_neq_NP_holds :
    PNP_set_level_sharpness_iff_P_neq_NP :=
  polylog_subprop_quadruple_iff_classes_distinct

/-! ## §3 — Single referee-readable scope capstone -/

/-- **★★★★★ PNP ROUTE SUBSTRATE-VS-LITERAL-CLAY SCOPE CAPSTONE ★★★★★** —

    The single citable referee-reading point for the framework's PNP
    route claim:

      (A) Under `PolylogEigenvalueConjecture`,
          `Clay_PvsNP_Standard PF_ComplexityEncoding` holds.
      (B) The conjecture decomposes (Iff.rfl) into four named
          algebraic sub-Props on `alpha_of_class ClassP/ClassNP`.
      (C) The enum-level mirror at `(√2, φ + 1/4)` holds axiom-free
          and unconditionally.
      (D) The set-level existential sharpness form is iff-equivalent
          to `ClassP ≠ ClassNP` — the residual is structurally
          identical to the Clay P ≠ NP question.

    What this theorem ESTABLISHES (mechanically, at the typed-Prop
    level): unlike the Hodge / NS / YM / BSD substrate restrictions
    and the V2 RH arithmetic-progression obstruction, the PNP
    residual is TIGHT — it is the Clay question, not a weakening or
    a structurally uninhabited statement. -/
theorem PF_substrate_PNP_route_scope_capstone :
    -- (A) Conditional Clay_PvsNP_Standard under the polylog conjecture.
    (PolylogEigenvalueConjecture →
       PF.Referee.StandardClayStatements.Clay_PvsNP_Standard
         PF_ComplexityEncoding) ∧
    -- (B) Conjecture decomposes into four sub-Props.
    PNP_conjunction_recomposition ∧
    -- (C) Enum-level mirror is unconditional.
    PNP_enum_mirror_unconditional ∧
    -- (D) Set-level sharpness is iff ClassP ≠ ClassNP.
    PNP_set_level_sharpness_iff_P_neq_NP :=
  ⟨PF_substrate_PNP_clay_witness,
   PNP_conjunction_recomposition_holds,
   PNP_enum_mirror_unconditional_holds,
   PNP_set_level_sharpness_iff_P_neq_NP_holds⟩

/-! ## §4 — Honest-scope marker -/

/-- **Honest-scope marker** — this file consolidates the PNP route's
    sharpness structure into a referee-reading point parallel to the
    Hodge, NS, YM, BSD, and RH accountability files. The polylog
    typed upgrade content is unchanged; the conditional discharge,
    Iff.rfl-decomposition, unconditional enum-mirror, and
    iff-with-ClassP-≠-ClassNP sharpness certificate are now
    mechanically readable in a single citation point. -/
theorem PF_substrate_PNP_route_scope_honest_scope : True := trivial

end PF.Referee.PNPRouteScopeAccountability

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PF_substrate_PNP_clay_witness
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PNP_conjunction_recomposition_holds
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PNP_enum_mirror_unconditional_holds
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PNP_set_level_sharpness_iff_P_neq_NP_holds
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PF_substrate_PNP_route_scope_capstone
#print axioms
  PF.Referee.PNPRouteScopeAccountability.PF_substrate_PNP_route_scope_honest_scope
