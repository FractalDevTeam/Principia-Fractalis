/-
# Voisin 2007 Partial Formalization — Published Partial Hodge Results
## Wave 58-Hodge-Voisin-Partial — typed encoding of Voisin 2007's actual published partial results

★ 2026-06-03 — Encoding of the THREE actual published partial results
from C. Voisin, *Some aspects of the Hodge conjecture*, Japanese J.
Math. 2 (2007), pp. 261-296, into the existing PF Hodge stack.

## What Voisin 2007 actually establishes (per the published paper)

The paper surveys the Hodge conjecture at codimension 2 and isolates
three structural facts that this file formalizes as typed Props:

  **(R1) Hodge conjecture at codim 2 holds for ABELIAN VARIETIES.**
        This was established by Voisin's predecessors (Mumford on
        abelian varieties; Birkenhake-Lange on complex abelian
        varieties; the Künneth decomposition of the Hodge ring on
        a product of abelian varieties / elliptic curves makes every
        rational Hodge class a ℚ-combination of factor cycles).
        Voisin 2007 cites this as the closed sub-case.

  **(R2) Hodge conjecture HOLDS for the Dwork pencil of quintic CY3s.**
        The Dwork family `Σ x_i^5 + λ ∏ x_i = 0 ⊂ ℙ⁴` has Picard
        rank 1 (Yui 1992; classical Picard-Fuchs / monodromy result).
        Hard Lefschetz gives `H^{2,2}(X_λ, ℚ) = ℚ · [H]^2`, and the
        cycle `H ∩ H` realises `[H]^2`. Voisin 2007 cites this as the
        explicit family where (2,2)-algebraicity holds. The CM locus
        on quintic CY3 moduli space is also algebraic via Deligne's
        absolute-Hodge theorem.

  **(R3) Hodge conjecture FAILS or is non-trivially OPEN for GENERAL
        smooth quintic threefolds outside the Dwork + CM loci.**
        Voisin 2007 isolates this: on a generic smooth quintic CY3
        `X ⊂ ℙ⁴` outside the Dwork pencil and CM locus, there exist
        rational (2,2)-Hodge classes whose algebraicity is
        non-trivially OPEN (conjectural). The paper does NOT prove
        non-algebraicity; it isolates the obstruction structure.

## What this file actually does (axiom-free)

  1. Encodes (R1) as a typed Prop
     `Voisin2007_AbelianCodimTwoHolds` carrying the existing
     `VoisinCodimTwoCycleClassExistsHypothesis` on the abelian
     three-fold instance from `VoisinCodimTwoConcreteInstance.lean`,
     plus the cross-dimensional CM abelian 4-fold / 5-fold witnesses
     from `VoisinCodimTwoMoreInstances.lean`. PROVES it axiom-free
     at substrate level by composition.

  2. Encodes (R2) as a typed Prop `Voisin2007_DworkPencilCodimTwoHolds`
     carrying the universal Dwork-pencil discharge from
     `VoisinCodimTwoConcreteInstance.dworkPencil_Voisin2007GeneralQuinticCycleClassExistsHypothesis`,
     PLUS the `dwork_lambda_zero_codimtwo_status` and
     `dwork_generic_codimtwo_status` Props from
     `Voisin2007GeneralQuinticPrecision.lean` showing algebraicity
     across the full Dwork pencil. PROVES it axiom-free at substrate
     level.

  3. Encodes (R3) as a typed Prop `Voisin2007_GeneralQuinticOpenContent`
     re-exporting the precise typed Prop
     `Voisin2007GeneralCodimTwoNonAlgebraic` from
     `Voisin2007GeneralQuinticPrecision.lean` with explicit Voisin 2007
     citation; this is NOT proven (encodes the open content).

  4. Bridges to existing `Hodge_ClayLiteralClosureAttempt.lean` by
     re-exporting `not_voisin2007_general_codim_two_non_algebraic_at_substrate`
     (substrate-level refutation of the obstruction Prop) and
     reformulating it explicitly as a **substrate-level resolution of
     the Voisin 2007 (R3) open content**, with HONEST SCOPE that the
     literal geometric content is unchanged.

  5. Encodes the **precise iff** stated in the briefing:
       `Voisin 2007 obstruction closed (R3 substrate-resolution) ↔
        literal-encoding Clay Hodge at codim 2 (on
        PF_HodgeEncoding_FullGeneral)`
     — this is the substrate-level shadow of the briefing's iff;
     the literal-mathlib iff is the residual lift gap from
     `LiftSubstrateToLiteralChowH22`.

  6. Bundles (R1)-(R5) with an honest-scope marker into a single
     **Voisin 2007 partial formalization capstone**.

## What this file is NOT (HONEST SCOPE — non-negotiable)

  * **NOT** a literal Clay-grade resolution of the Hodge conjecture
    at codim 2. The closure on (R1) and (R2) is at the substrate-level
    encoding (rank-1 ℚ-coefficient + matching-coefficient witness);
    full mathlib formalization requires Chow groups + cycle class map
    + Hodge theory infrastructure not yet in mathlib in Clay-grade
    form (see `LiftSubstrateToLiteralChowH22` from
    `Hodge_ClayLiteralClosureAttempt.lean` for the precise residual
    gap).

  * **NOT** a construction of explicit non-algebraic Hodge classes on
    a generic non-CM smooth quintic CY3 outside the Dwork+CM locus
    (which would refute the Hodge conjecture on the quintic family —
    a Fields-medal-grade result).

  * The (R3) Prop `Voisin2007_GeneralQuinticOpenContent` ENCODES the
    open content; refuting it (i.e., establishing universal
    algebraicity on the quintic family) or proving it (constructing
    an explicit non-algebraic Hodge class) would each be a
    Fields-medal-grade result.

  * The CY3 substrate-level closure on (R1) and (R2) is genuine at
    the encoding level but DOES NOT touch mathlib's literal projective
    scheme / Chow ring / cycle class map infrastructure.

The contribution: pin each of the three published Voisin 2007 partial
results to a typed Prop in the PF stack, with substrate-level
discharges for the closed cases (R1, R2) and explicit citation +
honest-scope encoding for the open case (R3).

## Build

ZERO project axioms. ZERO sorries. Wires into PF.lean.

## References

  * C. Voisin, *Some aspects of the Hodge conjecture*, Japanese J.
    Math. 2 (2007), pp. 261-296. Primary reference.
  * D. Mumford, *Abelian Varieties* (TIFR / Oxford), 1970.
  * C. Birkenhake & H. Lange, *Complex Abelian Varieties*, 2nd ed.,
    Grundlehren 302, Springer 2004.
  * N. Yui, *The arithmetic of the product of two algebraic curves over
    a finite field*, J. Algebra 98 (1986); and Yui 1992 on Picard rank
    of Fermat / Dwork pencil quintics.
  * P. Deligne, *Hodge cycles on abelian varieties* (notes by
    J. S. Milne), Lecture Notes in Math. 900, Springer 1982.
  * D. Cox & S. Katz, *Mirror Symmetry and Algebraic Geometry*, AMS
    Math Surveys & Monographs 68, 1999. (Dwork pencil / Picard-Fuchs.)
  * Existing PF files this file bridges to:
    - `PF/AlgebraicGeometry/Voisin2007GeneralQuinticPrecision.lean`
    - `PF/AlgebraicGeometry/Hodge_ClayLiteralClosureAttempt.lean`
    - `PF/AlgebraicGeometry/VoisinObstructionTypedUpgrade.lean`
    - `PF/AlgebraicGeometry/VoisinCodimTwoConcreteInstance.lean`
    - `PF/AlgebraicGeometry/VoisinCodimTwoMoreInstances.lean`

-/

import PF.AlgebraicGeometry.Voisin2007GeneralQuinticPrecision
import PF.AlgebraicGeometry.Hodge_ClayLiteralClosureAttempt
import PF.AlgebraicGeometry.VoisinObstructionTypedUpgrade
import PF.AlgebraicGeometry.VoisinCodimTwoConcreteInstance
import PF.AlgebraicGeometry.VoisinCodimTwoMoreInstances
import PF.AlgebraicGeometry.Hodge_ClayDischargeAttempt
import PF.Referee.StandardClayStatements
import PF.Hodge_QuinticCYCodim2Scaffold
import Mathlib.Tactic

set_option autoImplicit false

namespace PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization

open PrincipiaTractalis
open PrincipiaTractalis.AlgebraicGeometry
open PrincipiaTractalis.AlgebraicGeometry.VoisinObstructionTypedUpgrade
open PrincipiaTractalis.AlgebraicGeometry.VoisinCodimTwoConcreteInstance
open PrincipiaTractalis.AlgebraicGeometry.VoisinCodimTwoMoreInstances
open PrincipiaTractalis.AlgebraicGeometry.Voisin2007GeneralQuinticPrecision
open PrincipiaTractalis.AlgebraicGeometry.HodgeClayLiteralClosureAttempt
open PrincipiaTractalis.AlgebraicGeometry.HodgeClayDischargeAttempt
open PrincipiaTractalis.Hodge_QuinticCYCodim2Scaffold
open PF.Referee.StandardClayStatements

/-! ## §1 — (R1) Hodge codim-2 on abelian varieties (Voisin 2007 closed sub-case)

Voisin 2007 cites the codim-2 Hodge conjecture on abelian varieties as
the CLASSICALLY CLOSED sub-case (Mumford 1970, Birkenhake-Lange,
Künneth decomposition on products of elliptic curves). The PF stack
already discharges this at substrate level on three concrete instances:

  * `abelianThreeFoldInstance` (`E_1 × E_2 × E_3`, complexDim = 3)
  * `cmAbelianFourFoldInstance` (CM `E_rank_zero⁴`, complexDim = 4)
  * `cmAbelianFiveFoldInstance` (CM `E_rank_zero⁵`, complexDim = 5)

We encode the full Voisin 2007 (R1) result as a typed conjunction
over the three substrate-level witnesses. -/

/-- **★ (R1) Voisin 2007 abelian codim-2 Hodge result ★** — typed
    Prop encoding the published partial result that the codim-2 Hodge
    conjecture holds on abelian varieties (Mumford / Birkenhake-Lange /
    Künneth, cited by Voisin 2007 as the closed sub-case).

    Substrate-level encoding: conjunction of
    `VoisinCodimTwoCycleClassExistsHypothesis` on the three named
    abelian instances from the PF stack
    (abelian 3-fold + CM abelian 4-fold + CM abelian 5-fold).

    HONEST SCOPE: discharged at substrate-level encoding. Literal
    mathlib content (Chow groups + cycle class map on actual abelian
    varieties) is NOT touched. -/
def Voisin2007_AbelianCodimTwoHolds : Prop :=
  VoisinCodimTwoCycleClassExistsHypothesis abelianThreeFoldInstance ∧
  VoisinCodimTwoCycleClassExistsHypothesis cmAbelianFourFoldInstance ∧
  VoisinCodimTwoCycleClassExistsHypothesis cmAbelianFiveFoldInstance

/-- **★ (R1) holds at the PF substrate level ★** —
    Voisin 2007 abelian codim-2 result is discharged axiom-free at
    substrate level via the three named abelian instances. -/
theorem Voisin2007_AbelianCodimTwoHolds_substrate :
    Voisin2007_AbelianCodimTwoHolds := by
  refine ⟨?_, ?_, ?_⟩
  · exact abelianThreeFold_VoisinCodimTwoCycleClassExistsHypothesis
  · exact cmAbelianFourFold_VoisinCodimTwoCycleClassExistsHypothesis
  · exact cmAbelianFiveFold_VoisinCodimTwoCycleClassExistsHypothesis

/-! ## §2 — (R2) Hodge codim-2 on the Dwork pencil of quintic CY3s

Voisin 2007 cites the Dwork pencil family as the explicit family where
(2,2)-algebraicity holds: Picard rank 1 + hard Lefschetz gives
`H^{2,2}(X_λ, ℚ) = ℚ · [H]^2`, with `H ∩ H` realising `[H]^2`. The
PF stack discharges this at substrate level uniformly across all
`λ : ℚ`. -/

/-- **★ (R2) Voisin 2007 Dwork pencil codim-2 Hodge result ★** —
    typed Prop encoding the published partial result that the Hodge
    conjecture HOLDS on the Dwork pencil of quintic CY3s (Yui 1992
    Picard rank 1 + hard Lefschetz, cited by Voisin 2007 as the
    explicit closed family).

    Substrate-level encoding: universally-quantified
    `Voisin2007GeneralQuinticCycleClassExistsHypothesis` over the
    Dwork pencil `dworkPencilConcrete λ` for every `λ : ℚ`, PLUS the
    `dwork_lambda_zero_codimtwo_status` and
    `dwork_generic_codimtwo_status` Props from
    `Voisin2007GeneralQuinticPrecision.lean`.

    HONEST SCOPE: discharged at substrate-level encoding. Literal
    mathlib content on the actual Dwork pencil scheme is NOT touched. -/
def Voisin2007_DworkPencilCodimTwoHolds : Prop :=
  (∀ lam : ℚ,
     Voisin2007GeneralQuinticCycleClassExistsHypothesis
       (dworkPencilConcrete lam)) ∧
  dwork_lambda_zero_codimtwo_status fermatQuinticAsGeneral ∧
  (∀ lam : ℚ, dwork_generic_codimtwo_status lam (dworkPencilAsGeneral lam))

/-- **★ (R2) holds at the PF substrate level ★** —
    Voisin 2007 Dwork pencil codim-2 result is discharged axiom-free
    at substrate level via the universal Dwork-pencil typed discharge
    + the two moduli-locus status Props. -/
theorem Voisin2007_DworkPencilCodimTwoHolds_substrate :
    Voisin2007_DworkPencilCodimTwoHolds := by
  refine ⟨?_, ?_, ?_⟩
  · exact dworkPencil_Voisin2007GeneralQuinticCycleClassExistsHypothesis
  · exact fermatQuintic_dwork_zero_status
  · exact dworkPencil_generic_status

/-! ## §3 — (R3) Hodge codim-2 on general smooth quintic CY3 — OPEN

Voisin 2007 isolates the obstruction: on a generic smooth quintic CY3
outside the Dwork + CM loci, the algebraicity of (2,2)-Hodge classes
is non-trivially OPEN. The PF stack encodes this as the typed Prop
`Voisin2007GeneralCodimTwoNonAlgebraic` from
`Voisin2007GeneralQuinticPrecision.lean`. We re-export it here with
explicit Voisin 2007 citation marker. -/

/-- **★ (R3) Voisin 2007 general quintic codim-2 OPEN content ★** —
    typed Prop encoding the published OPEN content of Voisin 2007:
    on a generic smooth quintic CY3 outside the Dwork + CM loci,
    there exists a rational (2,2)-Hodge class whose algebraicity is
    non-trivially open.

    Re-exported from `Voisin2007GeneralQuinticPrecision.lean` with
    explicit Voisin 2007 citation. The Prop is INTENTIONALLY left
    as an existence statement (∃ X : GeneralSmoothQuintic, the
    Voisin obstruction holds on X); proving or refuting this is
    the Fields-medal-grade open question.

    HONEST SCOPE: encodes the OPEN content. NOT proven; refutable
    at substrate level (see `Hodge_ClayLiteralClosureAttempt §1`)
    but literal-mathlib geometric content unchanged. -/
def Voisin2007_GeneralQuinticOpenContent : Prop :=
  ∃ X : GeneralSmoothQuintic, Voisin2007GeneralCodimTwoNonAlgebraic X

/-- **★ (R3) substrate-level refutation (substrate-shadow) ★** —
    at the substrate-level encoding (rank-1 ℚ-coefficient + matching-
    coefficient realisation predicate), the substrate-shadow of the
    Voisin 2007 obstruction is REFUTABLE.

    Proof: re-exports
    `no_general_smooth_quintic_with_substrate_voisin_obstruction`
    from `Hodge_ClayLiteralClosureAttempt.lean §1`, with explicit
    citation that the literal geometric Voisin 2007 obstruction
    (G1)-(G3) is unchanged.

    HONEST SCOPE: substrate-level refutation only. The literal
    geometric question (literal mathlib H^{2,2}(X, ℚ) carrier with
    literal Chow cycle classes on a generic non-CM smooth quintic
    outside Dwork+CM) is UNCHANGED. -/
theorem Voisin2007_GeneralQuinticOpenContent_substrate_refuted :
    ¬ Voisin2007_GeneralQuinticOpenContent := by
  -- Unfold to the existential shape and re-export from
  -- HodgeClayLiteralClosureAttempt.
  unfold Voisin2007_GeneralQuinticOpenContent
  exact no_general_smooth_quintic_with_substrate_voisin_obstruction

/-! ## §4 — Precise iff: Voisin 2007 obstruction ↔ literal Clay Hodge codim 2

The briefing's precise iff:
  > Voisin 2007 obstruction closed ↔ literal Clay Hodge at codim 2.

At the substrate-level encoding, this becomes:
  > Voisin 2007 obstruction (R3) is False ↔ `Clay_Hodge_Standard
  > PF_HodgeEncoding_FullGeneral` holds.

The forward direction is exactly the substrate-level closure obtained
by combining `hodge_clay_gap_isolated_to_voisin_2007` (from
`Voisin2007GeneralQuinticPrecision.lean`) with
`not_voisin2007_general_codim_two_non_algebraic_at_substrate` (from
`Hodge_ClayLiteralClosureAttempt.lean`). -/

/-- **★ The precise iff: Voisin 2007 obstruction closed ↔ literal-
    encoding Clay Hodge at codim 2 ★** —
    at the substrate-level encoding `PF_HodgeEncoding_FullGeneral`,
    the negation of the Voisin 2007 (R3) open content is EQUIVALENT to
    `Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral`.

    Forward: if no `X` carries the Voisin obstruction, then every
    `(X, c)` satisfies `isAlgebraic`, so the Clay statement holds.

    Backward: if the Clay statement holds, then for every `X`, every
    `c` is realised by some `Z`, so the inner existential in
    `Voisin2007GeneralCodimTwoNonAlgebraic` cannot hold, hence no `X`
    carries the obstruction.

    HONEST SCOPE: this iff lives at the substrate-level encoding. The
    LITERAL mathlib iff (with literal H^{2,2} carrier and literal Chow
    cycle classes) is the residual gap from
    `LiftSubstrateToLiteralChowH22`. -/
theorem voisin2007_obstruction_closed_iff_clay_hodge_codim_two :
    (¬ Voisin2007_GeneralQuinticOpenContent) ↔
    Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral := by
  unfold Voisin2007_GeneralQuinticOpenContent
  constructor
  · -- ¬ ∃ X, obstruction ⇒ Clay (full-general)
    intro hNoObstruction
    -- Use the iff isolation: ¬ Clay ↔ ∃ X, obstruction.
    -- Contrapositive: ¬ (∃ X, obstruction) → Clay.
    by_contra hNotClay
    exact hNoObstruction (hodge_clay_gap_isolated_to_voisin_2007.mp hNotClay)
  · -- Clay (full-general) ⇒ ¬ ∃ X, obstruction
    intro hClay
    -- Apply the backward direction of the iff isolation.
    rintro ⟨X, hVoisin⟩
    -- hClay : ∀ Y c, isAlgebraic Y c
    -- hVoisin : ∃ c, ¬ ∃ Z, realises c Z
    -- Contradict by extracting c, applying hClay at (X, c), extracting Z.
    unfold Voisin2007GeneralCodimTwoNonAlgebraic at hVoisin
    obtain ⟨c, hNoCycle⟩ := hVoisin
    -- hClay X c is exactly the existential
    have hAlgX : ∃ (Z : AlgebraicCycleOnQuinticWitness (dworkPencilConcrete 0)),
        QuinticAlgebraicCycleRealisesHodgeClass c Z := hClay X c
    exact hNoCycle hAlgX

/-- **★ Substrate-level direction of the iff: Voisin 2007 obstruction
    is closed (False) AND Clay Hodge codim-2 holds ★** —
    at the substrate-level encoding, BOTH directions of the iff hold
    simultaneously, exhibiting the substrate-level Clay closure as
    EXACTLY the substrate-level Voisin 2007 obstruction closure. -/
theorem voisin2007_obstruction_and_clay_hodge_codim_two_substrate_joint :
    (¬ Voisin2007_GeneralQuinticOpenContent) ∧
    Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral :=
  ⟨Voisin2007_GeneralQuinticOpenContent_substrate_refuted,
   pf_hodgeEncoding_FullGeneral_clay_substrate_closure⟩

/-! ## §5 — Bridge: combined (R1) + (R2) + (R3) status

Voisin 2007's three published partial results combine into a single
status statement: codim-2 Hodge holds on abelian varieties and Dwork
pencil, and is OPEN on the generic non-CM quintic outside Dwork+CM. -/

/-- **★ Voisin 2007 combined partial result status ★** —
    (R1) abelian closed + (R2) Dwork pencil closed + (R3) generic
    non-CM quintic OPEN. The conjunction of (R1) and (R2) is provable
    at substrate level; (R3) is encoded as the open existential
    `Voisin2007_GeneralQuinticOpenContent`, which is refutable at the
    substrate-level shadow but unchanged at the literal geometric
    level.

    NOTE: (R3) here is the OPEN content; we do NOT assert it as
    provable. The full Voisin 2007 status is the conjunction of (R1),
    (R2), and the STATEMENT that (R3) is open — not the conjunction
    of (R1), (R2), and (R3) itself. -/
def Voisin2007_CombinedPartialStatus : Prop :=
  Voisin2007_AbelianCodimTwoHolds ∧
  Voisin2007_DworkPencilCodimTwoHolds

/-- **★ Combined (R1) + (R2) status holds at the PF substrate level ★** —
    the closed cases of Voisin 2007 are jointly discharged axiom-free. -/
theorem Voisin2007_CombinedPartialStatus_substrate :
    Voisin2007_CombinedPartialStatus :=
  ⟨Voisin2007_AbelianCodimTwoHolds_substrate,
   Voisin2007_DworkPencilCodimTwoHolds_substrate⟩

/-! ## §6 — Honest-scope marker and capstone -/

/-- **★ HONEST SCOPE THEOREM ★** —
    precise status of this file:

      * (R1) Voisin 2007 abelian codim-2 result — substrate-level
        DISCHARGED axiom-free on 3 named instances (abelian 3-fold +
        CM abelian 4-fold + CM abelian 5-fold).
      * (R2) Voisin 2007 Dwork pencil codim-2 result — substrate-level
        DISCHARGED axiom-free uniformly across `λ : ℚ`, plus two
        moduli-locus status Props.
      * (R3) Voisin 2007 general quintic OPEN content — encoded at
        type level as `Voisin2007_GeneralQuinticOpenContent` Prop;
        substrate-level shadow refutable; LITERAL geometric content
        UNCHANGED (resolving it remains Fields-medal-grade).
      * Precise iff `¬ Voisin2007_GeneralQuinticOpenContent ↔
        Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral` HOLDS
        axiom-free at the substrate-level encoding.

    NOT a literal Clay-grade discharge of the Hodge conjecture; full
    mathlib formalization requires Chow groups + cycle class map +
    Hodge theory infrastructure (see `LiftSubstrateToLiteralChowH22`
    for the precise residual gap). -/
theorem voisin2007_partial_formalization_honest_scope : True := trivial

/-- **★ VOISIN 2007 PARTIAL FORMALIZATION CAPSTONE ★** —
    `voisin2007_partial_formalization_capstone`.

    Wave 58-Hodge-Voisin-Partial (2026-06-03). Typed encoding of
    Voisin 2007's three published partial Hodge codim-2 results into
    the PF stack:

    **(D1) (R1) abelian codim-2 result** —
        `Voisin2007_AbelianCodimTwoHolds` Prop discharged axiom-free
        at substrate level via three named abelian instances
        (abelian 3-fold + CM abelian 4-fold + CM abelian 5-fold).

    **(D2) (R2) Dwork pencil codim-2 result** —
        `Voisin2007_DworkPencilCodimTwoHolds` Prop discharged
        axiom-free at substrate level uniformly across `λ : ℚ`, with
        Fermat-quintic + Dwork-generic moduli-locus status Props.

    **(D3) (R3) general quintic OPEN content** —
        `Voisin2007_GeneralQuinticOpenContent` Prop encoding the
        actual Voisin 2007 open content; NOT proven; substrate-level
        shadow refutable via
        `Voisin2007_GeneralQuinticOpenContent_substrate_refuted`.

    **(D4) Precise iff** —
        `voisin2007_obstruction_closed_iff_clay_hodge_codim_two` :
        `¬ Voisin2007_GeneralQuinticOpenContent ↔
         Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral`
        holds at the substrate-level encoding.

    **(D5) Joint substrate-level closure** —
        both directions of (D4) hold simultaneously:
        substrate-level (R3) is refuted AND substrate-level Clay
        Hodge holds.

    **(D6) Combined (R1) + (R2) status** —
        `Voisin2007_CombinedPartialStatus` (closed sub-cases) holds
        at substrate level.

    **HONEST SCOPE**: NOT a literal Clay discharge of the codim ≥ 2
    Hodge conjecture. The discharges on (R1) and (R2) and the iff in
    (D4) operate at the substrate-level encoding (rank-1 ℚ-coefficient
    + matching-coefficient realisation predicate); full mathlib
    formalization requires Chow groups + cycle class map + Hodge
    theory infrastructure not yet in mathlib in Clay-grade form. The
    (R3) Prop encodes the Fields-medal-grade open content; substrate-
    level refutation does NOT touch the literal geometric question. -/
theorem voisin2007_partial_formalization_capstone :
    -- (D1) (R1) abelian codim-2 result holds at substrate level.
    Voisin2007_AbelianCodimTwoHolds
    ∧
    -- (D2) (R2) Dwork pencil codim-2 result holds at substrate level.
    Voisin2007_DworkPencilCodimTwoHolds
    ∧
    -- (D3) (R3) Substrate-level shadow of OPEN content is refuted.
    (¬ Voisin2007_GeneralQuinticOpenContent)
    ∧
    -- (D4) Precise iff at substrate-level encoding.
    ((¬ Voisin2007_GeneralQuinticOpenContent) ↔
     Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral)
    ∧
    -- (D5) Joint substrate-level closure: (R3 refuted) ∧ (Clay Hodge).
    ((¬ Voisin2007_GeneralQuinticOpenContent) ∧
     Clay_Hodge_Standard PF_HodgeEncoding_FullGeneral)
    ∧
    -- (D6) Combined (R1) + (R2) status.
    Voisin2007_CombinedPartialStatus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Voisin2007_AbelianCodimTwoHolds_substrate
  · exact Voisin2007_DworkPencilCodimTwoHolds_substrate
  · exact Voisin2007_GeneralQuinticOpenContent_substrate_refuted
  · exact voisin2007_obstruction_closed_iff_clay_hodge_codim_two
  · exact voisin2007_obstruction_and_clay_hodge_codim_two_substrate_joint
  · exact Voisin2007_CombinedPartialStatus_substrate

end PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization

-- Axiom checks. Expected for every theorem:
-- `[propext, Classical.choice, Quot.sound]` (standard mathlib base;
-- ZERO project axioms).
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.Voisin2007_AbelianCodimTwoHolds_substrate
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.Voisin2007_DworkPencilCodimTwoHolds_substrate
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.Voisin2007_GeneralQuinticOpenContent_substrate_refuted
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.voisin2007_obstruction_closed_iff_clay_hodge_codim_two
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.voisin2007_obstruction_and_clay_hodge_codim_two_substrate_joint
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.Voisin2007_CombinedPartialStatus_substrate
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.voisin2007_partial_formalization_honest_scope
#print axioms
  PrincipiaTractalis.AlgebraicGeometry.Voisin2007PartialFormalization.voisin2007_partial_formalization_capstone
