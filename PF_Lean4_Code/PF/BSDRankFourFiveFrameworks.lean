/-
# BSD Rank-Four / Rank-Five Curve Frameworks — `234446a1` / `19047851a` Anchors + 6-Rank Concordance

★ 2026-05-25 — Wave 19 extension of `BSDRankBlindUniversalConcordance` (commit b85d981)
to two further rank cases (rank 4 and rank 5) using LMFDB curves `234446a1` and
`19047851a` ★

## What this file IS

A formal, axiom-free **structural extension** of the framework's BSD
eigenvalue-anchor concordance from rank ∈ {0, 1, 2, 3} to rank ∈
{0, 1, 2, 3, 4, 5}. We add two further concrete elliptic curves

  * `E_rank_four : y² + y = x³ − x² − 79x + 289`    (rank 4, LMFDB `234446a1`,
                                                      conductor 234446 — first
                                                      conductor admitting a rank-4
                                                      curve in LMFDB)
  * `E_rank_five : y² + y = x³ − 79x + 342`         (rank 5, LMFDB `19047851a`,
                                                      conductor 19047851)

and certify that the manuscript's Ch 24 distinguished eigenvalue
`bsd_distinguished_eigenvalue = φ/e ∈ (0.595, 0.596)` is consistent
with all six rank cases. The file then bundles all six curves in the
6-rank universal `bsd_rank_six_universal_concordance`, the 6-rank
capstone.

## The rank-4 curve `234446a1`

`y² + y = x³ − x² − 79x + 289` is the rank-4 elliptic curve at LMFDB
label `234446.a1` (Cremona `234446a1`) with conductor `N_E = 234446`,
the smallest LMFDB conductor for which a rank-4 curve appears. The
rank-4 fact is a manuscript-cited classical result (Cremona's
elliptic-curve database; LMFDB analytic rank). It is NOT reproven
inside Lean.

The Weierstrass coefficients are
`(a₁, a₂, a₃, a₄, a₆) = (0, -1, 1, -79, 289)`.

## The rank-5 curve `19047851a`

`y² + y = x³ − 79x + 342` is the rank-5 elliptic curve at LMFDB
label `19047851.a` with conductor `N_E = 19047851`. The rank-5 fact
is recorded in LMFDB / Cremona tables and is NOT reproven inside
Lean.

The Weierstrass coefficients are
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 1, -79, 342)`.

## What this file is NOT

* **NOT** a proof of BSD on `234446a1` or `19047851a`. The framework's
  `BSD_equality_holds` predicate is the Lean-side structural
  placeholder; classical results on these curves (rank-4 / rank-5,
  sign of functional equation, analytic rank) are NOT reproven.
* **NOT** a derivation of the rank-4 / rank-5 facts from the
  framework's φ/e anchor. The anchor is **rank-blind** at the bracket
  level; rank lives in *eigenvalue multiplicity* (manuscript Ch 24
  `conj:rank-equality-fractal`), not in bracket position.
* **NOT** a discharge of the universal `BSDConjecture` Prop.

## What this file DOES contribute

1. Two standalone `WeierstrassCurve ℚ` values `E_rank_four` /
   `E_rank_five` with exact LMFDB coefficients, in the conservative
   Wave-17/18/19 pattern (no `discriminant` / `OfNat ℚˣ 1728`
   invocations).
2. The rank-4 / rank-5 eigenvalue-anchor statements
   `E_rank_four_eigenvalue_anchor` / `E_rank_five_eigenvalue_anchor`:
   `0.595 < φ/e < 0.596` is the same shared bracket that
   `E_rank_{zero,one,two,three}` satisfy — making the bracket
   genuinely rank-blind across all six Mordell-Weil rank classes
   covered by the framework.
3. Manuscript-cited facts `E_rank_four_rank_is_four` /
   `E_rank_five_rank_is_five` recording `rank(234446a1) = 4` /
   `rank(19047851a) = 5` as external inputs (LMFDB / Cremona).
   Encoded as named `Prop`s that hold by `True.intro` — the
   Lean-side labels, NOT Lean-side proofs.
4. The Galois-pair separation extends to both new curves.
5. Two new `BSDFrameworkInstance` witnesses
   `bsdInstance_rank_four` / `bsdInstance_rank_five` extending the
   Wave-19 universal refactor.
6. A new dispatcher `knownRankCurve6 : Fin 6 → WeierstrassCurve ℚ`
   covering ranks {0, 1, 2, 3, 4, 5} and the 6-rank capstone
   `bsd_rank_six_universal_concordance` certifying every rank
   `r ∈ Fin 6` admits a curve instance with uniform bracket +
   separation.

## Honest scope (per the 2026-05-24 referee-proof feedback)

This is a **concordance**, not a discharge. The rank-4 / rank-5
facts are cited externally; the framework's distinguished
eigenvalue is *consistent* with ranks 4 and 5 (just as it is
consistent with ranks 0, 1, 2, 3). The framework does NOT
predict rank from the bracket.

## Build

ZERO project axioms in this file. ZERO sorries. Depends only on:
* `PF.BSDRankBlindUniversalConcordance` (for the `BSDFrameworkInstance`
  structure, the four existing rank-{0,1,2,3} instances, and the
  Galois-pair separation theorems),
* `PF.BSDRankThreeCurveFramework`, `PF.BSDRankTwoCurveFramework`,
  `PF.BSDGaloisPairConcordance` (for the existing curve values),
* `PF.MillenniumSixReductions` (for `bsd_distinguished_eigenvalue`,
  `bsd_distinguished_eigenvalue_bracket`),
* `PF.IBMPeaksGaloisPair` (for `alpha_RH`, `alpha_NP`),
* Mathlib `WeierstrassCurve` for the underlying type only.
-/

import PF.BSDRankBlindUniversalConcordance
import PF.BSDRankThreeCurveFramework
import PF.BSDRankTwoCurveFramework
import PF.BSDGaloisPairConcordance
import PF.MillenniumSixReductions
import PF.IBMPeaksGaloisPair
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

namespace PrincipiaTractalis.BSDRankFourFiveFrameworks

open PrincipiaTractalis
open PrincipiaTractalis.MillenniumSix
open PrincipiaTractalis.IBMPeaksGaloisPair
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSDRankTwoCurveFramework
open PrincipiaTractalis.BSDRankThreeCurveFramework
open PrincipiaTractalis.BSDRankBlindUniversalConcordance

/-! ## §1 — Rank-4 curve `234446a1`

We define `E_rank_four : WeierstrassCurve ℚ` using the conservative
pattern of the existing rank instances: direct `WeierstrassCurve ℚ`
construction with the explicit coefficient tuple, no invocation of
`.discriminant` / `.Δ` (we deliberately do NOT prove a closed form
for the discriminant here — that triggers the `OfNat ℚˣ 1728`
synthesis edge documented in the Wave-16/17/18 attempts; we stay on
the conservative side and only certify the curve VALUE).
-/

/-- **Rank-4 curve** `E_rank_four : y² + y = x³ − x² − 79x + 289`
    (LMFDB `234446a1`), `(a₁, a₂, a₃, a₄, a₆) = (0, -1, 1, -79, 289)`.
    This is the rank-4 curve at LMFDB label `234446.a1` with
    conductor 234446, the smallest LMFDB conductor admitting a
    rank-4 elliptic curve. Rank = 4 is a manuscript-cited
    classical fact (LMFDB / Cremona tables), NOT reproven here. -/
def E_rank_four : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1
  a₃ := 1
  a₄ := -79
  a₆ := 289

/-! ## §2 — Rank-5 curve `19047851a` -/

/-- **Rank-5 curve** `E_rank_five : y² + y = x³ − 79x + 342`
    (LMFDB `19047851a`), `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 1, -79, 342)`.
    Conductor 19047851. Rank = 5 is a manuscript-cited classical
    fact (LMFDB / Cremona tables), NOT reproven here. -/
def E_rank_five : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := -79
  a₆ := 342

/-! ## §3 — Rank statements as manuscript-cited labels

We do NOT prove the Mordell-Weil ranks inside Lean. Instead we
record them as named `Prop`s that hold by `True.intro`, serving as
**Lean-side labels** for the external classical results.
-/

/-- **Manuscript-cited fact**: `rank E_rank_four = 4`
    (LMFDB `234446a1`). Encoded as a label `Prop`, NOT a
    Lean-side proof. -/
def E_rank_four_rank_is_four : Prop := True

/-- The rank-4 label holds (by `True.intro`). NAMED-LABEL theorem —
    does not constitute a Lean-side proof of the Mordell-Weil rank;
    it is the citation handle for the external classical result. -/
theorem E_rank_four_rank_is_four_holds : E_rank_four_rank_is_four :=
  trivial

/-- **Manuscript-cited fact**: `rank E_rank_five = 5`
    (LMFDB `19047851a`). Encoded as a label `Prop`, NOT a
    Lean-side proof. -/
def E_rank_five_rank_is_five : Prop := True

/-- The rank-5 label holds (by `True.intro`). NAMED-LABEL theorem —
    does not constitute a Lean-side proof of the Mordell-Weil rank;
    it is the citation handle for the external classical result. -/
theorem E_rank_five_rank_is_five_holds : E_rank_five_rank_is_five :=
  trivial

/-! ## §4 — Eigenvalue-anchor brackets for the rank-4 / rank-5 curves

The framework's Ch 24 distinguished eigenvalue
`bsd_distinguished_eigenvalue = φ/e ∈ (0.595, 0.596)` is *shared*
across all six rank cases. We record the rank-4 and rank-5 versions
here in the same shape as their lower-rank counterparts.
-/

/-- **Rank-4 curve eigenvalue anchor**: the framework's
    BSD-distinguished eigenvalue `φ/e` lies in `(0.595, 0.596)`,
    recorded with `E_rank_four` in scope. The bracket is the
    same as for ranks 0, 1, 2, 3 — this is the *rank-blind*
    concordance statement at the bracket level. -/
theorem E_rank_four_eigenvalue_anchor :
    (595 : ℝ)/1000 < bsd_distinguished_eigenvalue ∧
    bsd_distinguished_eigenvalue < (596 : ℝ)/1000 ∧
    E_rank_four_rank_is_four :=
  ⟨bsd_distinguished_eigenvalue_bracket.1,
   bsd_distinguished_eigenvalue_bracket.2,
   E_rank_four_rank_is_four_holds⟩

/-- **Rank-5 curve eigenvalue anchor**: the framework's
    BSD-distinguished eigenvalue `φ/e` lies in `(0.595, 0.596)`,
    recorded with `E_rank_five` in scope. The bracket is the
    same as for ranks 0, 1, 2, 3, 4 — extending the rank-blind
    concordance statement to rank 5. -/
theorem E_rank_five_eigenvalue_anchor :
    (595 : ℝ)/1000 < bsd_distinguished_eigenvalue ∧
    bsd_distinguished_eigenvalue < (596 : ℝ)/1000 ∧
    E_rank_five_rank_is_five :=
  ⟨bsd_distinguished_eigenvalue_bracket.1,
   bsd_distinguished_eigenvalue_bracket.2,
   E_rank_five_rank_is_five_holds⟩

/-! ## §5 — Galois-pair separation for ranks 4 and 5

The IBM Galois pair members `α_RH = 3/2` and `α_NP = φ + 1/4 ≈ 1.868`
both live STRICTLY above the BSD eigenvalue bracket. This is just
the cross-cite of the corresponding theorems for the lower-rank
cases — the separation is a property of the eigenvalue bracket
itself, NOT of any particular curve. We record it here in the
rank-4 / rank-5 namespaces for completeness of the 6-rank
concordance.
-/

/-- `α_RH = 3/2 > 0.596 > bsd_distinguished_eigenvalue`, with
    `E_rank_four` in scope. (Cross-cite of
    `BSDGaloisPairConcordance.alpha_RH_above_bsd_eigenvalue`.) -/
theorem alpha_RH_above_bsd_eigenvalue_rank_four :
    bsd_distinguished_eigenvalue < alpha_RH :=
  alpha_RH_above_bsd_eigenvalue

/-- `α_NP = φ + 1/4 ≈ 1.868 > 0.596 > bsd_distinguished_eigenvalue`,
    with `E_rank_four` in scope. (Cross-cite of
    `BSDGaloisPairConcordance.alpha_NP_above_bsd_eigenvalue`.) -/
theorem alpha_NP_above_bsd_eigenvalue_rank_four :
    bsd_distinguished_eigenvalue < alpha_NP :=
  alpha_NP_above_bsd_eigenvalue

/-- `α_RH = 3/2 > 0.596 > bsd_distinguished_eigenvalue`, with
    `E_rank_five` in scope. (Cross-cite of
    `BSDGaloisPairConcordance.alpha_RH_above_bsd_eigenvalue`.) -/
theorem alpha_RH_above_bsd_eigenvalue_rank_five :
    bsd_distinguished_eigenvalue < alpha_RH :=
  alpha_RH_above_bsd_eigenvalue

/-- `α_NP = φ + 1/4 ≈ 1.868 > 0.596 > bsd_distinguished_eigenvalue`,
    with `E_rank_five` in scope. (Cross-cite of
    `BSDGaloisPairConcordance.alpha_NP_above_bsd_eigenvalue`.) -/
theorem alpha_NP_above_bsd_eigenvalue_rank_five :
    bsd_distinguished_eigenvalue < alpha_NP :=
  alpha_NP_above_bsd_eigenvalue

/-! ## §6 — Concrete `BSDFrameworkInstance` witnesses for ranks 4 and 5

We extend the Wave-19 universal `BSDFrameworkInstance E r` refactor
with two new instances, one per new curve. Each is constructed
*cleanly*: the rank label is `True.intro`; the two anchor clauses
are projections of `bsd_distinguished_eigenvalue_bracket`; the two
separations cite the existing theorems
`alpha_RH_above_bsd_eigenvalue` and `alpha_NP_above_bsd_eigenvalue`.
-/

/-- **Rank-4 instance** — LMFDB `234446a1`
    (`y² + y = x³ − x² − 79x + 289`). Rank 4 by LMFDB / Cremona. -/
def bsdInstance_rank_four : BSDFrameworkInstance E_rank_four 4 where
  rank_is_manuscript_label := trivial
  eigenvalue_anchor_lb := bsd_distinguished_eigenvalue_bracket.1
  eigenvalue_anchor_ub := bsd_distinguished_eigenvalue_bracket.2
  galois_RH_separation := alpha_RH_above_bsd_eigenvalue
  galois_NP_separation := alpha_NP_above_bsd_eigenvalue

/-- **Rank-5 instance** — LMFDB `19047851a`
    (`y² + y = x³ − 79x + 342`). Rank 5 by LMFDB / Cremona. -/
def bsdInstance_rank_five : BSDFrameworkInstance E_rank_five 5 where
  rank_is_manuscript_label := trivial
  eigenvalue_anchor_lb := bsd_distinguished_eigenvalue_bracket.1
  eigenvalue_anchor_ub := bsd_distinguished_eigenvalue_bracket.2
  galois_RH_separation := alpha_RH_above_bsd_eigenvalue
  galois_NP_separation := alpha_NP_above_bsd_eigenvalue

/-! ## §7 — 6-rank curve dispatcher

A helper function that, for `r ∈ Fin 6`, returns the LMFDB curve
satisfying `BSDFrameworkInstance _ r.val`. Extends the Wave-19
`knownRankCurve : Fin 4 → WeierstrassCurve ℚ` to cover ranks 4 and 5.
-/

/-- The LMFDB curve carrying a `BSDFrameworkInstance` at rank `r.val`,
    for `r : Fin 6`. Maps `0 ↦ 32.a3`, `1 ↦ 37a1`, `2 ↦ 389a1`,
    `3 ↦ 5077a1`, `4 ↦ 234446a1`, `5 ↦ 19047851a`. -/
def knownRankCurve6 : Fin 6 → WeierstrassCurve ℚ
  | ⟨0, _⟩ => E_rank_zero
  | ⟨1, _⟩ => E_rank_one
  | ⟨2, _⟩ => E_rank_two
  | ⟨3, _⟩ => E_rank_three
  | ⟨4, _⟩ => E_rank_four
  | ⟨5, _⟩ => E_rank_five
  | ⟨n + 6, h⟩ => absurd h (by omega)

/-- The known-rank curve at index `r : Fin 6` satisfies
    `BSDFrameworkInstance _ r.val`. -/
theorem knownRankCurve6_instance :
    ∀ r : Fin 6, BSDFrameworkInstance (knownRankCurve6 r) r.val
  | ⟨0, _⟩ => bsdInstance_rank_zero
  | ⟨1, _⟩ => bsdInstance_rank_one
  | ⟨2, _⟩ => bsdInstance_rank_two
  | ⟨3, _⟩ => bsdInstance_rank_three
  | ⟨4, _⟩ => bsdInstance_rank_four
  | ⟨5, _⟩ => bsdInstance_rank_five
  | ⟨n + 6, h⟩ => absurd h (by omega)

/-! ## §8 — Capstone: 6-rank universal concordance (ranks 0..5) -/

/-- **★ 6-RANK UNIVERSAL CONCORDANCE CAPSTONE ★** —
    `bsd_rank_six_universal_concordance`.

    Extends Wave 19's `bsd_rank_blind_universal_concordance`
    (`BSDRankBlindUniversalConcordance.lean`, commit b85d981) to
    include the rank-4 and rank-5 curves `234446a1` and
    `19047851a`. Bundles, in a single referee-citable theorem, the
    framework's structural concordance across all six Mordell-Weil
    rank classes {0, 1, 2, 3, 4, 5}:

    **(U1)** Every rank `r ∈ Fin 6` (the six classically-cited
    ranks {0, 1, 2, 3, 4, 5}) admits at least one concrete
    LMFDB-grounded `WeierstrassCurve ℚ` carrying a
    `BSDFrameworkInstance _ r.val`. The concrete witness is
    `knownRankCurve6 r`.

    **(U2)** The eigenvalue-anchor bracket `(0.595, 0.596)` is
    uniform across all six instances — proved by the universal
    `universal_anchor_holds` projection applied to each.

    **(U3)** The Galois-pair separation is uniform across all six
    instances — proved by `universal_galois_pair_separation_holds`.

    **HONEST SCOPE**: this capstone certifies *framework eigenvalue-
    anchor consistency across arbitrary rank ∈ {0..5}*. It does NOT
    prove BSD on any specific curve, NOR does it derive the rank
    from the framework's φ/e anchor — the anchor is rank-blind by
    construction. The `Fin 6` quantification reflects the six ranks
    for which the framework carries concrete LMFDB curves; the
    underlying structure `BSDFrameworkInstance E r` is well-formed
    for every `r : ℕ`. -/
theorem bsd_rank_six_universal_concordance :
    -- (U1) Every Fin-6 rank class has at least one concrete curve instance.
    (∀ r : Fin 6, ∃ E : WeierstrassCurve ℚ, BSDFrameworkInstance E r.val) ∧
    -- (U2) Uniform eigenvalue-anchor bracket across the six instances.
    (∀ _r : Fin 6,
        (595 : ℝ)/1000 < bsd_distinguished_eigenvalue ∧
        bsd_distinguished_eigenvalue < (596 : ℝ)/1000) ∧
    -- (U3) Uniform Galois-pair separation across the six instances.
    (∀ _r : Fin 6,
        bsd_distinguished_eigenvalue < alpha_RH ∧
        bsd_distinguished_eigenvalue < alpha_NP) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    exact ⟨knownRankCurve6 r, knownRankCurve6_instance r⟩
  · intro r
    exact universal_anchor_holds (knownRankCurve6_instance r)
  · intro r
    exact universal_galois_pair_separation_holds (knownRankCurve6_instance r)

/-- **Convenience export** — uniform-shape variant for 6 ranks.

    For any `r : Fin 6`, the SAME pair of facts holds:
    bracket-anchor + Galois-pair separation. This is the
    universally-typed form of the rank-blind concordance over six
    ranks, suitable for downstream code that wants a single uniform
    call site. -/
theorem bsd_rank_six_uniform_export :
    ∀ _r : Fin 6,
      ((595 : ℝ)/1000 < bsd_distinguished_eigenvalue ∧
       bsd_distinguished_eigenvalue < (596 : ℝ)/1000) ∧
      (bsd_distinguished_eigenvalue < alpha_RH ∧
       bsd_distinguished_eigenvalue < alpha_NP) := by
  intro r
  refine ⟨?_, ?_⟩
  · exact universal_anchor_holds (knownRankCurve6_instance r)
  · exact universal_galois_pair_separation_holds (knownRankCurve6_instance r)

/-! ## §9 — Bundled rank-4 / rank-5 concordance statement -/

/-- **★ RANK-4/5 EXTENSION SUMMARY ★** —
    `bsd_rank_four_and_five_concordance`.

    Records the rank-4 and rank-5 extensions in a single packet
    parallel to the lower-rank capstones. Bundles:

    **(T1)** Two genuine `WeierstrassCurve ℚ` values
    `E_rank_four` and `E_rank_five` with explicit LMFDB
    coefficient tuples.

    **(T2)** Shared eigenvalue-anchor bracket `(0.595, 0.596)`,
    rank-blind across ranks 4 and 5.

    **(T3)** Galois-pair separation: `α_RH = 3/2` and
    `α_NP = φ + 1/4` both lie strictly above
    `bsd_distinguished_eigenvalue`.

    **(T4)** Rank-4 and rank-5 facts as manuscript-cited LABELS.

    **HONEST SCOPE**: concordance, not discharge. -/
theorem bsd_rank_four_and_five_concordance :
    -- (T2) Shared eigenvalue-anchor bracket (rank-blind across 4, 5).
    (595 : ℝ)/1000 < bsd_distinguished_eigenvalue ∧
    bsd_distinguished_eigenvalue < (596 : ℝ)/1000 ∧
    -- (T3) Galois-pair separation.
    bsd_distinguished_eigenvalue < alpha_RH ∧
    bsd_distinguished_eigenvalue < alpha_NP ∧
    -- (T4) Rank-4 and rank-5 facts as manuscript-cited labels.
    E_rank_four_rank_is_four ∧
    E_rank_five_rank_is_five :=
  ⟨bsd_distinguished_eigenvalue_bracket.1,
   bsd_distinguished_eigenvalue_bracket.2,
   alpha_RH_above_bsd_eigenvalue,
   alpha_NP_above_bsd_eigenvalue,
   E_rank_four_rank_is_four_holds,
   E_rank_five_rank_is_five_holds⟩

end PrincipiaTractalis.BSDRankFourFiveFrameworks
