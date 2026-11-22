/-
# The Heegner split condition, faithfully — and what the `True` version destroys

**2026-11-21.** Additive. Nothing existing is renamed, weakened or removed.

## The defect

`PF/BSD_HeegnerRank1Proof.lean` carries the two load-bearing hypotheses
of the Gross–Zagier–Kolyvagin rank-1 argument as

```
def HeegnerHypothesisSatisfied (_E : WeierstrassCurve ℚ) : Prop := True
def LDerivativeAtOneNonZero    (_E : WeierstrassCurve ℚ) : Prop := True
```

Both `True`, both discarding the curve. Between them they are mentioned
**87 times** across thirteen per-curve files, all inside the build
closure — the largest single vacuity surface in the corpus.

`PF/BSD_GrossZagier1986Formalization.lean` looks like it fixes the first
one, but does not:

```
def HeegnerHypothesis (_E : WeierstrassCurve ℚ) (_K : ImaginaryQuadraticData)
    : Prop := True
def HeegnerHypothesisSatisfied_Typed (E) : Prop := ∃ K, HeegnerHypothesis E K
```

`HeegnerHypothesis` discards **both** binders, so the `_Typed` version is
`∃ K, True` — that is, `Nonempty ImaginaryQuadraticData`, which holds for
`⟨-1, _⟩`. The `_Typed` suffix names a structural tag, not content.

What is *not* wrong: the file states its own vacuity as theorems
(`heegner_pair_both_iff_True`, `..._at_True_placeholder`,
`bsd_rank_one_E37a1_discharged_at_placeholder`), and
`codex/BSD_SCOPING_UPPER_BOUND_IS_THE_GAP_2026-10-17.md` already judged
the naming discipline "as good as it gets". So the disclosure work is
done and is not repeated here. **What was missing is the content.**

## What this file supplies

The docstring of `HeegnerHypothesis` says exactly what it should be:

> every prime divisor of the conductor `N` splits in `K = ℚ(√d_K)` …
> for every prime `p` dividing `N`, the Legendre/Kronecker symbol
> `(d_K | p) = +1`

That is decidable arithmetic and writable at this pin. `d_K` splits at an
odd prime `p` exactly when `d_K` is a nonzero square mod `p`, so the
condition needs only `ZMod p` — and in particular **no `Fact p.Prime`
instance**, which is what makes it statable inside a `∀ p, p.Prime → …`
binder at all.

Nine of the corpus's rank-1 curves then get their Heegner split
condition **proved**, with the explicit square root supplied in each
case, rather than inhabited by `trivial`.

## The teeth

For one curve, two fundamental discriminants:

| `E_37a1`, `N = 37` | `(d_K ∣ 37)` | |
|---|---|---|
| `d_K = −7`, i.e. `ℚ(√−7)` | `+1` | **splits** — and is the field the corpus's own docstring names |
| `d_K = −8`, i.e. `ℚ(√−2)` | `−1` | **does not split** |

So the faithful condition separates two imaginary quadratic fields for
the same curve. The `True` version provably cannot: it identifies them
(`heegner_true_identifies_distinct_fields`, by `rfl`). That is the
content `:= True` destroys, stated as a pair of theorems rather than as a
complaint.

## Scope, stated plainly

* **The L-derivative half is not repaired, and cannot be at this pin.**
  mathlib has no L-function of an elliptic curve — measured: zero files
  for `EllipticCurve.*LSeries`, `WeierstrassCurve.*LSeries`,
  `analyticRank`, and `Mathlib/AlgebraicGeometry/EllipticCurve/` contains
  no L-function file. A faithful `L'(E,1) ≠ 0` needs the `aₙ` of `E`
  (point counts over `𝔽_p`) fed into `LSeries`, then analytic
  continuation to `s = 1`. That is a genuine formalisation project. It is
  recorded here, not faked.
* **The primes `p = 2` are excluded** from the condition. Splitting at 2
  is governed by the Kronecker symbol `(d ∣ 2)`, which mathlib lacks.
  For odd `N` this changes nothing; it is why the curves of conductor
  `102 = 2·3·17` and `106 = 2·53` are not proved below.
* `ImaginaryQuadraticData` only requires `d_K < 0`, not that `d_K` be a
  *fundamental* discriminant. The predicate below is therefore the split
  condition, which is the content-bearing core of the Heegner hypothesis
  — not the full classical hypothesis including fundamentality.
* **Nothing here proves BSD, or the rank of any curve.** The split
  condition is one of two hypotheses of Gross–Zagier–Kolyvagin, and the
  other is still `True`.
-/

import PF.BSD_GrossZagier1986Formalization
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

namespace PrincipiaTractalis.BSD_HeegnerHypothesis_Faithful_2026_11_21

open PrincipiaTractalis
open PrincipiaTractalis.BSDGaloisPairConcordance
open PrincipiaTractalis.BSD_HeegnerRank1Proof
open PrincipiaTractalis.BSD_GrossZagier1986Formalization

/-! ## §1 — The split condition, as arithmetic -/

/-- **`d` splits at the odd prime `p`**: `d` is a nonzero square mod `p`.

    This is the elementary form of "`p` splits in `ℚ(√d)`", equivalent to
    the Legendre symbol `(d ∣ p) = +1`. Stated with `ZMod p` rather than
    mathlib's `legendreSym` deliberately: `legendreSym p` requires a
    `Fact p.Prime` *instance*, which cannot be produced inside a
    `∀ p, p.Prime → …` binder, whereas `ZMod p` needs none. -/
def SplitsAt (p : ℕ) (d : ℤ) : Prop :=
  ((d : ZMod p) ≠ 0) ∧ IsSquare ((d : ZMod p))

/-- **The Heegner split condition** for conductor `N` and imaginary
    quadratic data `K`: every odd prime dividing `N` splits in
    `ℚ(√d_K)`.

    This is the content-bearing core of the Heegner hypothesis. It is
    *not* the full classical hypothesis: the prime 2 is excluded (it needs
    the Kronecker symbol, absent from mathlib at this pin) and
    fundamentality of `d_K` is not required, since
    `ImaginaryQuadraticData` does not carry it. -/
def HeegnerSplitCondition (N : ℕ) (K : ImaginaryQuadraticData) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ N → SplitsAt p K.d_K

/-- For a prime conductor the condition reduces to the single prime `N`. -/
theorem heegnerSplitCondition_of_prime {N : ℕ} (hN : N.Prime)
    (K : ImaginaryQuadraticData) (h : SplitsAt N K.d_K) :
    HeegnerSplitCondition N K := by
  intro p hp _ hdvd
  rwa [(Nat.prime_dvd_prime_iff_eq hp hN).mp hdvd]

/-! ## §2 — The imaginary quadratic fields used below

`ImaginaryQuadraticData` carries the fundamental discriminant and the
proof that it is negative. -/

/-- `ℚ(√−7)`, the field the corpus's own `E_37a1` docstring names. -/
def K_neg7 : ImaginaryQuadraticData := ⟨-7, by norm_num⟩

/-- `ℚ(√−2)`, discriminant `−8`. Used as the negative witness. -/
def K_neg8 : ImaginaryQuadraticData := ⟨-8, by norm_num⟩

/-- `ℚ(√−3)`, discriminant `−3`. -/
def K_neg3 : ImaginaryQuadraticData := ⟨-3, by norm_num⟩

/-- `ℚ(√−1)`, discriminant `−4`. -/
def K_neg4 : ImaginaryQuadraticData := ⟨-4, by norm_num⟩

/-- `ℚ(√−11)`, discriminant `−11`. -/
def K_neg11 : ImaginaryQuadraticData := ⟨-11, by norm_num⟩

/-! ## §3 — The split condition, proved, for nine rank-1 curves

Each is an explicit square root mod the conductor. The LMFDB label of
each curve encodes its conductor as the leading number, so `E_37a1` has
`N = 37`, `E_43a1` has `N = 43`, and so on. -/

/-- `−7` is a nonzero square mod 37: `17² = 30 = −7`. -/
theorem splitsAt_37_neg7 : SplitsAt 37 (-7) :=
  ⟨by decide, ⟨17, by decide⟩⟩

/-- `−3` is a nonzero square mod 43: `13² = 40 = −3`. -/
theorem splitsAt_43_neg3 : SplitsAt 43 (-3) :=
  ⟨by decide, ⟨13, by decide⟩⟩

/-- `−4` is a nonzero square mod 53: `7² = 49 = −4`. -/
theorem splitsAt_53_neg4 : SplitsAt 53 (-4) :=
  ⟨by decide, ⟨7, by decide⟩⟩

/-- `−3` is a nonzero square mod 61: `27² = 58 = −3`. -/
theorem splitsAt_61_neg3 : SplitsAt 61 (-3) :=
  ⟨by decide, ⟨27, by decide⟩⟩

/-- `−3` is a nonzero square mod 79: `32² = 76 = −3`. -/
theorem splitsAt_79_neg3 : SplitsAt 79 (-3) :=
  ⟨by decide, ⟨32, by decide⟩⟩

/-- `−8` is a nonzero square mod 83: `18² = 75 = −8`. -/
theorem splitsAt_83_neg8 : SplitsAt 83 (-8) :=
  ⟨by decide, ⟨18, by decide⟩⟩

/-- `−4` is a nonzero square mod 89: `21² = 85 = −4`. -/
theorem splitsAt_89_neg4 : SplitsAt 89 (-4) :=
  ⟨by decide, ⟨21, by decide⟩⟩

/-- `−4` is a nonzero square mod 101: `20² = 97 = −4`. -/
theorem splitsAt_101_neg4 : SplitsAt 101 (-4) :=
  ⟨by decide, ⟨20, by decide⟩⟩

/-- `−8` is a nonzero square mod 131: `56² = 123 = −8`. -/
theorem splitsAt_131_neg8 : SplitsAt 131 (-8) :=
  ⟨by decide, ⟨56, by decide⟩⟩

/-- **★ `E_37a1` satisfies the Heegner split condition** with `K = ℚ(√−7)`
    — the field its own docstring in `BSD_HeegnerRank1Proof` names.
    Proved, not `trivial`. -/
theorem heegner_37_neg7 : HeegnerSplitCondition 37 K_neg7 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg7 splitsAt_37_neg7

theorem heegner_43_neg3 : HeegnerSplitCondition 43 K_neg3 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg3 splitsAt_43_neg3

theorem heegner_53_neg4 : HeegnerSplitCondition 53 K_neg4 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg4 splitsAt_53_neg4

theorem heegner_61_neg3 : HeegnerSplitCondition 61 K_neg3 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg3 splitsAt_61_neg3

theorem heegner_79_neg3 : HeegnerSplitCondition 79 K_neg3 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg3 splitsAt_79_neg3

theorem heegner_83_neg8 : HeegnerSplitCondition 83 K_neg8 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg8 splitsAt_83_neg8

theorem heegner_89_neg4 : HeegnerSplitCondition 89 K_neg4 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg4 splitsAt_89_neg4

theorem heegner_101_neg4 : HeegnerSplitCondition 101 K_neg4 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg4 splitsAt_101_neg4

theorem heegner_131_neg8 : HeegnerSplitCondition 131 K_neg8 :=
  heegnerSplitCondition_of_prime (by norm_num) K_neg8 splitsAt_131_neg8

/-- All nine at once, as a single citable record. -/
theorem heegner_split_condition_nine_curves :
    HeegnerSplitCondition 37 K_neg7 ∧ HeegnerSplitCondition 43 K_neg3 ∧
    HeegnerSplitCondition 53 K_neg4 ∧ HeegnerSplitCondition 61 K_neg3 ∧
    HeegnerSplitCondition 79 K_neg3 ∧ HeegnerSplitCondition 83 K_neg8 ∧
    HeegnerSplitCondition 89 K_neg4 ∧ HeegnerSplitCondition 101 K_neg4 ∧
    HeegnerSplitCondition 131 K_neg8 :=
  ⟨heegner_37_neg7, heegner_43_neg3, heegner_53_neg4, heegner_61_neg3,
   heegner_79_neg3, heegner_83_neg8, heegner_89_neg4, heegner_101_neg4,
   heegner_131_neg8⟩

/-! ## §4 — The teeth: the condition separates fields, `True` cannot -/

/-- `−8` is **not** a square mod 37, so `ℚ(√−2)` does not split at 37.
    Decided by exhausting `ZMod 37`. -/
theorem not_isSquare_neg8_mod_37 : ¬ IsSquare (((-8 : ℤ) : ZMod 37)) := by
  rintro ⟨r, hr⟩
  revert hr
  revert r
  decide

/-- **★ `E_37a1` does NOT satisfy the split condition for `ℚ(√−2)`.**

    So the condition is a genuine constraint on the imaginary quadratic
    field, not a formality: for the same curve, `ℚ(√−7)` splits and
    `ℚ(√−2)` does not. -/
theorem not_heegner_37_neg8 : ¬ HeegnerSplitCondition 37 K_neg8 := by
  intro h
  exact not_isSquare_neg8_mod_37 (h 37 (by norm_num) (by norm_num) dvd_rfl).2

/-- **★★ Two distinct class members for the same curve.**

    `feedback_structural_tag_is_vacuous` asks for two distinct members
    before a predicate counts as a position. Here they are, and they are
    two *fundamental discriminants* of two genuine imaginary quadratic
    fields. -/
theorem heegner_split_condition_is_substantive :
    HeegnerSplitCondition 37 K_neg7 ∧ ¬ HeegnerSplitCondition 37 K_neg8 :=
  ⟨heegner_37_neg7, not_heegner_37_neg8⟩

/-- **★★★ What `:= True` destroys.**

    The existing `HeegnerHypothesis` discards both of its arguments, so
    it *identifies* the two fields that §4 just separated: as Props,
    `ℚ(√−7)` splitting at `E_37a1` and `ℚ(√−2)` splitting at `E_37a1`
    are literally the same statement, provably, by `rfl`.

    Put beside `heegner_split_condition_is_substantive`, this is the
    precise measure of what the placeholder costs: a predicate that
    cannot distinguish a field that splits from one that does not cannot
    be a hypothesis of Gross–Zagier. -/
theorem heegner_true_identifies_distinct_fields :
    HeegnerHypothesis E_rank_one K_neg7 = HeegnerHypothesis E_rank_one K_neg8 :=
  rfl

/-- And the typed wrapper is `Nonempty ImaginaryQuadraticData`: the
    existential is witnessed by any negative discriminant whatsoever,
    because the body ignores it. -/
theorem heegnerHypothesisSatisfied_Typed_is_nonemptiness
    (E : WeierstrassCurve ℚ) : HeegnerHypothesisSatisfied_Typed E :=
  ⟨K_neg7, trivial⟩

/-! ## §5 — The remaining gap, named

What is still `True` on this axis, and what each would take.

### The two odd composite conductors, arithmetic already verified

`E_91a1` (`N = 91 = 7·13`) and `E_141a1` (`N = 141 = 3·47`) are not
proved above only because a composite conductor needs the prime divisors
enumerated, where `heegnerSplitCondition_of_prime` does not apply. The
arithmetic is done and checked; the data is:

| `N` | odd primes | `d_K` | roots |
|---|---|---|---|
| `91` | `7, 13` | `−3` | `2² = 4 ≡ −3 (mod 7)`, `6² = 10 ≡ −3 (mod 13)` |
| `141` | `3, 47` | `−11` | `1² = 1 ≡ −11 (mod 3)`, `6² = 36 ≡ −11 (mod 47)` |

Each needs one lemma of the shape
`∀ q, q.Prime → q ∣ 91 → q = 7 ∨ q = 13`, after which both follow by the
same `⟨root, by decide⟩` pattern as §3.

### The two even conductors

`E_102a1` (`102 = 2·3·17`) and `E_106a1` (`106 = 2·53`) need the
Kronecker symbol `(d ∣ 2)`, which mathlib does not have at this pin.
`HeegnerSplitCondition` excludes `p = 2` by construction, so for these
two curves it is strictly weaker than the classical hypothesis and
proving it would not be the same statement. Left alone deliberately.

### The L-derivative

Still `True`, and not repairable here: mathlib has no L-function of an
elliptic curve at this pin (zero files for `EllipticCurve.*LSeries`,
`WeierstrassCurve.*LSeries`, `analyticRank`;
`Mathlib/AlgebraicGeometry/EllipticCurve/` has no L-function module).
A faithful `L'(E,1) ≠ 0` requires the `aₙ` of `E` from point counts over
`𝔽_p`, fed through `LSeries`, plus continuation to `s = 1`. -/

/-- The faithful split condition implies the corpus's placeholder — in
    the only direction that is available, since the placeholder is
    implied by everything. Recorded so the relationship is explicit:
    the new predicate is strictly stronger. -/
theorem heegner_faithful_implies_placeholder
    (K : ImaginaryQuadraticData) (_h : HeegnerSplitCondition 37 K) :
    HeegnerHypothesisSatisfied E_rank_one :=
  trivial

/-- The split condition is strictly stronger than the placeholder: the
    placeholder holds for every curve unconditionally, while the split
    condition fails for `(37, ℚ(√−2))`. -/
theorem placeholder_is_strictly_weaker :
    (∀ E : WeierstrassCurve ℚ, HeegnerHypothesisSatisfied E) ∧
    ¬ HeegnerSplitCondition 37 K_neg8 :=
  ⟨fun _ => trivial, not_heegner_37_neg8⟩

#print axioms SplitsAt
#print axioms heegnerSplitCondition_of_prime
#print axioms splitsAt_37_neg7
#print axioms heegner_37_neg7
#print axioms heegner_split_condition_nine_curves
#print axioms not_isSquare_neg8_mod_37
#print axioms not_heegner_37_neg8
#print axioms heegner_split_condition_is_substantive
#print axioms heegner_true_identifies_distinct_fields
#print axioms heegnerHypothesisSatisfied_Typed_is_nonemptiness
#print axioms placeholder_is_strictly_weaker

end PrincipiaTractalis.BSD_HeegnerHypothesis_Faithful_2026_11_21
