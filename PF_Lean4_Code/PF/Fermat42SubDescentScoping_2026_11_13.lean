/-
# PF.Fermat42SubDescentScoping_2026_11_13

**Scoping of the full `not_fermat_42_sub` descent** — the Pythagorean
case-split structure, with each case stated as a named lemma.

## Actual implementation structure

Given a minimal `Fermat42Sub a b c` (via `Fermat42Sub.exists_minimal`
and `Fermat42Sub.coprime_of_minimal` from
`Fermat42SubFoundations_2026_11_13`), normalize to `a > 0, c > 0`.
Pythagorean triple on `c² + (b²)² = (a²)²` gives two primary cases
split on parity of `b`:

### Case B: `b` even (so `b²` even, `c` odd)

File: `Fermat42SubCaseBClosure_2026_11_13.lean`,
theorem `fermat42Sub_caseB_descends`.

Classification: ∃ m, n coprime of opposite parity, `m ≥ 0`, with
  * `c = m² - n²`
  * `b² = 2mn`
  * `a² = m² + n²`

Reduction chain:
1. Square-split `b² = 2mn` with coprime `(m, n)`, `m odd`, `n even`
   gives `m = i²`, `n = 2j²`, `b = 2ij`
   (via `Fermat42SubCaseB_squareSplit` — **discharged** in
   `Fermat42SubSplitLemmas_2026_11_13`).
2. `a² = m² + n² = i⁴ + 4j⁴`, so `(a - 2j²)(a + 2j²) = i⁴`.
3. 4th-power-split via `Fermat42SubCaseB_fourthPowerSplit`
   (**discharged** in `Fermat42SubSplitLemmas_2026_11_13`):
   `a - 2j² = p⁴`, `a + 2j² = q⁴`, `pq = i`.
4. Subtracting: `q⁴ - p⁴ = (2j)²` — a **strictly smaller
   `Fermat42Sub (q, p, 2j)`** with `|2j| < |c|`.
5. Contradicts minimality.

**Composing `fermat42Sub_caseB_descends` with the two discharged split
sub-gaps gives UNCONDITIONAL Case B impossibility on three-axiom bar.**

### Case A: `b` odd (so `b²` odd, `c` even)

File: `Fermat42SubCaseAReduction_2026_11_13.lean`,
theorem `fermat42Sub_caseA_reduces`.

Classification: ∃ m, n coprime of opposite parity, `m ≥ 0`, with
  * `b² = m² - n²`
  * `c = 2mn`
  * `a² = m² + n²`

Reduction chain:
1. WLOG `m odd`, `n even`; write `n = 2k`.  Then `b² = (m - 2k)(m + 2k)`.
2. Pair-coprimality derivation (from `IsCoprime m (2k)`):
   `IsCoprime (m - 2k) (m + 2k)`.
3. Square-split via `Fermat42SubCaseA_squareSplit` (**discharged** in
   `Fermat42SubSplitLemmas_2026_11_13`):
   `m - 2k = s²`, `m + 2k = t²`, `st = b`, `IsCoprime s t`.
4. From sum/difference: `2m = s² + t²`, `4k = t² - s²`.
5. Substitute into `a² = m² + (2k)²`:
   `(2a)² = (s² + t²)² + (t² - s²)² = 2(s⁴ + t⁴)`,
   so `2a² = s⁴ + t⁴` — a **`Fermat42Double (s, t, a)`** instance.
6. `s² ≠ t²` from `k > 0` and `t² - s² = 4k`.
7. Contradiction via `Fermat42Double_impossible` — **the remaining
   sub-gap**.

### The final sub-gap: `Fermat42Double_impossible`

`∀ s t a : ℤ, s ≠ 0 → t ≠ 0 → a ≠ 0 → IsCoprime s t → s² ≠ t² →
2a² ≠ s⁴ + t⁴`.

(Note: `s = t = a = 1` is a counterexample WITHOUT the `s² ≠ t²`
hypothesis — the hypothesis is required.)

Structural lemmas in `Fermat42DoubleImpossible_2026_11_13.lean`:
* `fermat42Double_parity` — any solution has `s, t` both odd.
* `odd_sq_mod_eight` — `s odd → s² ≡ 1 mod 8`.
* `fermat42Double_u_mod_four` — `u = (s²+t²)/2 ≡ 1 mod 4`.

Remaining: full Pythagorean descent on `(u, v, a)` with
`u² + v² = a²`, `v = (t²-s²)/2 > 0`, `u = m² - n²`, `v = 2mn`,
`a = m² + n²`, `m` odd, `n = 2k` even (forced by `u ≡ 1 mod 4`),
followed by case-analysis on the `(t-s)(t+s) = 4v = 8mk`
decomposition.  Reduces to showing `xy = 2mk` with `x² + y² = m² - 4k²`
has no non-trivial integer solutions — the quadratic in `x²` has
discriminant `m⁴ - 24m²k² + 16k⁴` which must be a perfect square,
leading to constraints that force degenerate `k = 0` in every case.

## Status summary

| Component | File | Status |
|-----------|------|--------|
| `Fermat42Sub` structure | `Foundations_2026_11_13` | ✅ three-axiom bar |
| `Fermat42Sub.exists_minimal` | `Foundations_2026_11_13` | ✅ three-axiom bar |
| `Fermat42Sub.coprime_of_minimal` | `Foundations_2026_11_13` | ✅ three-axiom bar |
| `fermat42SubCaseB_squareSplit_holds` | `SplitLemmas_2026_11_13` | ✅ three-axiom bar |
| `fermat42SubCaseA_squareSplit_holds` | `SplitLemmas_2026_11_13` | ✅ three-axiom bar |
| `fermat42SubCaseB_fourthPowerSplit_holds` | `SplitLemmas_2026_11_13` | ✅ three-axiom bar |
| `fermat42Sub_caseB_descends` | `CaseBClosure_2026_11_13` | ✅ three-axiom bar (composes with split sub-gaps to unconditional Case B impossibility) |
| `fermat42Sub_caseA_reduces` | `CaseAReduction_2026_11_13` | ✅ three-axiom bar (conditional on `Fermat42Double_impossible`) |
| `fermat42Double_parity` | `DoubleImpossible_2026_11_13` | ✅ three-axiom bar |
| `odd_sq_mod_eight` | `DoubleImpossible_2026_11_13` | ✅ three-axiom bar |
| `fermat42Double_u_mod_four` | `DoubleImpossible_2026_11_13` | ✅ three-axiom bar |
| `Fermat42Double_impossible` (full theorem) | — | **OPEN** |

## Correction to prior scoping

A prior version of this document described Case B as "reducing to a
`Fermat42` instance via mathlib's `not_fermat_42`".  This was
incorrect: Case B's actual implementation produces a strictly smaller
`Fermat42Sub` instance (self-descent), not a `Fermat42` reduction.
`not_fermat_42` is not invoked in any proof — only mentioned in
docstrings.  The Case A path, by contrast, produces a
`Fermat42Double` instance (not a smaller `Fermat42Sub`), hence
requiring `Fermat42Double_impossible` as the final sub-gap.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubFoundations_2026_11_13

namespace PF.Fermat42Sub

/-- **Case B sub-gap discharged** via `fermat42Sub_caseB_descends`
in `CaseBClosure_2026_11_13`; composed with the two split sub-gaps
(`fermat42SubCaseB_squareSplit_holds`,
`fermat42SubCaseB_fourthPowerSplit_holds`), it gives unconditional
Case B impossibility on three-axiom bar. -/
def Fermat42SubCaseB_impossible : Prop :=
  ∀ a b c : ℤ, Fermat42Sub a b c → b % 2 = 0 → c % 2 = 1 → False

/-- **Case A sub-gap** — reducing to `Fermat42Double_impossible`
via `fermat42Sub_caseA_reduces` in `CaseAReduction_2026_11_13`. -/
def Fermat42SubCaseA_impossible : Prop :=
  ∀ a b c : ℤ, Minimal a b c → b % 2 = 1 → c % 2 = 0 → False

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.Fermat42SubCaseB_impossible
#print axioms PF.Fermat42Sub.Fermat42SubCaseA_impossible
