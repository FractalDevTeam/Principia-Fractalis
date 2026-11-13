/-
# PF.Fermat42SubDescentScoping_2026_11_13

**Scoping of the full `not_fermat_42_sub` descent** — the Pythagorean
case-split structure, with each case stated as a named lemma whose
proof is the substantial remaining work.

## Delivered: scoping only

Two named sub-gap PREDICATES capture the descent structure.  Their
proofs are the ~100 Lean lines of Pythagorean case analysis and are
left to a dedicated descent session.

## The two cases

Given a minimal `Fermat42Sub a b c` (via `Fermat42Sub.exists_minimal`
and `Fermat42Sub.coprime_of_minimal` from
`Fermat42SubFoundations_2026_11_13`), after normalizing to
`a > 0, c > 0`, the Pythagorean triple classification on
`c² + (b²)² = (a²)²` gives two primary cases:

### Case A: `b` odd (so `b²` odd, `c` even)
Classification: ∃ m, n coprime of opposite parity, m ≥ 0, m > n, with
  * `b² = m² - n²`
  * `c = 2mn`
  * `a² = m² + n²`

After applying a second Pythagorean classification to `a² = m² + n²`,
derive a new instance `u² = p⁴ - q⁴` (smaller `Fermat42Sub`) — contradicts
minimality.

### Case B: `b` even (so `b²` even, `c` odd)
Classification: ∃ m, n coprime of opposite parity, m ≥ 0, m > n, with
  * `c = m² - n²`
  * `b² = 2mn`
  * `a² = m² + n²`

After the second Pythagorean classification + coprime-decomposition
of `b² = 4mrs`, derive `i² = j⁴ + k⁴` — a **`Fermat42` instance**
excluded by mathlib's `not_fermat_42`.

### Parity derivation

Standard modular argument:
* `b` odd ⟹ `c` even (via `b⁴ + c² = a⁴` mod 4).
* `b` even + `gcd(a,b) = 1` ⟹ `a` odd ⟹ `c` odd.

Named predicates below capture each sub-case.

## Combined conclusion

Once both sub-gap predicates are universally true,
`not_fermat_42_sub : ∀ a b c, ¬ Fermat42Sub a b c` follows by:
1. Take minimal counterexample.
2. Case split on parity of `b`.
3. Apply the appropriate case closure to derive contradiction.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen. 2026-11-13.
-/

import PF.Fermat42SubFoundations_2026_11_13

namespace PF.Fermat42Sub

/-- **Case A sub-gap**: if `Fermat42Sub a b c` is minimal with `b` odd
and `c` even, then there exists a `Fermat42Sub` instance with strictly
smaller `|c|` — contradicting minimality.

Proof sketch:
1. Pythagorean classification of `(b², c, a²)`: ∃ m, n coprime of
   opposite parity with `b² = m² - n², c = 2mn, a² = m² + n²`.
2. Pythagorean classification of `(n, m, a)` (from `a² = m² + n²`):
   ∃ r, s coprime of opposite parity with `a = r² - s², n = 2rs,
   m = r² + s²`.
3. From `b² = m² - n²` and the (r, s) parameterization, derive an
   equation of the form `u² = p⁴ - q⁴` with smaller `|u|`.
4. The new instance is strictly smaller in `|c|`.

Estimated ~50-60 Lean lines. -/
def Fermat42SubCaseA_descent : Prop :=
  ∀ a b c : ℤ, Minimal a b c → b % 2 = 1 → c % 2 = 0 →
    ∃ a1 b1 c1 : ℤ, Fermat42Sub a1 b1 c1 ∧ Int.natAbs c1 < Int.natAbs c

/-- **Case B sub-gap**: if `Fermat42Sub a b c` with `b` even and `c`
odd, then reduction via Pythagorean classification gives a `Fermat42`
instance (excluded by mathlib's `not_fermat_42`), yielding
contradiction directly.

Proof sketch:
1. Pythagorean classification of `(c, b², a²)`: ∃ m, n coprime of
   opposite parity with `c = m² - n², b² = 2mn, a² = m² + n²`.
2. Pythagorean classification of `(n, m, a)`: ∃ r, s coprime with
   `a = r² - s², n = 2rs, m = r² + s²`.
3. `b² = 2mn = 4mrs`. Coprime decomposition on (m, r, s) via gcd
   arguments: each is a square — `m = i², r = j², s = k²`.
4. `m = r² + s² ⟹ i² = j⁴ + k⁴`.
5. Apply mathlib's `not_fermat_42 j k i` for contradiction.

Estimated ~50-60 Lean lines. -/
def Fermat42SubCaseB_impossible : Prop :=
  ∀ a b c : ℤ, Fermat42Sub a b c → b % 2 = 0 → c % 2 = 1 → False

end PF.Fermat42Sub

/-! ## §Axiom check -/
#print axioms PF.Fermat42Sub.Fermat42SubCaseA_descent
#print axioms PF.Fermat42Sub.Fermat42SubCaseB_impossible
