There are no non-zero integers `a`, `b`, `c` with `a^4 - b^4 = c^2` — the "difference form" of Fermat's n=4 theorem. This is the companion to mathlib's `not_fermat_42` (sum form `a^4 + b^4 = c^2`, `Mathlib.NumberTheory.FLT.Four`); together the two theorems close both diophantine shapes of Fermat's n=4 case.

Contents (mirrors `Fermat42`/`Fermat42.Minimal`/`not_fermat_42` for the sum form):
- `Fermat42Sub (a b c : ℤ) : Prop` — the predicate `a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a^4 - b^4 = c^2` (nonzero `c` required to exclude the `a = ±b, c = 0` family);
- `Fermat42Sub.Minimal`, `exists_minimal`, `coprime_of_minimal`, scaling `Fermat42Sub.mul`;
- Pythagorean descent case split on parity of `b`:
  - `b` odd (Case A): reduces to the classical auxiliary equation `2a^2 = s^4 + t^4` with coprime `s, t` and `s^2 ≠ t^2`, which is itself impossible by infinite descent (`fermat42Double_impossible_unconditional` — Pythagorean classification on `u^2 + v^2 = a^2`, two parallel coprime factorizations, UFD 4-way split into `(a', b, c, d)` satisfying `k = a' b c d` and the key relation `4 a' b c d = (c^2 - b^2)(2 a'^2 - d^2)`, completing the square to force `2 e^2 = b^4 + c^4` with `|e| ≤ k^2 < a`);
  - `b` even (Case B): direct infinite descent on `Fermat42Sub` via square-split + 4th-power-split, with a parity mirror for the `c ≡ 3 mod 4` Pythagorean classification sub-case.

All declarations report axioms `[propext, Classical.choice, Quot.sound]`.

Parts of this contribution were developed with AI assistance (Claude). All statements are machine-checked by the Lean kernel.
