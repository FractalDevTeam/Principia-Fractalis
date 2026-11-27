/-
Copyright (c) 2026 Pablo Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Cohen
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# CANDIDATE for `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`

Not a standalone file in the final PR. The three theorems below are to be
inserted into mathlib's own `Determinant/Basic.lean`, immediately after
`det_fin_three`, which is currently the last declaration before `end Matrix`.
Verified both standalone and in situ against mathlib master
`leanprover/lean4:v4.37.0-rc1`.

## What this adds, and why

That file provides `det_fin_one`, `det_fin_one_of`, `det_fin_two`,
`det_fin_two_of` and `det_fin_three`. Two members of the family are missing:

* **`det_fin_three_of`** — the `!![...]` form, which `det_fin_one` and
  `det_fin_two` both have. Its absence looks like an oversight rather than a
  decision.
* **`det_fin_four` / `det_fin_four_of`** — the next case. Expanding a `4 × 4`
  determinant through `det_succ_row_zero` by hand is a recurring small cost,
  and the `succAbove` bookkeeping at the last column is a genuine trap (see the
  comment in the proof).

## Two deliberate choices a reviewer may want to discuss

1. **`det_fin_three_of` is `@[simp]`, `det_fin_four_of` is not.**
   `det_fin_two_of` is `@[simp]` and rewrites to 2 terms; three gives 6, which
   is comparable. Four gives **24**, which is large for the default simp set, so
   it is left off deliberately rather than by omission.
2. **The `det_fin_four` right-hand side is the full Leibniz expansion**, ordered
   as `det_fin_three`'s is — lexicographically by `(σ 0, σ 1, σ 2, σ 3)`. It was
   generated programmatically, not typed, and cross-checked against an
   independent Laplace expansion along row 0 on 500 random rational matrices.
   `det_fin_four_of` is proved as `det_fin_four _`, so the compiler verifies the
   letter form against the index form; the lettering is not asserted.
-/

namespace Matrix

variable {R : Type*} [CommRing R]

@[simp]
theorem det_fin_three_of (a b c d e f g h i : R) :
    Matrix.det !![a, b, c; d, e, f; g, h, i] =
      a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
  det_fin_three _

/-- Determinant of 4x4 matrix -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    det A =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2
      - A 0 0 * A 1 2 * A 2 1 * A 3 3 + A 0 0 * A 1 2 * A 2 3 * A 3 1
      + A 0 0 * A 1 3 * A 2 1 * A 3 2 - A 0 0 * A 1 3 * A 2 2 * A 3 1
      - A 0 1 * A 1 0 * A 2 2 * A 3 3 + A 0 1 * A 1 0 * A 2 3 * A 3 2
      + A 0 1 * A 1 2 * A 2 0 * A 3 3 - A 0 1 * A 1 2 * A 2 3 * A 3 0
      - A 0 1 * A 1 3 * A 2 0 * A 3 2 + A 0 1 * A 1 3 * A 2 2 * A 3 0
      + A 0 2 * A 1 0 * A 2 1 * A 3 3 - A 0 2 * A 1 0 * A 2 3 * A 3 1
      - A 0 2 * A 1 1 * A 2 0 * A 3 3 + A 0 2 * A 1 1 * A 2 3 * A 3 0
      + A 0 2 * A 1 3 * A 2 0 * A 3 1 - A 0 2 * A 1 3 * A 2 1 * A 3 0
      - A 0 3 * A 1 0 * A 2 1 * A 3 2 + A 0 3 * A 1 0 * A 2 2 * A 3 1
      + A 0 3 * A 1 1 * A 2 0 * A 3 2 - A 0 3 * A 1 1 * A 2 2 * A 3 0
      - A 0 3 * A 1 2 * A 2 0 * A 3 1 + A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  -- The three `succAbove` values the row-0 expansion leaves behind. Note the
  -- asymmetry: at the last column the `castSucc` branch is taken, so
  -- `succAbove 3 2 = 2`, while the other two give `3`.
  have e1 : (1 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have e2 : (2 : Fin 4).succAbove (2 : Fin 3) = 3 := by decide
  have e3 : (3 : Fin 4).succAbove (2 : Fin 3) = 2 := by decide
  rw [det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, e1, e2, e3]
  ring

-- Not `@[simp]`: unlike `det_fin_two_of` and `det_fin_three_of`, this rewrites
-- to 24 terms, which is too large for the default simp set.
theorem det_fin_four_of (a b c d e f g h i j k l m n o p : R) :
    Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] =
      a * f * k * p - a * f * l * o - a * g * j * p + a * g * l * n
      + a * h * j * o - a * h * k * n - b * e * k * p + b * e * l * o
      + b * g * i * p - b * g * l * m - b * h * i * o + b * h * k * m
      + c * e * j * p - c * e * l * n - c * f * i * p + c * f * l * m
      + c * h * i * n - c * h * j * m - d * e * j * o + d * e * k * n
      + d * f * i * o - d * f * k * m - d * g * i * n + d * g * j * m :=
  det_fin_four _

end Matrix
