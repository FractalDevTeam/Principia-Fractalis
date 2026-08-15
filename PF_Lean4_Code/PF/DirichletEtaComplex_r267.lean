/-
# r267: DIRICHLET ETA AS A COMPLEX L-SERIES.

★ 2026-08-13 r267 — the next brick on the Dirichlet-eta path. Defines
Dirichlet eta as a complex function using mathlib's `LSeries` framework,
and proves summability on the right half-plane `1 < re s`.

Follows the pattern of `LSeries_zeta_eq_riemannZeta` in
`Mathlib/NumberTheory/LSeries/Dirichlet.lean`.

## What r267 adds

- `dirichletEtaCoeff : ℕ → ℂ`:
  `dirichletEtaCoeff 0 = 0` (LSeries convention) and
  `dirichletEtaCoeff n = (-1)^(n+1)` for `n ≥ 1`, i.e., `1, -1, 1, -1, …`.

- `dirichletEta (s : ℂ) : ℂ := LSeries dirichletEtaCoeff s`
  — the mathlib-native Dirichlet series encoding of
  `η(s) = Σ_{n=1}^∞ (-1)^{n+1}/n^s`.

- `dirichletEtaCoeff_norm_le_one`:
  `∀ n : ℕ, n ≠ 0 → ‖dirichletEtaCoeff n‖ = 1` — the coefficients
  are bounded (they are units on the unit circle).

- `dirichletEta_summable`:
  `1 < re s → LSeriesSummable dirichletEtaCoeff s` — via mathlib's
  `LSeriesSummable_of_bounded_of_one_lt_re`.

- `dirichletEta_hasSum`:
  `1 < re s → LSeriesHasSum dirichletEtaCoeff s (dirichletEta s)` —
  the packaged HasSum form.

## Route B substrate value

r267 makes Dirichlet eta a first-class complex function in the corpus.
Downstream bricks will:
- r268 — prove `dirichletEta s = (1 - 2^(1-s)) · riemannZeta s` for
  `1 < re s` via series regrouping.
- r269 — extend by analytic continuation to `0 < re s`.
- r270 — specialize to `s = 1/2` and match the r265 real-valued
  `dirichletEtaHalf` from the alternating-series construction.
- r271 — inhabit the r266 conditional hypothesis, unconditionally
  discharging Route B fact (a).

## Scope

* NOT novel — Dirichlet eta as an L-series is elementary.
* NOT a Millennium discharge.
* IS the complex-side setup on the Dirichlet-eta path.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet

open scoped Real

namespace PrincipiaTractalis.DirichletEtaComplex

open Complex

/-! ## §1 Coefficients. -/

/-- **`dirichletEtaCoeff`** — Dirichlet eta coefficients as required by
mathlib's `LSeries` convention: `f 0 = 0` and `f n = (-1)^(n+1)` for
`n ≥ 1`. Gives the sign pattern `1, -1, 1, -1, …` for `n = 1, 2, 3, 4, …`. -/
noncomputable def dirichletEtaCoeff (n : ℕ) : ℂ :=
  if n = 0 then 0 else (-1 : ℂ)^(n + 1)

/-- **`dirichletEtaCoeff_norm_le_one`** — for `n ≥ 1`,
`‖dirichletEtaCoeff n‖ = 1`. Uniform bound needed for LSeries
summability on `1 < re s`. -/
theorem dirichletEtaCoeff_norm_le_one (n : ℕ) (hn : n ≠ 0) :
    ‖dirichletEtaCoeff n‖ ≤ 1 := by
  unfold dirichletEtaCoeff
  rw [if_neg hn]
  simp [norm_pow]

/-! ## §2 The complex Dirichlet eta function. -/

/-- **`dirichletEta`** — the Dirichlet eta function, defined as the
`LSeries` of `dirichletEtaCoeff`. -/
noncomputable def dirichletEta (s : ℂ) : ℂ :=
  LSeries dirichletEtaCoeff s

/-! ## §3 Summability on the right half-plane. -/

/-- **`dirichletEta_summable`** — the LSeries defining `dirichletEta`
converges absolutely for `1 < re s`. Via mathlib's
`LSeriesSummable_of_bounded_of_one_lt_re` and the bound
`‖dirichletEtaCoeff n‖ ≤ 1`. -/
theorem dirichletEta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable dirichletEtaCoeff s :=
  LSeriesSummable_of_bounded_of_one_lt_re dirichletEtaCoeff_norm_le_one hs

/-- **`dirichletEta_hasSum`** — packaged HasSum form: the LSeries term
sequence sums to `dirichletEta s` on `1 < re s`. -/
theorem dirichletEta_hasSum {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum dirichletEtaCoeff s (dirichletEta s) :=
  (dirichletEta_summable hs).LSeriesHasSum

/-! ## §4 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaComplex.dirichletEtaCoeff_norm_le_one
#print axioms PrincipiaTractalis.DirichletEtaComplex.dirichletEta_summable
#print axioms PrincipiaTractalis.DirichletEtaComplex.dirichletEta_hasSum

end PrincipiaTractalis.DirichletEtaComplex
