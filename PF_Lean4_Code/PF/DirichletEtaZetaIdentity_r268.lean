/-
# r268: DIRICHLET ETA-ZETA IDENTITY ON `1 < re s`.

★ 2026-08-14 r268 — the classical identity
  `η(s) = (1 - 2^(1-s)) · ζ(s)`
formalised for the complex Dirichlet eta of r267 and mathlib's
`riemannZeta`, on the domain of absolute convergence `1 < re s`.

The proof is the standard even/odd split:
  `ζ(s) - η(s) = Σ_{n ≥ 1, n even} 2/n^s = 2 · Σ_{k ≥ 1} 1/(2k)^s
              = 2 · 2^(-s) · ζ(s) = 2^(1-s) · ζ(s)`
hence `η(s) = (1 - 2^(1-s)) · ζ(s)`.

## What r268 adds

- `zeta_sub_eta_even_hasSum`:
  `HasSum (fun k : ℕ => term (1 : ℕ → ℂ) s (2*k) - term dirichletEtaCoeff s (2*k))
         (2^(1-s) · riemannZeta s)`
  — the "even part" of the term-wise difference sums to `2^(1-s) · ζ(s)`.

- `zeta_sub_eta_odd_hasSum`:
  `HasSum (fun k : ℕ => term (1 : ℕ → ℂ) s (2*k+1) - term dirichletEtaCoeff s (2*k+1)) 0`
  — the "odd part" of the term-wise difference is identically zero.

- `zeta_sub_eta_hasSum`:
  `HasSum (fun n => term (1 : ℕ → ℂ) s n - term dirichletEtaCoeff s n)
         (2^(1-s) · riemannZeta s)`
  — combining even + odd via `HasSum.even_add_odd`.

- `dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta`:
  `dirichletEta s = (1 - (2 : ℂ)^(1 - s)) · riemannZeta s`
  for `1 < re s`. Concludes via `HasSum.unique` against
  `LSeriesHasSum_one - dirichletEta_hasSum`.

## Route B substrate value

r268 formalises the Euler identity that r266 exposed as the ONE
missing analytical hypothesis on the Route B path. Downstream:
- r269 will extend to `0 < re s` via analytic continuation of η.
- r270 will specialise to `s = 1/2` and combine with r265.
- r271 will discharge the r266 conditional hypothesis outright.

## Scope

* NOT novel — the eta-zeta functional identity is classical.
* NOT a Millennium discharge.
* IS the complex-side identity brick on the Dirichlet-eta path.

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`. Kernel-only.
-/

import PF.DirichletEtaComplex_r267

open scoped Real

namespace PrincipiaTractalis.DirichletEtaZetaIdentity

open Complex LSeries
open PrincipiaTractalis.DirichletEtaComplex

/-! ## §1 Coefficient facts. -/

/-- **`dirichletEtaCoeff_two_mul`** — for `k ≥ 1`,
`dirichletEtaCoeff (2 k) = -1`. Uses `(-1)^(2k+1) = -1`. -/
lemma dirichletEtaCoeff_two_mul {k : ℕ} (hk : k ≠ 0) :
    dirichletEtaCoeff (2 * k) = -1 := by
  have h2k : (2 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by decide) hk
  unfold dirichletEtaCoeff
  rw [if_neg h2k]
  have h_par : 2 * k + 1 = 2 * k + 1 := rfl
  rw [show (2 * k + 1 : ℕ) = 2 * k + 1 from rfl, pow_add, pow_mul, pow_one]
  have h_sq : ((-1 : ℂ) ^ 2) ^ k = 1 := by
    rw [show ((-1 : ℂ) ^ 2) = 1 by norm_num, one_pow]
  rw [h_sq, one_mul]

/-- **`dirichletEtaCoeff_two_mul_add_one`** — for all `k : ℕ`,
`dirichletEtaCoeff (2k+1) = 1`. Uses `(-1)^(2k+2) = 1`. -/
lemma dirichletEtaCoeff_two_mul_add_one (k : ℕ) :
    dirichletEtaCoeff (2 * k + 1) = 1 := by
  have h_odd_ne : (2 * k + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
  unfold dirichletEtaCoeff
  rw [if_neg h_odd_ne]
  have h_rw : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  rw [h_rw, pow_mul]
  have h_sq : ((-1 : ℂ) ^ 2) = 1 := by norm_num
  rw [h_sq, one_pow]

/-! ## §2 Termwise algebra of the difference. -/

/-- **`term_one_sub_term_eta_even`** — for `k : ℕ` and `s : ℂ`, the even-index
difference `term 1 s (2k) - term dirichletEtaCoeff s (2k)` equals
`(2 : ℂ)^(1 - s) · term 1 s k`. Pointwise identity — no summability needed. -/
lemma term_one_sub_term_eta_even (s : ℂ) (k : ℕ) :
    term (1 : ℕ → ℂ) s (2 * k) - term dirichletEtaCoeff s (2 * k) =
      (2 : ℂ) ^ (1 - s) * term (1 : ℕ → ℂ) s k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have h2k : (2 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by decide) hk
    have hk_cast : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have h2c : (2 : ℂ) ≠ 0 := by norm_num
    have h_eta : dirichletEtaCoeff (2 * k) = -1 := dirichletEtaCoeff_two_mul hk
    -- Unfold all three `term _ s _` calls.
    rw [LSeries.term_of_ne_zero h2k, LSeries.term_of_ne_zero h2k,
        LSeries.term_of_ne_zero hk]
    rw [h_eta]
    have h_one_val : (1 : ℕ → ℂ) (2 * k) = 1 := rfl
    have h_one_k : (1 : ℕ → ℂ) k = 1 := rfl
    rw [h_one_val, h_one_k]
    -- Split `((2 * k : ℕ) : ℂ) ^ s = (2 : ℂ)^s * (k : ℂ)^s`.
    have h_split : ((2 * k : ℕ) : ℂ) ^ s = (2 : ℂ) ^ s * ((k : ℕ) : ℂ) ^ s := by
      have := natCast_mul_natCast_cpow 2 k s
      simpa using this
    rw [h_split]
    -- Now: 1 / (2^s * k^s) - -1 / (2^s * k^s) = 2^(1-s) * (1 / k^s)
    have h_pow_diff : (2 : ℂ) ^ (1 - s) = (2 : ℂ) / (2 : ℂ) ^ s := by
      rw [Complex.cpow_sub _ _ h2c, cpow_one]
    rw [h_pow_diff]
    have h2s_ne : (2 : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2c)
    have hks_ne : ((k : ℕ) : ℂ) ^ s ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hk_cast)
    field_simp
    ring

/-- **`term_one_eq_term_eta_odd`** — for `k : ℕ` and `s : ℂ`, the odd-index
values of `term 1 s` and `term dirichletEtaCoeff s` agree because
`(-1)^(2k+2) = 1`. Pointwise identity. -/
lemma term_one_eq_term_eta_odd (s : ℂ) (k : ℕ) :
    term (1 : ℕ → ℂ) s (2 * k + 1) = term dirichletEtaCoeff s (2 * k + 1) := by
  have h_odd_ne : (2 * k + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
  rw [LSeries.term_of_ne_zero h_odd_ne, LSeries.term_of_ne_zero h_odd_ne]
  rw [dirichletEtaCoeff_two_mul_add_one]
  rfl

/-! ## §3 Even and odd HasSum bricks. -/

/-- **`zeta_sub_eta_even_hasSum`** — the term-wise "even part" of
`ζ − η` sums to `2^(1-s) · ζ(s)`.

Proof: pointwise-eq to `2^(1-s) · term 1 s k`, then `HasSum.mul_left`
of `LSeriesHasSum_one`. -/
theorem zeta_sub_eta_even_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => term (1 : ℕ → ℂ) s (2 * k) -
              term dirichletEtaCoeff s (2 * k))
           ((2 : ℂ) ^ (1 - s) * riemannZeta s) := by
  have h_zeta : HasSum (term (1 : ℕ → ℂ) s) (riemannZeta s) := LSeriesHasSum_one hs
  have h_scaled : HasSum (fun k => (2 : ℂ) ^ (1 - s) * term (1 : ℕ → ℂ) s k)
      ((2 : ℂ) ^ (1 - s) * riemannZeta s) := h_zeta.mul_left _
  have h_eq : (fun k : ℕ => term (1 : ℕ → ℂ) s (2 * k) -
                term dirichletEtaCoeff s (2 * k)) =
              fun k => (2 : ℂ) ^ (1 - s) * term (1 : ℕ → ℂ) s k := by
    funext k
    exact term_one_sub_term_eta_even s k
  rw [h_eq]
  exact h_scaled

/-- **`zeta_sub_eta_odd_hasSum`** — the term-wise "odd part" of
`ζ − η` is identically zero. -/
theorem zeta_sub_eta_odd_hasSum (s : ℂ) :
    HasSum (fun k : ℕ => term (1 : ℕ → ℂ) s (2 * k + 1) -
              term dirichletEtaCoeff s (2 * k + 1)) 0 := by
  have h_eq : (fun k : ℕ => term (1 : ℕ → ℂ) s (2 * k + 1) -
                term dirichletEtaCoeff s (2 * k + 1)) = (fun _ : ℕ => (0 : ℂ)) := by
    funext k
    rw [term_one_eq_term_eta_odd, sub_self]
  rw [h_eq]
  exact hasSum_zero

/-! ## §4 Combined difference HasSum. -/

/-- **`zeta_sub_eta_hasSum`** — the full term-wise difference sums to
`2^(1-s) · ζ(s)`, via `HasSum.even_add_odd`. -/
theorem zeta_sub_eta_hasSum {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => term (1 : ℕ → ℂ) s n - term dirichletEtaCoeff s n)
           ((2 : ℂ) ^ (1 - s) * riemannZeta s) := by
  set f : ℕ → ℂ := fun n => term (1 : ℕ → ℂ) s n - term dirichletEtaCoeff s n
    with hf_def
  have h_even : HasSum (fun k => f (2 * k)) ((2 : ℂ) ^ (1 - s) * riemannZeta s) :=
    zeta_sub_eta_even_hasSum hs
  have h_odd : HasSum (fun k => f (2 * k + 1)) 0 :=
    zeta_sub_eta_odd_hasSum s
  have h := h_even.even_add_odd h_odd
  rw [add_zero] at h
  exact h

/-! ## §5 The eta-zeta identity on `1 < re s`. -/

/-- **`dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta`** — the classical
identity `η(s) = (1 − 2^{1−s}) · ζ(s)` on `1 < re s`.

Proof: by `HasSum.sub` on `LSeriesHasSum_one` and `dirichletEta_hasSum`
we get `HasSum (fun n => term 1 s n - term eta s n) (ζ − η)`. By
`HasSum.unique` against `zeta_sub_eta_hasSum` we get
`ζ − η = 2^{1−s} · ζ`, and rearranging yields the identity. -/
theorem dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    dirichletEta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h_zeta : HasSum (term (1 : ℕ → ℂ) s) (riemannZeta s) := LSeriesHasSum_one hs
  have h_eta : HasSum (term dirichletEtaCoeff s) (dirichletEta s) := dirichletEta_hasSum hs
  have h_diff : HasSum (fun n => term (1 : ℕ → ℂ) s n - term dirichletEtaCoeff s n)
                       (riemannZeta s - dirichletEta s) := h_zeta.sub h_eta
  have h_target : HasSum (fun n => term (1 : ℕ → ℂ) s n - term dirichletEtaCoeff s n)
                         ((2 : ℂ) ^ (1 - s) * riemannZeta s) :=
    zeta_sub_eta_hasSum hs
  have h_eq : riemannZeta s - dirichletEta s = (2 : ℂ) ^ (1 - s) * riemannZeta s :=
    h_diff.unique h_target
  linear_combination -h_eq

/-! ## §6 Axiom check. -/

#print axioms PrincipiaTractalis.DirichletEtaZetaIdentity.zeta_sub_eta_even_hasSum
#print axioms PrincipiaTractalis.DirichletEtaZetaIdentity.zeta_sub_eta_odd_hasSum
#print axioms PrincipiaTractalis.DirichletEtaZetaIdentity.zeta_sub_eta_hasSum
#print axioms PrincipiaTractalis.DirichletEtaZetaIdentity.dirichletEta_eq_one_sub_two_cpow_mul_riemannZeta

end PrincipiaTractalis.DirichletEtaZetaIdentity
