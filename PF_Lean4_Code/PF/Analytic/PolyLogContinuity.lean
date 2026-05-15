/-
# Polylog Continuity in `s`

The deepest analytic-content piece of the polylog-route axiom retirement:
proving continuity of `polyLog s z` in the parameter `s ∈ ℂ`.

**The formal definition** (from `PF.Analytic.Polylog`):
```
polyLog (s : ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, z^(n+1) / (↑(n+1))^s
```

**Continuity analysis**:

* **Termwise**: each map `s ↦ z^(n+1) / (n+1)^s` is continuous in `s`.
  For fixed `z` and `n`, the term equals `z^(n+1) · exp(-s · log(n+1))`,
  a product of a constant with `exp` composed with a linear function
  of `s`. Continuous.

* **Series convergence**:
  - For `|z| < 1`: absolutely convergent for all `s`, uniformly on
    half-planes `Re s ≥ σ`. Continuity by Weierstrass M-test.
  - For `|z| = 1, z ≠ 1`: conditionally convergent for `Re s > 0`
    (Dirichlet test). Continuity by Abel's theorem, but the formal
    `tsum` may not capture the analytic continuation.
  - For `|z| > 1`: series diverges; the "right" polylog is the
    analytic continuation via Hankel representation.

For our `z_book = exp(I·π·√2)` with `|z_book| = 1, z_book ≠ 1`, the
formal `tsum` series converges conditionally. The CONTINUITY in `s`
comes from analytic continuation — provided by the Hankel-route chain
(mechanized in modules 1-17 of the polylog route).

This file:
* Proves **termwise continuity**: each term in the polylog series is
  continuous in `s`.
* Documents the path to full polylog continuity via analytic
  continuation.

Stage L4 — Polylog continuity (termwise + framework).
-/

import PF.Analytic.ZBookNeOne

namespace PrincipiaTractalis.Analytic

open Complex

/-! ## Termwise continuity -/

/-- **Term continuity**: for any `z ∈ ℂ` and `n : ℕ`, the function
    `s ↦ z^(n+1) / (n+1)^s` is continuous in `s ∈ ℂ`.

    Proof: the term equals `z^(n+1) · ((n+1 : ℂ))^(-s)`. Since `n+1 > 0`,
    the base `(n+1 : ℂ)` is in `slitPlane`, so `s ↦ (n+1)^(-s)` is
    continuous (cpow continuous in exponent for nonzero base). Times
    the constant `z^(n+1)`, still continuous. -/
theorem continuous_polyLog_term (z : ℂ) (n : ℕ) :
    Continuous (fun s : ℂ => z^(n+1) / ((n+1 : ℕ) : ℂ)^s) := by
  -- (n+1 : ℂ) ≠ 0 since n+1 ≥ 1 > 0
  have h_ne : ((n+1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  -- s ↦ (n+1)^s is continuous (cpow continuous in exponent for nonzero base)
  have h_cpow : Continuous (fun s : ℂ => ((n+1 : ℕ) : ℂ)^s) := by
    -- (n+1)^s = exp(s · log(n+1))
    have h_rewrite : (fun s : ℂ => ((n+1 : ℕ) : ℂ)^s) =
                     fun s : ℂ => Complex.exp (s * Complex.log ((n+1 : ℕ) : ℂ)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero h_ne]
      ring_nf
    rw [h_rewrite]
    exact Complex.continuous_exp.comp (continuous_id.mul continuous_const)
  -- Division by continuous nonzero function
  apply Continuous.div continuous_const h_cpow
  intro s
  -- (n+1)^s ≠ 0 since base ≠ 0
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl h_ne)

/-! ## Polylog continuity (open content)

The full polylog continuity in `s` for `z = z_book` (on the unit
circle, `z ≠ 1`) requires analytic continuation.

**The path via the Hankel-route chain**:

The Hankel representation
```
polyLog s z = (Γ(1-s) / (2πi)) · ∮_H (-t)^(s-1) / (e^t/z - 1) dt
```
provides analytic continuation of polylog beyond the disc of
convergence `|z| < 1`. The right-hand side is continuous (analytic)
in `s` for `s ∉ {1, 2, 3, ...}` (the poles of `Γ(1-s)`).

With the 17-module Hankel-route formalization in place, the technical
work to transfer continuity is:

1. **Equality of definitions**: prove the formal `tsum`-series polyLog
   equals the Hankel-integral polyLog on the appropriate domain.
   - For `|z| < 1`: tsum converges absolutely; Hankel integral also
     equals the analytic function there.
   - For `|z| = 1, z ≠ 1` and `0 < Re s < 1`: tsum converges
     conditionally (Dirichlet); Hankel integral gives the analytic
     continuation.

2. **Continuity transfer**: once equality holds, polyLog continuity in
   `s` follows from continuity of the Hankel-integral representation
   (proven via DCT in the polylog-route chain, modulo the analytic
   continuation of the integrand in `s`).

The Hankel-route chain establishes the EDGE INTEGRALS' convergence to
Γ(s) and `e^(2πi(s-1))·Γ(s)`. To get full polylog continuity at z_book,
one would additionally need to bridge these edge limits to the polylog
series via Jonquières' formula (also mechanized at the statement level
in `PF.Analytic.Jonquieres`).

This is the **substantive analytic deliverable** remaining for the
unconditional `bookEvaluation` continuity. With it, the IVT framework
in `SStarBridge.lean` becomes fully unconditional given the numerical
sign-change input.

The termwise continuity proven above is the structural foundation;
the series-level continuity requires either:
* Weierstrass M-test for `|z| < 1`, or
* Analytic continuation transfer (the Hankel route, for `|z| = 1`).
-/

/-- **Termwise continuity (negation-of-exponent form)**: equivalent
    statement using `(n+1)^(-s)` instead of `1/(n+1)^s`. Useful for
    matching mathlib conventions. -/
theorem continuous_polyLog_term_neg (z : ℂ) (n : ℕ) :
    Continuous (fun s : ℂ => z^(n+1) * ((n+1 : ℕ) : ℂ)^(-s)) := by
  have h_ne : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h_cpow : Continuous (fun s : ℂ => ((n+1 : ℕ) : ℂ)^(-s)) := by
    have h_rewrite : (fun s : ℂ => ((n+1 : ℕ) : ℂ)^(-s)) =
                     fun s : ℂ => Complex.exp ((-s) * Complex.log ((n+1 : ℕ) : ℂ)) := by
      funext s
      rw [Complex.cpow_def_of_ne_zero h_ne]
      ring_nf
    rw [h_rewrite]
    exact Complex.continuous_exp.comp (continuous_neg.mul continuous_const)
  exact continuous_const.mul h_cpow

/-! ## Open: full polylog continuity at z_book

The continuity theorem we'd want for the unconditional `bookEvaluation`:

```
theorem continuousAt_polyLog_z_book {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    ContinuousAt (fun s : ℂ => polyLog s z_book) s
```

The proof goes via analytic continuation from the Hankel route. The
17-module chain provides all the analytic infrastructure; the
remaining work is the formal equality

  `polyLog s z_book = (Γ(1-s) / (2πi)) · (∫ upper − ∫ lower limit)`

which together with the proven Hankel-route limit theorem and
continuity of `Γ(1-s)` (for `s.re < 1` ⟹ `(1-s).re > 0`) gives the
polylog continuity at z_book.
-/

end PrincipiaTractalis.Analytic
