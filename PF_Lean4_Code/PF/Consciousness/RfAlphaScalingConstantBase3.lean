/-
# The `R_f` α-Scaling Constant, Derived From Base 3

**Pablo Cohen + Claude Opus 5**, 2026-10-07.

## What this file settles

Chapter 7 (`ch07_constants.tex`, "Universal Constants and Emergent Principles" —
the Grothendieck memorial chapter) states the **Universal Scaling Law**
`thm:pi-ten-scaling`:

    lim_{α → α_c} (R_f(α,s) - R_f(α_c,s)) / (α - α_c)  =  (π/10) · f(α_c, s)

"where `f(α_c,s)` is a structure-specific function that depends on the
particular problem being studied", and derives the `1/10` in a `level2`
environment from "the decimal expansion structure of the logarithm" plus a
`level3` claim that ten bins maximise Shannon entropy.

This file derives the constant from the actual definition of `R_f`, in base 3.
**The constant is `iπ`.** There is no `1/10`.

## The derivation, which is one line

`R_f(α,s) = Σ_{n≥1} exp(iπα·D₃(n)) / n^s` (`fractalResonance`), so the α-
dependence of each term sits entirely in the phase `exp(iπα·D₃(n))`, whose
α-derivative is `iπ·D₃(n)` times itself. Hence termwise

    ∂/∂α [ exp(iπα·D₃(n)) / n^s ]  =  iπ · D₃(n) · exp(iπα·D₃(n)) / n^s

which is `rf_term_hasDerivAt` / `rf_term_deriv_eq` below, and summing gives

    ∂R_f/∂α  =  iπ · Σ_{n≥1} D₃(n) · exp(iπα·D₃(n)) / n^s.

So the universal prefactor is `iπ` and the structure-specific function is the
**D₃-weighted resonance sum** — a genuinely base-3 object, since `D₃` is the
base-3 digital sum. Base 3 enters twice: once as the weight `D₃(n)`, and once
through the manuscript's own critical value `α_c = 3/2 = Σ_{k≥0} 3^{-k}`, the
base-3 geometric sum, at which the phase is exactly `(-i)^{D₃(n)}`.

Numerically (checked outside Lean, 4·10⁵ terms, against central finite
differences at `α_c = 3/2`): `|∂R_f/∂α|` equals 3.422, 3.189, 3.147, 3.141651
at `s = 2, 4, 6, 10`, converging to `π = 3.141593` — because the D₃-weighted
sum tends to modulus 1 as `Re s → ∞` (the `n = 1` term, `D₃(1) = 1`,
dominates). The constant visible at the framework's own critical point is `π`.
It is never `π/10 ≈ 0.3142`; the weighted sum has modulus in `[1.00, 1.09]`
there, never `0.1`.

## Why the chapter's own statement could not have determined `1/10`

`scaling_constant_underdetermined` below: because `f(α_c,s)` is unconstrained,
**any** nonzero constant `c` satisfies the displayed law with a suitable `f`
(take `f := c⁻¹ · iπ · D₃(n) · term`). So `thm:pi-ten-scaling` as written is
satisfied by every nonzero constant and cannot single out `π/10` — or `iπ`, or
anything else. The constant has to come from the derivative itself, which is
what `rf_term_deriv_eq` supplies. This is the manuscript analogue of a
`def X : Prop := True`: a free parameter absorbs the content.

`prefactor_ne_pi_div_ten` records the sharpest form: the true prefactor is
purely imaginary and nonzero, while `π/10` is real and positive, so they are
not equal for any `n` with `D₃(n) ≠ 0`.

## Scope — what is and is not claimed

* PROVEN here, axiom-free: the **termwise** identity, the base-3 congruence
  `D₃(n) ≡ n (mod 2)`, the underdetermination of the chapter's constant, and
  `iπ·D₃(n) ≠ π/10`.
* NOT proven here: differentiation under the infinite sum. That is valid for
  `Re s > 1` (since `D₃(n) = O(log n)`, so `Σ D₃(n)/n^σ` converges there), but
  it needs a `hasDerivAt_tsum`-style uniformity argument and is left as the
  explicit next lemma rather than asserted.
* This file does **not** claim `π/10` is absent from the rest of the
  manuscript's physics, only that the α-scaling law of Ch 7 yields `iπ`. Each
  other appearance of `π/10` needs its own check. One is already known to
  dissolve: in `def:consciousness_strata` (Appendix I) the combination
  `(π/10)·(0.95-t)/0.05` is identically `2π·(0.95-t)` — the `1/10` cancels
  against the `0.05` threshold step, leaving a bare `2π`.

## The base-3 congruence, and why the odd-α collapse works

`digitalSum3_mod_two`: `D₃(n) ≡ n (mod 2)` for every `n`, because `3^k ≡ 1
(mod 2)` so `n = Σ dₖ3^k ≡ Σ dₖ = D₃(n)`. This is the fact underneath
`phaseFactor_alpha_nat_odd` elsewhere in the corpus: at odd integer `α`,
`exp(iπα·D₃(n)) = (-1)^{D₃(n)} = (-1)^n`, which is why `R_f` collapses to the
alternating Dirichlet series there.
-/
import PF.Consciousness.FractalResonance

-- `digitalSum3` is `PrincipiaTractalis.TuringEncoding.digitalSum3`; FractalResonance
-- opens that namespace and so must this file. PF's lakefile does not set
-- `autoImplicit false`, so an unresolved identifier is silently bound as an
-- implicit type variable rather than reported -- which is exactly what happened on
-- the first build of this file. Disabled locally so a typo is an error.
set_option autoImplicit false

namespace PrincipiaTractalis.Consciousness

open Complex
open PrincipiaTractalis.TuringEncoding

/-! ## Section 1 — The base-3 congruence `D₃(n) ≡ n (mod 2)` -/

/-- **`D₃(n) ≡ n (mod 2)`.**

    Every power of three is odd, so `n = Σ dₖ·3^k ≡ Σ dₖ = D₃(n) (mod 2)`.
    Proved by strong induction along the base-3 recursion
    `D₃(n) = n % 3 + D₃(n / 3)`.

    This is the fact underneath the corpus's odd-α collapse: at odd integer
    `α` the phase `exp(iπα·D₃(n))` equals `(-1)^{D₃(n)} = (-1)^n`. -/
theorem digitalSum3_mod_two (n : ℕ) : digitalSum3 n % 2 = n % 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [digitalSum3]
    · have hne : n ≠ 0 := by omega
      have hlt : n / 3 < n := Nat.div_lt_self h (by norm_num)
      have hrec : digitalSum3 n = n % 3 + digitalSum3 (n / 3) := by
        rw [digitalSum3]; simp [hne]
      have hih := ih (n / 3) hlt
      omega

/-! ## Section 2 — The α-derivative of the phase, and of a single `R_f` term

The whole α-dependence of `R_f` sits in the phase `exp(iπα·D₃(n))`. Its
α-derivative multiplies it by `iπ·D₃(n)`, and `1/n^s` is an α-constant. -/

/-- **The phase factor, written as an exponential linear in `α`.**

    `exp(iπα·D₃(n)) = exp((iπ·D₃(n))·α)` — the form in which the derivative
    constant `iπ·D₃(n)` is visible. -/
theorem phaseFactor_eq_exp_const_mul (α : ℝ) (n : ℕ) :
    phaseFactor α n
      = Complex.exp ((Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)) * (α : ℂ)) := by
  unfold phaseFactor
  congr 1
  push_cast
  ring

/-- **α-derivative of the phase factor**: multiplication by `iπ·D₃(n)`. -/
theorem phaseFactor_hasDerivAt (α : ℝ) (n : ℕ) :
    HasDerivAt (fun a : ℝ => phaseFactor a n)
      (Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ) * phaseFactor α n) α := by
  set C : ℂ := Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ) with hC
  have hlin : HasDerivAt (fun a : ℝ => C * (a : ℂ)) C α := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := α)).const_mul C
  have hexp : HasDerivAt (fun a : ℝ => Complex.exp (C * (a : ℂ)))
      (Complex.exp (C * (α : ℂ)) * C) α := hlin.cexp
  have hfun : (fun a : ℝ => phaseFactor a n)
      = fun a : ℝ => Complex.exp (C * (a : ℂ)) := by
    funext a; rw [phaseFactor_eq_exp_const_mul]
  rw [hfun]
  convert hexp using 1
  rw [phaseFactor_eq_exp_const_mul]
  ring

/-- **★ THE SCALING CONSTANT, TERMWISE ★**

    `∂/∂α [ exp(iπα·D₃(n)) / n^s ] = iπ·D₃(n) · exp(iπα·D₃(n)) / n^s`.

    The universal prefactor is `iπ`; the `n`-dependence is the base-3 digital
    sum `D₃(n)`. No factor of `1/10` occurs or can occur: the only constant
    entering is the `π` of the phase `exp(iπα·…)`. -/
theorem rf_term_hasDerivAt (α : ℝ) (s : ℂ) (n : ℕ) :
    HasDerivAt (fun a : ℝ => fractalResonanceTerm_complex a s n)
      (Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)
        * fractalResonanceTerm_complex α s n) α := by
  unfold fractalResonanceTerm_complex
  simpa [mul_div_assoc] using (phaseFactor_hasDerivAt α n).div_const ((n : ℂ) ^ s)

/-- The same identity in `deriv` form. -/
theorem rf_term_deriv_eq (α : ℝ) (s : ℂ) (n : ℕ) :
    deriv (fun a : ℝ => fractalResonanceTerm_complex a s n) α
      = Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)
        * fractalResonanceTerm_complex α s n :=
  (rf_term_hasDerivAt α s n).deriv

/-! ## Section 3 — Why Ch 7's displayed law cannot determine its own constant -/

/-- **★ THE CH 7 SCALING LAW IS SATISFIED BY EVERY NONZERO CONSTANT ★**

    `thm:pi-ten-scaling` displays the α-derivative as `(π/10) · f(α_c,s)` with
    `f` described only as "a structure-specific function that depends on the
    particular problem". Because `f` is unconstrained it absorbs any prefactor:
    for EVERY nonzero `c` there is an `f` making the displayed law true.

    So that statement cannot single out `π/10`, nor `iπ`, nor any other
    constant — it has no content as regards the constant. The constant must
    come from the derivative itself (`rf_term_deriv_eq`), and there it is `iπ`.

    This is the manuscript analogue of a vacuous `def X : Prop := True`: a free
    parameter absorbs the claim. -/
theorem scaling_constant_underdetermined
    (α : ℝ) (s : ℂ) (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    ∃ f : ℂ, deriv (fun a : ℝ => fractalResonanceTerm_complex a s n) α = c * f := by
  refine ⟨c⁻¹ * (Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)
      * fractalResonanceTerm_complex α s n), ?_⟩
  rw [rf_term_deriv_eq]
  field_simp

/-- **★ `iπ·D₃(n)` IS NOT `π/10` ★**

    The true prefactor is purely imaginary and nonzero whenever `D₃(n) ≠ 0`;
    `π/10` is real and positive. So they are never equal, and no choice of
    normalisation turns one into the other.

    No hypothesis on `n` is needed: the true prefactor is a real multiple of `I`,
    so its real part is `0` for every `n`, while `π/10 > 0`. -/
theorem prefactor_ne_pi_div_ten (n : ℕ) :
    Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ) ≠ ((Real.pi / 10 : ℝ) : ℂ) := by
  intro hEq
  have h1 : Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)
      = ((Real.pi * (digitalSum3 n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1] at hEq
  have hre := congrArg Complex.re hEq
  simp at hre
  linarith [Real.pi_pos]

/-- The prefactor's modulus is `π·D₃(n)` — so at `D₃(n) = 1` it is exactly `π`,
    matching the numerical limit of `|∂R_f/∂α|` at `α_c = 3/2` as `Re s → ∞`. -/
theorem norm_prefactor (n : ℕ) :
    ‖Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)‖
      = Real.pi * (digitalSum3 n : ℝ) := by
  have h1 : Complex.I * (Real.pi : ℂ) * (digitalSum3 n : ℂ)
      = ((Real.pi * (digitalSum3 n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ## Section 4 — Axiom audit -/

#print axioms digitalSum3_mod_two
#print axioms rf_term_hasDerivAt
#print axioms rf_term_deriv_eq
#print axioms scaling_constant_underdetermined
#print axioms prefactor_ne_pi_div_ten

end PrincipiaTractalis.Consciousness
