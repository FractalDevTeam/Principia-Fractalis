/-
# r214: the exact 3-Euler factor for the fractal resonance function.

★ 2026-08-07 r214 — the framework's FIRST **repair**.  Every prior stone in this
arc (r123, r212, the ch03/ch23/ch24 ledger entries) removed a claim.  This one
puts a correct theorem where a wrong one stood. ★

## The identity

For `Re s > 1`, with `D₃(n)` the base-3 digit sum and

    R_f(α, s) = Σ_{n ≥ 1} e^{iπ α D₃(n)} · n^{−s}          (ch03_resonance.tex:93)

the following holds for **every** real `α`:

    (1 − 3^{−s}) · R_f(α, s) = Σ_{n ≥ 1, 3 ∤ n} e^{iπ α D₃(n)} · n^{−s}.

That is `euler_factor_three_nat` (§4).  Numerically checked to 2e-16 at
s = 2.5 and s = 4.0 across α ∈ {0.7, 1.5, 2.0, φ} before formalization.

## What it REPAIRS — `ch09_spectral_unity.tex:221-227`

`ch09` Step 2 writes, citing the scaling law `D₃(3^k n) = D₃(n)`:

    G(α,s) = Π_{k≥0} (1 + e^{iπα}/3^{ks} + e^{2iπα}/3^{ks}) · G_prim(α,s).

**The scaling law is right.  The consequence drawn from it is wrong.**

The claimed correction factor depends on `α`.  The true one does not.  Both
halves of that sentence are in the kernel below:

* `euler_ratio_independent_of_alpha` (§5) — one and the same factor,
  `1 − 3^{−s}`, relates `R_f(α,·)` to its 3-free part for every `α`
  simultaneously.
* `euler_factor_unique` / `ch09_correction_factor_is_alpha_free` (§5) — *any*
  family `E : ℝ → ℂ` of correction factors is forced to be constant in `α`
  (given the series is non-zero).  An α-dependent factor is impossible.
* `ch09Factor_not_alpha_free` (§5) — the `k = 0` term of ch09's own product,
  `1 + e^{iπα} + e^{2iπα}`, already takes the value `3` at `α = 0` and `1` at
  `α = 1`.  It is α-dependent on the nose.

The repair is *additive*: nothing in ch09's scaling law is discarded.  What
changes is the shape of what the law buys you — a single geometric factor at
the prime 3, not a product of α-twisted blocks.

## Exactly ONE Euler factor, and no product over other primes

`D₃` is additive on base-3 **digit blocks**, never on prime factorisations.
Two decisive counterexamples, both in the kernel:

    D₃(6)  = 2   but  D₃(2) + D₃(3) = 2 + 1 = 3     (`digitSum3_not_additive_six`)
    D₃(10) = 2   but  D₃(2) + D₃(5) = 2 + 3 = 5     (`digitSum3_not_additive_ten`)

Hence the phase `e^{iπα D₃(n)}` is not a completely multiplicative arithmetic
function and `R_f` has no Euler product over the primes.  The failure is shown
directly on the terms at α = 1 in `rfTerm_not_multiplicative` (§7):
`rfTerm 1 s 6 = −(rfTerm 1 s 2 · rfTerm 1 s 3)`.

The prime 3 is special *not* because 3 is prime, but because 3 is the base.

## What this does NOT say

Nothing about the Riemann Hypothesis, nothing about BSD, nothing about any
Millennium problem.  This is a theorem about a Dirichlet series in its region
of absolute convergence.  `ch09`'s Theorem `thm:spectral_zeta` (the claimed
bijection of `R_f` zeros with ζ zeros, via a "consciousness correction factor")
is untouched by this file — it is *not* repaired here, and the broken Step 2
was one of its load-bearing steps.

## Cross-references

* `codex/AUDIT_RESPONSE_2026-08-06.md` — the audit that opened this arc.
* `PF/SigmaAbscissa_r212.lean` — the abscissa `σ(α) = log₃|1 + 2cos πα|`, built
  from the same ternary digit-block structure.  §8 below extends r212's φ guard
  rail to the block factor `χ(α) = 1 + 2 cos(πα)`.

## Formalization notes

* The sum is indexed by all of `ℕ`, not `ℕ≥1`.  This is not a cheat: for
  `Re s > 1` the `n = 0` term is `e^{iπα·0} · 0^{−s} = 0` in mathlib's `cpow`
  convention, so the two agree.  `euler_factor_three` (§4) restates the result
  over the honest subtype `{n // n ≠ 0}` for readers who want it.
* The 3-free index set is `{m : ℕ // ¬ (3 ∣ m)}`, which excludes `0`
  automatically since `3 ∣ 0`.
* The ζ anchor (§6) identifies the α = 0 specialisation with mathlib's
  `riemannZeta` outright — `euler_factor_three_zeta`.  Non-vacuity is therefore
  witnessed against a classical object, not against a definition of our own.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.GoldenRatio

open scoped Real

namespace PrincipiaTractalis.EulerFactorThree

/-! ## §1 — the base-3 digit sum and its scaling law

`D₃(n)`, and the one fact ch09 got right: multiplying by a power of the base
prepends zero digits, so the digit sum is unchanged. -/

/-- `D₃(n)`: the sum of the base-3 digits of `n`.  `ch03_resonance.tex:49`. -/
def digitSum3 (n : ℕ) : ℕ := (Nat.digits 3 n).sum

@[simp] theorem digitSum3_zero : digitSum3 0 = 0 := by simp [digitSum3]

/-- `Nat.digits 3 (3 * m) = 0 :: Nat.digits 3 m`.  The hypothesis `m ≠ 0` is
essential: `Nat.digits 3 0 = []`, so the statement fails at `m = 0`. -/
theorem digits_three_mul (m : ℕ) (hm : m ≠ 0) :
    Nat.digits 3 (3 * m) = 0 :: Nat.digits 3 m := by
  have hpos : 0 < 3 * m := Nat.mul_pos (by norm_num) (Nat.pos_of_ne_zero hm)
  rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 3) hpos]
  congr 1
  · exact Nat.mul_mod_right 3 m
  · congr 1
    exact Nat.mul_div_cancel_left m (by norm_num)

/-- **The scaling law, one step.**  `D₃(3m) = D₃(m)` for `m ≠ 0`. -/
theorem digitSum3_three_mul (m : ℕ) (hm : m ≠ 0) : digitSum3 (3 * m) = digitSum3 m := by
  unfold digitSum3
  rw [digits_three_mul m hm, List.sum_cons, Nat.zero_add]

/-- **The scaling law.**  `D₃(3^j · m) = D₃(m)` for `m ≠ 0`.  This is exactly the
identity ch09 Step 2 invokes; §4 draws the correct consequence from it. -/
theorem digitSum3_pow_mul (j m : ℕ) (hm : m ≠ 0) : digitSum3 (3 ^ j * m) = digitSum3 m := by
  induction j with
  | zero => simp
  | succ k ih =>
      have hk : (3 : ℕ) ^ k * m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hm
      calc digitSum3 (3 ^ (k + 1) * m)
          = digitSum3 (3 * (3 ^ k * m)) := by ring_nf
        _ = digitSum3 (3 ^ k * m) := digitSum3_three_mul _ hk
        _ = digitSum3 m := ih

/-! ### `D₃` is not additive on prime factorisations

The two counterexamples that block any Euler product over primes other than 3. -/

@[simp] theorem digitSum3_two : digitSum3 2 = 2 := by simp [digitSum3]
@[simp] theorem digitSum3_three : digitSum3 3 = 1 := by simp [digitSum3]
@[simp] theorem digitSum3_five : digitSum3 5 = 3 := by simp [digitSum3]
@[simp] theorem digitSum3_six : digitSum3 6 = 2 := by simp [digitSum3]
@[simp] theorem digitSum3_ten : digitSum3 10 = 2 := by simp [digitSum3]

/-- `D₃(6) = 2` but `D₃(2) + D₃(3) = 3`. -/
theorem digitSum3_not_additive_six : digitSum3 6 ≠ digitSum3 2 + digitSum3 3 := by
  simp

/-- `D₃(10) = 2` but `D₃(2) + D₃(5) = 5`. -/
theorem digitSum3_not_additive_ten : digitSum3 10 ≠ digitSum3 2 + digitSum3 5 := by
  simp

/-! ## §2 — the 3-adic factorisation

Every `n ≥ 1` is uniquely `3^j · m` with `3 ∤ m`.  Stated as an `Equiv` so that
§4 can reindex the sum by it. -/

theorem ne_zero_of_not_three_dvd {m : ℕ} (h : ¬ (3 ∣ m)) : m ≠ 0 := by
  rintro rfl
  exact h (dvd_zero 3)

/-- **The 3-adic factorisation.**  `n ↦ (v₃(n), n / 3^{v₃(n)})` is a bijection
from the nonzero naturals onto pairs `(j, m)` with `3 ∤ m`; the inverse is
`(j, m) ↦ 3^j · m`. -/
def threeAdicEquiv : ℕ × {m : ℕ // ¬ (3 ∣ m)} ≃ {n : ℕ // n ≠ 0} where
  toFun p := ⟨3 ^ p.1 * (p.2 : ℕ),
    Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_zero_of_not_three_dvd p.2.2)⟩
  invFun n := ((n : ℕ).factorization 3,
    ⟨(n : ℕ) / 3 ^ (n : ℕ).factorization 3, Nat.not_dvd_ordCompl Nat.prime_three n.2⟩)
  left_inv := by
    rintro ⟨j, m, hm⟩
    have hm0 : m ≠ 0 := ne_zero_of_not_three_dvd hm
    have hfac : (3 ^ j * m).factorization 3 = j := by
      rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0]
      simp [Nat.Prime.factorization_pow Nat.prime_three,
        Nat.factorization_eq_zero_of_not_dvd hm]
    have hdiv : 3 ^ j * m / 3 ^ j = m :=
      Nat.mul_div_cancel_left m (pow_pos (by norm_num) j)
    simp only [hfac, hdiv]
  right_inv := by
    rintro ⟨n, hn⟩
    exact Subtype.ext (Nat.ordProj_mul_ordCompl_eq_self n 3)

@[simp] theorem threeAdicEquiv_apply (p : ℕ × {m : ℕ // ¬ (3 ∣ m)}) :
    (threeAdicEquiv p : ℕ) = 3 ^ p.1 * (p.2 : ℕ) := rfl

/-- The factorisation map is injective. -/
theorem threeAdic_injective :
    Function.Injective (fun p : ℕ × {m : ℕ // ¬ (3 ∣ m)} => 3 ^ p.1 * (p.2 : ℕ)) := by
  intro p q h
  exact threeAdicEquiv.injective (Subtype.ext h)

/-- Every nonzero natural is `3^j · m` with `3 ∤ m`. -/
theorem threeAdic_surjective_on_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∃ p : ℕ × {m : ℕ // ¬ (3 ∣ m)}, 3 ^ p.1 * (p.2 : ℕ) = n :=
  ⟨threeAdicEquiv.symm ⟨n, hn⟩, congrArg Subtype.val (threeAdicEquiv.apply_symm_apply ⟨n, hn⟩)⟩

/-! ## §3 — the term, its norm, and summability -/

/-- The `n`-th term of `R_f(α, s)`: phase `e^{iπ α D₃(n)}` times `n^{−s}`. -/
noncomputable def rfTerm (α : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp ((Real.pi * α * (digitSum3 n : ℝ) : ℝ) * Complex.I) * (n : ℂ) ^ (-s)

/-! ### `cpow` multiplicativity on natural-number bases

`Complex.cpow` is not unconditionally multiplicative.  It is on nonnegative real
bases, which is all we need. -/

theorem natCast_mul_cpow (a b : ℕ) (z : ℂ) :
    ((a * b : ℕ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ z := by
  have h : ((a * b : ℕ) : ℂ) = ((a : ℝ) : ℂ) * ((b : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  push_cast
  ring

theorem natCast_pow_cpow (a : ℕ) (z : ℂ) (j : ℕ) :
    ((a ^ j : ℕ) : ℂ) ^ z = ((a : ℂ) ^ z) ^ j := by
  induction j with
  | zero => simp
  | succ k ih => rw [pow_succ, natCast_mul_cpow, ih, pow_succ]

/-- The phase has modulus one, so the term has the p-series modulus. -/
theorem norm_rfTerm (α : ℝ) (s : ℂ) (hs : s.re ≠ 0) (n : ℕ) :
    ‖rfTerm α s n‖ = (n : ℝ) ^ (-s.re) := by
  unfold rfTerm
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hs)]
  simp

theorem rfTerm_ne_zero (α : ℝ) (s : ℂ) (hs : s.re ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    rfTerm α s n ≠ 0 := by
  intro h0
  have hnorm := norm_rfTerm α s hs n
  rw [h0, norm_zero] at hnorm
  have hpos : (0 : ℝ) < (n : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
  linarith

/-- The `n = 0` term vanishes, because `0^{−s} = 0` for `s ≠ 0`. -/
theorem rfTerm_zero (α : ℝ) (s : ℂ) (hs : s ≠ 0) : rfTerm α s 0 = 0 := by
  unfold rfTerm
  rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs), mul_zero]

/-- **Absolute convergence for `Re s > 1`.** -/
theorem summable_rfTerm (α : ℝ) (s : ℂ) (hs : 1 < s.re) : Summable (rfTerm α s) := by
  have hre : s.re ≠ 0 := by intro h; rw [h] at hs; linarith
  apply Summable.of_norm
  simp_rw [norm_rfTerm α s hre]
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- The scaling law transported to the term: multiplying the index by `3^j`
multiplies the term by `(3^{−s})^j`, with the phase **unchanged**. -/
theorem rfTerm_three_pow_mul (α : ℝ) (s : ℂ) (j m : ℕ) (hm : m ≠ 0) :
    rfTerm α s (3 ^ j * m) = ((3 : ℂ) ^ (-s)) ^ j * rfTerm α s m := by
  unfold rfTerm
  rw [digitSum3_pow_mul j m hm, natCast_mul_cpow, natCast_pow_cpow]
  push_cast
  ring

/-! ## §4 — the main theorem -/

/-- `‖3^{−s}‖ < 1` whenever `0 < Re s`. -/
theorem norm_three_cpow_neg_lt_one (s : ℂ) (hs : 0 < s.re) : ‖(3 : ℂ) ^ (-s)‖ < 1 := by
  have h3 : ((3 : ℕ) : ℂ) = (3 : ℂ) := by norm_num
  have hre : (-s).re ≠ 0 := by simp; linarith
  rw [← h3, Complex.norm_natCast_cpow_of_re_ne_zero 3 hre]
  have h3r : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [h3r, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- **THE EXACT 3-EULER FACTOR.**

    (1 − 3^{−s}) · Σ_{n} e^{iπα D₃(n)} n^{−s} = Σ_{3 ∤ m} e^{iπα D₃(m)} m^{−s}

for every real `α` and every `s` with `Re s > 1`.  The left sum ranges over all
of `ℕ`; its `n = 0` term is `0`.  See `euler_factor_three` for the same
statement over `{n // n ≠ 0}`.

This is the correct consequence of ch09's scaling law `D₃(3^k n) = D₃(n)`.
One geometric factor, at the base prime 3, with **no dependence on `α`**. -/
theorem euler_factor_three_nat (α : ℝ) (s : ℂ) (hs : 1 < s.re) :
    (1 - (3 : ℂ) ^ (-s)) * ∑' n : ℕ, rfTerm α s n
      = ∑' m : {m : ℕ // ¬ (3 ∣ m)}, rfTerm α s (m : ℕ) := by
  have hre : s.re ≠ 0 := by intro h; rw [h] at hs; linarith
  have hs0 : s ≠ 0 := fun h => hre (by rw [h]; simp)
  have hcnorm : ‖(3 : ℂ) ^ (-s)‖ < 1 := norm_three_cpow_neg_lt_one s (by linarith)
  have hone : (1 : ℂ) - (3 : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : (3 : ℂ) ^ (-s) = 1 := by linear_combination -h
    rw [this, norm_one] at hcnorm
    exact lt_irrefl 1 hcnorm
  have hsum : Summable (rfTerm α s) := summable_rfTerm α s hs
  have hsub : Summable (fun m : {m : ℕ // ¬ (3 ∣ m)} => rfTerm α s (m : ℕ)) :=
    hsum.subtype {m : ℕ | ¬ (3 ∣ m)}
  -- the reindexing map
  have hginj := threeAdic_injective
  have hgout : ∀ x : ℕ, x ∉ Set.range (fun p : ℕ × {m : ℕ // ¬ (3 ∣ m)} => 3 ^ p.1 * (p.2 : ℕ)) →
      rfTerm α s x = 0 := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact rfTerm_zero α s hs0
    · exact absurd (threeAdic_surjective_on_ne_zero hx0) (by simpa [Set.range] using hx)
  have hgsupp : Function.support (rfTerm α s) ⊆
      Set.range (fun p : ℕ × {m : ℕ // ¬ (3 ∣ m)} => 3 ^ p.1 * (p.2 : ℕ)) := by
    intro x hx
    by_contra hxr
    exact hx (hgout x hxr)
  -- the term identity along the reindexing
  have e1 : ∀ p : ℕ × {m : ℕ // ¬ (3 ∣ m)},
      rfTerm α s (3 ^ p.1 * (p.2 : ℕ)) = ((3 : ℂ) ^ (-s)) ^ p.1 * rfTerm α s (p.2 : ℕ) :=
    fun p => rfTerm_three_pow_mul α s p.1 (p.2 : ℕ) (ne_zero_of_not_three_dvd p.2.2)
  have hcomp : Summable
      (fun p : ℕ × {m : ℕ // ¬ (3 ∣ m)} => rfTerm α s (3 ^ p.1 * (p.2 : ℕ))) := by
    have := (hginj.summable_iff hgout).mpr hsum
    simpa [Function.comp] using this
  have hsumg : Summable (fun p : ℕ × {m : ℕ // ¬ (3 ∣ m)} =>
      ((3 : ℂ) ^ (-s)) ^ p.1 * rfTerm α s (p.2 : ℕ)) := by
    simpa only [e1] using hcomp
  -- the computation
  have hT : ∑' n : ℕ, rfTerm α s n
      = (1 - (3 : ℂ) ^ (-s))⁻¹ * ∑' m : {m : ℕ // ¬ (3 ∣ m)}, rfTerm α s (m : ℕ) := by
    rw [← hginj.tsum_eq hgsupp]
    simp only [e1]
    rw [hsumg.tsum_prod' (fun j : ℕ => hsub.mul_left (((3 : ℂ) ^ (-s)) ^ j))]
    simp only [tsum_mul_left]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hcnorm]
  rw [hT, ← mul_assoc, mul_inv_cancel₀ hone, one_mul]

/-- The same identity indexed by the honest subtypes: `{n // n ≠ 0}` on the left,
`{m // m ≠ 0 ∧ 3 ∤ m}` on the right. -/
theorem euler_factor_three (α : ℝ) (s : ℂ) (hs : 1 < s.re) :
    (1 - (3 : ℂ) ^ (-s)) * ∑' n : {n : ℕ // n ≠ 0}, rfTerm α s (n : ℕ)
      = ∑' m : {m : ℕ // m ≠ 0 ∧ ¬ (3 ∣ m)}, rfTerm α s (m : ℕ) := by
  have hre : s.re ≠ 0 := by intro h; rw [h] at hs; linarith
  have hs0 : s ≠ 0 := fun h => hre (by rw [h]; simp)
  -- left: drop the vanishing `n = 0` term
  have hL : ∑' n : {n : ℕ // n ≠ 0}, rfTerm α s (n : ℕ) = ∑' n : ℕ, rfTerm α s n := by
    refine Subtype.val_injective.tsum_eq ?_
    intro x hx
    by_contra hxr
    have hx0 : x = 0 := by
      by_contra h
      exact hxr ⟨⟨x, h⟩, rfl⟩
    exact hx (by rw [hx0]; exact rfTerm_zero α s hs0)
  -- right: the two index subtypes coincide
  have hR : ∑' m : {m : ℕ // m ≠ 0 ∧ ¬ (3 ∣ m)}, rfTerm α s (m : ℕ)
      = ∑' m : {m : ℕ // ¬ (3 ∣ m)}, rfTerm α s (m : ℕ) := by
    exact (Equiv.subtypeEquivRight
        (fun _ => ⟨And.right, fun h => ⟨ne_zero_of_not_three_dvd h, h⟩⟩)).tsum_eq
      (fun m : {m : ℕ // ¬ (3 ∣ m)} => rfTerm α s (m : ℕ))
  rw [hL, hR, euler_factor_three_nat α s hs]

/-! ## §5 — the corollary that refutes `ch09_spectral_unity.tex:221-227`

`ch09` asserts an `α`-dependent correction factor.  The true factor is
`1 − 3^{−s}` for every `α`, and no other factor is possible. -/

/-- `R_f(α, s)` as a single symbol. -/
noncomputable def rfFull (α : ℝ) (s : ℂ) : ℂ := ∑' n : ℕ, rfTerm α s n

/-- The 3-free part of `R_f(α, s)` — ch09's `G_prim`. -/
noncomputable def rfPrim (α : ℝ) (s : ℂ) : ℂ :=
  ∑' m : {m : ℕ // ¬ (3 ∣ m)}, rfTerm α s (m : ℕ)

theorem rfPrim_eq (α : ℝ) (s : ℂ) (hs : 1 < s.re) :
    rfPrim α s = (1 - (3 : ℂ) ^ (-s)) * rfFull α s :=
  (euler_factor_three_nat α s hs).symm

/-- **ONE factor, for ALL `α`.**  There is a single complex number `E`, namely
`1 − 3^{−s}`, depending on `s` alone, such that `G_prim(α,s) = E · G(α,s)`
simultaneously for every real `α`.  `ch09:221-227` claims a factor that varies
with `α`; this says it cannot. -/
theorem euler_ratio_independent_of_alpha (s : ℂ) (hs : 1 < s.re) :
    ∃ E : ℂ, E = 1 - (3 : ℂ) ^ (-s) ∧ ∀ α : ℝ, rfPrim α s = E * rfFull α s :=
  ⟨1 - (3 : ℂ) ^ (-s), rfl, fun α => rfPrim_eq α s hs⟩

/-- Any correction factor is *the* correction factor.  No α-dependent
alternative exists where the series is non-zero. -/
theorem euler_factor_unique (α : ℝ) (s : ℂ) (hs : 1 < s.re) (E : ℂ)
    (hne : rfFull α s ≠ 0) (h : rfPrim α s = E * rfFull α s) :
    E = 1 - (3 : ℂ) ^ (-s) := by
  have hmain : E * rfFull α s = (1 - (3 : ℂ) ^ (-s)) * rfFull α s := by
    rw [← h, rfPrim_eq α s hs]
  exact mul_right_cancel₀ hne hmain

/-- **The refutation in one line.**  Any family `E : ℝ → ℂ` of correction
factors relating `G_prim(·, s)` to `G(·, s)` is constant in `α`.  ch09's
product, whose factors contain `e^{iπα}` and `e^{2iπα}`, is not. -/
theorem ch09_correction_factor_is_alpha_free (α β : ℝ) (s : ℂ) (hs : 1 < s.re)
    (E : ℝ → ℂ) (hne : ∀ γ : ℝ, rfFull γ s ≠ 0)
    (hE : ∀ γ : ℝ, rfPrim γ s = E γ * rfFull γ s) : E α = E β := by
  rw [euler_factor_unique α s hs (E α) (hne α) (hE α),
    euler_factor_unique β s hs (E β) (hne β) (hE β)]

/-- The `k`-th factor of the product asserted at `ch09_spectral_unity.tex:223`. -/
noncomputable def ch09Factor (α : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  1 + Complex.exp (((Real.pi * α : ℝ) : ℂ) * Complex.I) / (3 : ℂ) ^ ((k : ℂ) * s)
    + Complex.exp (((2 * Real.pi * α : ℝ) : ℂ) * Complex.I) / (3 : ℂ) ^ ((k : ℂ) * s)

theorem ch09Factor_zero_alpha_zero (s : ℂ) : ch09Factor 0 s 0 = 3 := by
  unfold ch09Factor
  norm_num

theorem ch09Factor_zero_alpha_one (s : ℂ) : ch09Factor 1 s 0 = 1 := by
  unfold ch09Factor
  have h1 : ((Real.pi * 1 : ℝ) : ℂ) = (Real.pi : ℂ) := by push_cast; ring
  have h2 : ((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
  norm_num

/-- **ch09's own factor is α-dependent.**  Its `k = 0` term is `3` at `α = 0`
and `1` at `α = 1`.  Combined with `ch09_correction_factor_is_alpha_free`, this
is the contradiction: the true factor cannot vary with `α`, and ch09's does. -/
theorem ch09Factor_not_alpha_free (s : ℂ) : ch09Factor 0 s 0 ≠ ch09Factor 1 s 0 := by
  rw [ch09Factor_zero_alpha_zero, ch09Factor_zero_alpha_one]
  norm_num

/-! ## §6 — the ζ anchor (non-vacuity)

At `α = 0` the phase is `1` and the theorem must collapse to the classical
`(1 − 3^{−s}) ζ(s) = Σ_{3 ∤ n} n^{−s}`.  It does, against mathlib's
`riemannZeta`. -/

@[simp] theorem rfTerm_alpha_zero (s : ℂ) (n : ℕ) : rfTerm 0 s n = (n : ℂ) ^ (-s) := by
  unfold rfTerm
  norm_num

theorem rfFull_alpha_zero_eq_zeta (s : ℂ) (hs : 1 < s.re) :
    rfFull 0 s = riemannZeta s := by
  unfold rfFull
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  exact tsum_congr fun n => by rw [rfTerm_alpha_zero, Complex.cpow_neg, one_div]

/-- **The ζ anchor.**  `(1 − 3^{−s}) · ζ(s) = Σ_{3 ∤ m} m^{−s}` for `Re s > 1`,
obtained as the `α = 0` case of `euler_factor_three_nat`.  The theorem is
therefore not vacuous: it reproduces a classical identity about `riemannZeta`. -/
theorem euler_factor_three_zeta (s : ℂ) (hs : 1 < s.re) :
    (1 - (3 : ℂ) ^ (-s)) * riemannZeta s
      = ∑' m : {m : ℕ // ¬ (3 ∣ m)}, ((m : ℕ) : ℂ) ^ (-s) := by
  have h := euler_factor_three_nat 0 s hs
  rw [show (∑' n : ℕ, rfTerm 0 s n) = riemannZeta s from rfFull_alpha_zero_eq_zeta s hs] at h
  rw [h]
  exact tsum_congr fun m => rfTerm_alpha_zero s (m : ℕ)

/-! ## §7 — no Euler product over the other primes

`D₃` is additive on digit blocks, not on prime factorisations.  §1 records the
arithmetic counterexamples; here is the failure on the terms themselves. -/

/-- At `α = 1` the term at `6` is the **negative** of the product of the terms
at `2` and `3`, because `D₃(6) = 2` while `D₃(2) + D₃(3) = 3`. -/
theorem rfTerm_six_eq_neg_mul (s : ℂ) :
    rfTerm 1 s 6 = -(rfTerm 1 s 2 * rfTerm 1 s 3) := by
  have h6 : ((6 : ℕ) : ℂ) ^ (-s) = ((2 : ℕ) : ℂ) ^ (-s) * ((3 : ℕ) : ℂ) ^ (-s) := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, natCast_mul_cpow]
  unfold rfTerm
  rw [digitSum3_six, digitSum3_two, digitSum3_three]
  have e2 : ((Real.pi * 1 * ((2 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I
      = 2 * (Real.pi : ℂ) * Complex.I := by push_cast; ring
  have e3 : ((Real.pi * 1 * ((1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I
      = (Real.pi : ℂ) * Complex.I := by push_cast; ring
  rw [e2, e3, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
  push_cast at h6 ⊢
  rw [h6]
  ring

/-- **No Euler product over primes.**  The phase `e^{iπ D₃(n)}` is not
completely multiplicative, so `R_f` admits no factorisation over the primes.
The single factor at `3` in §4 comes from `3` being the **base**, not from `3`
being prime. -/
theorem rfTerm_not_multiplicative (s : ℂ) (hs : s.re ≠ 0) :
    rfTerm 1 s 6 ≠ rfTerm 1 s 2 * rfTerm 1 s 3 := by
  intro h
  have hneg := rfTerm_six_eq_neg_mul s
  rw [h] at hneg
  have hz : rfTerm 1 s 2 * rfTerm 1 s 3 = 0 := by linear_combination hneg / 2
  rcases mul_eq_zero.mp hz with h2 | h3
  · exact rfTerm_ne_zero 1 s hs (by norm_num) h2
  · exact rfTerm_ne_zero 1 s hs (by norm_num) h3

/-! ## §8 — the φ guard rail (P2)

The ternary block factor of r212 is `χ(α) = 1 + 2 cos(πα)`
(`PF/SigmaAbscissa_r212.lean`, `norm_one_add_exp_add_exp_sq_pi_mul`).  It hits
the golden ratio exactly:

    χ(2/5) = 1 + 2 cos(2π/5) = φ,        χ(1/5) = 1 + 2 cos(π/5) = φ².

**READ THIS BEFORE QUOTING IT.**  φ appears here as a **VALUE of χ at the
RATIONAL argument α = 2/5**.  It does **not** appear as an α.  This is not a
derivation of `α_Hodge = φ`, and it will look like one.  The framework's
`α_Hodge` is `φ ≈ 1.618`, which is irrational and is *not* `2/5`
(`chi_argument_ne_goldenRatio`).  r212 already proved that the ternary digit
mechanism provably misses every irrational α, φ included
(`irrational_imp_sigma_ne_zero_one`, `sigma_goldenRatio_ne_half`).  Nothing in
this section weakens that.  Same discipline, same conclusion. -/

/-- The ternary block factor `χ(α) = 1 + 2 cos(πα)` of r212. -/
noncomputable def chi (α : ℝ) : ℝ := 1 + 2 * Real.cos (Real.pi * α)

private theorem cos_two_pi_div_five_aux (r : ℝ) (hr : r ^ 2 = 5) :
    2 * ((1 + r) / 4) ^ 2 - 1 = (r - 1) / 4 := by
  linear_combination hr / 8

theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  exact cos_two_pi_div_five_aux _ (Real.sq_sqrt (by norm_num))

/-- `χ(2/5) = φ`, exactly.  The argument `2/5` is RATIONAL. -/
theorem chi_two_fifths : chi (2 / 5) = Real.goldenRatio := by
  have hgr : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have h : Real.pi * (2 / 5 : ℝ) = 2 * Real.pi / 5 := by ring
  unfold chi
  rw [h, cos_two_pi_div_five, hgr]
  ring

/-- `χ(1/5) = φ²`, exactly.  The argument `1/5` is RATIONAL. -/
theorem chi_one_fifth : chi (1 / 5) = Real.goldenRatio ^ 2 := by
  have hgr : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : Real.pi * (1 / 5 : ℝ) = Real.pi / 5 := by ring
  unfold chi
  rw [h, Real.cos_pi_div_five, hgr]
  linear_combination -h5 / 4

/-- **THE GUARD RAIL.**  The α at which χ takes the value φ is `2/5`, and
`2/5 ≠ φ`.  A value of χ is not an argument of χ. -/
theorem chi_argument_ne_goldenRatio : (2 / 5 : ℝ) ≠ Real.goldenRatio := by
  have hgr : Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl
  have h0 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [hgr]
  intro h
  nlinarith [h, h0]

/-- The guard rail, bundled: χ hits φ, at a rational argument that is not φ. -/
theorem chi_golden_is_a_value_not_an_argument :
    chi (2 / 5) = Real.goldenRatio ∧ (2 / 5 : ℝ) ≠ Real.goldenRatio :=
  ⟨chi_two_fifths, chi_argument_ne_goldenRatio⟩

end PrincipiaTractalis.EulerFactorThree

/-! ## §9 — kernel axiom audit

House rule: the audit lives IN the file, so `lake build` re-runs it.  Every
declaration below must report exactly `[propext, Classical.choice, Quot.sound]`. -/

-- §1  digit sum and scaling law
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_zero
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_two
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_three
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_five
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_six
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_ten
#print axioms PrincipiaTractalis.EulerFactorThree.digits_three_mul
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_three_mul
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_pow_mul
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_not_additive_six
#print axioms PrincipiaTractalis.EulerFactorThree.digitSum3_not_additive_ten
-- §2  3-adic factorisation
#print axioms PrincipiaTractalis.EulerFactorThree.ne_zero_of_not_three_dvd
#print axioms PrincipiaTractalis.EulerFactorThree.threeAdicEquiv
#print axioms PrincipiaTractalis.EulerFactorThree.threeAdicEquiv_apply
#print axioms PrincipiaTractalis.EulerFactorThree.threeAdic_injective
#print axioms PrincipiaTractalis.EulerFactorThree.threeAdic_surjective_on_ne_zero
-- §3  term, norm, summability
#print axioms PrincipiaTractalis.EulerFactorThree.natCast_mul_cpow
#print axioms PrincipiaTractalis.EulerFactorThree.natCast_pow_cpow
#print axioms PrincipiaTractalis.EulerFactorThree.norm_rfTerm
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_ne_zero
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_zero
#print axioms PrincipiaTractalis.EulerFactorThree.summable_rfTerm
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_three_pow_mul
-- §4  MAIN
#print axioms PrincipiaTractalis.EulerFactorThree.norm_three_cpow_neg_lt_one
#print axioms PrincipiaTractalis.EulerFactorThree.euler_factor_three_nat
#print axioms PrincipiaTractalis.EulerFactorThree.euler_factor_three
-- §5  the ch09 refutation
#print axioms PrincipiaTractalis.EulerFactorThree.rfPrim_eq
#print axioms PrincipiaTractalis.EulerFactorThree.euler_ratio_independent_of_alpha
#print axioms PrincipiaTractalis.EulerFactorThree.euler_factor_unique
#print axioms PrincipiaTractalis.EulerFactorThree.ch09_correction_factor_is_alpha_free
#print axioms PrincipiaTractalis.EulerFactorThree.ch09Factor_zero_alpha_zero
#print axioms PrincipiaTractalis.EulerFactorThree.ch09Factor_zero_alpha_one
#print axioms PrincipiaTractalis.EulerFactorThree.ch09Factor_not_alpha_free
-- §6  ζ anchor
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_alpha_zero
#print axioms PrincipiaTractalis.EulerFactorThree.rfFull_alpha_zero_eq_zeta
#print axioms PrincipiaTractalis.EulerFactorThree.euler_factor_three_zeta
-- §7  no Euler product over primes
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_six_eq_neg_mul
#print axioms PrincipiaTractalis.EulerFactorThree.rfTerm_not_multiplicative
-- §8  φ guard rail
#print axioms PrincipiaTractalis.EulerFactorThree.cos_two_pi_div_five
#print axioms PrincipiaTractalis.EulerFactorThree.chi_two_fifths
#print axioms PrincipiaTractalis.EulerFactorThree.chi_one_fifth
#print axioms PrincipiaTractalis.EulerFactorThree.chi_argument_ne_goldenRatio
#print axioms PrincipiaTractalis.EulerFactorThree.chi_golden_is_a_value_not_an_argument
