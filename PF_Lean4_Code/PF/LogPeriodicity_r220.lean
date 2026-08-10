/-
# r220: log₃-periodicity — the exact renormalisation `S(3N) = χ · S(N)`,
# and the parameter-free log-frequency it forces.

★ 2026-08-10 r220 — the stone that turns the framework's self-similarity
prediction from a remark into a theorem, and pins its frequency with **no free
parameter**. ★

## §0 The one-line content

Let `D₃(n)` be the base-3 digit sum (`ch03_resonance.tex:49`), let `ω : ℂ`, and
let

    S(ω, N)  =  Σ_{n < N} ω^{D₃(n)} .

Write `χ(ω) = 1 + ω + ω²`.  Then, **exactly** and for every `ω`,

    S(ω, 3N)  =  χ(ω) · S(ω, N)          at every `N = 3^k`.

This is `S_three_mul` (§1).  It is not an asymptotic, not a leading order, and
carries no error term: the summatory function of the ternary digit character is
*exactly* self-similar under `N ↦ 3N`.

Two consequences, both in the kernel below:

* **Amplitude.**  `‖S(ω, 3^k)‖ = ‖χ(ω)‖^k = ‖χ(ω)‖^{log₃ N}` — a pure power law
  `N^σ` with `σ = log₃‖χ‖`, which is exactly r212's abscissa `σ(α)` at
  `ω = e^{iπα}` (`sigma_eq_logb_norm_chi`, `rpow_sigma_eq_norm_chi`, §2).
* **Phase.**  `arg S(ω, 3^k) = k · arg χ(ω)` in `ℝ / 2πℤ`
  (`arg_S_pow_three`, §3).  The phase advances by `arg χ` per factor of 3 in
  `N`, i.e. it is **periodic in `ln N` with period `ln 3`**.

Hence the modulation is log-periodic and its frequency is fixed by the base
alone:

    logPeriod     =  ln 3          =  1.0986122886681098
    logFrequency  =  2π / ln 3     =  5.719202...
    logFrequency · logPeriod = 2π                       (`logFrequency_mul_logPeriod`)

**There is no free parameter in that frequency.**  It is not fitted, not tuned,
and does not depend on `ω`, on `α`, or on any amplitude.  Only the base 3
enters.  That is rare, and it is the reason this stone exists.

The physics-facing form is `logModulation_three_mul` (§3):

    cos( (2π / ln 3) · ln x + φ₀ )   is invariant under   x ↦ 3x

for every phase offset `φ₀` and every `x > 0`.  One full period of the
modulation per factor of 3 in scale.

## §0.1 What supplies the Ω paper's missing content

*The Ocean of Timeless Existence*, line 166, predicts a CMB signature
`δT/T ~ sin(k · D₃(r)) · exp(−r/r_c)`.  As written that is not computable:
`D₃` of a **real** argument is undefined, and no period is stated.  The digit
block structure already in the corpus (r212 `digitBlock_sum`, r214
`digitSum3_pow_mul`, r218 `sum_wordWeight`) supplies both missing pieces at
once: the correct continuous variable is `log₃` of the scale, and the period is
`ln 3` exactly.

## §0.2 WHAT THIS DOES NOT ESTABLISH — computed, and recorded

**The CMB cannot test this.  Do not propose the CMB test.**

A log-period of `ln 3` puts successive peaks at `l, 3l, 9l, …`.  Across
Planck's usable range `l = 2 … 2500` that is

    log₃(2500/2)  =  ln(1250)/ln(3)  ≈  6.5 cycles

and the three cheapest of those cycles are cosmic-variance limited: the
fractional variance `sqrt(2/(2l+1))` is **63 % at l = 2, 39 % at l = 6, 23 % at
l = 18**.  A 6-cycle log-sinusoid is furthermore close to degenerate with the
scalar spectral index `n_s` and its running `dn_s/dln k`, which are exactly the
parameters that absorb slow log-scale tilt.  The test is not merely hard; the
signal is in the part of the log-axis where the data are worst and the
degeneracy is worst.

**Instruments that could see it** span more decades in LENGTH:

| probe                                     | range              | cycles of `ln 3` |
|-------------------------------------------|--------------------|------------------|
| galaxy clustering ξ(r)                    | 0.1 – 200 Mpc/h    | **6.9**          |
| Lyman-α + clustering + CMB combined       | 0.01 – 10⁴ Mpc     | **12.6**         |
| all cosmic structure                      | 1 kpc – 14 Gpc     | **15.0**         |

**A correction worth recording.**  A first pass put the halo mass function at
14.7 cycles.  That is wrong.  The halo mass function gives only **4.9** cycles,
because `M ∝ r³`, so the log-period in `ln M` is `3 ln 3`, not `ln 3`.
**Derived variables inherit a rescaled period**, and the rescaling divides the
cycle count.  Any observable must be reduced to a LENGTH before its cycle count
is read off this table.

## §0.3 SCOPE — plainly

This is a theorem about the summatory function of the base-3 digit character.

It asserts **nothing** about the CMB, nothing about cosmic structure, nothing
about physical reality.  No claim is made that any observable carries this
modulation.  Whether one does is exactly what an experiment would decide, and
**no experiment is performed here**.  Nothing below bears on the Riemann
Hypothesis, BSD, P vs NP, Yang–Mills, Navier–Stokes, or any Millennium problem.

The numbers in §0.2 are arithmetic on stated instrument ranges.  They are not
formalized in Lean and are not theorems; they are recorded so that the reach of
the theorem is not overstated by a later reader.

## §0.4 Which form §3's phase statement takes

`Complex.arg` is valued in `(−π, π]`, so the naive real subtraction
`arg(χ^{k+1}) − arg(χ^k) = arg χ` is FALSE as stated (it fails by `2π` whenever
the phase wraps).  Rather than weaken the claim, the phase statement is made in
`Real.Angle = ℝ / 2πℤ`, where it is exactly true and unconditional:

    (arg (χ^{k+1}) : Real.Angle) − (arg (χ^k) : Real.Angle) = (arg χ : Real.Angle)

That is `phase_advance_per_triadic_step`, proved from mathlib's
`Complex.arg_pow_coe_angle`.  **The mod-2π form is the honest one, and it is the
one used.**  The multiplicative fallback `chi_pow_succ` and the real-valued
`Real.logb` statements are also given, so nothing rests on the angle API.

## §1–§5 map

* §1 — `S`, `chi`, and the exact renormalisation `S(3N) = χ S(N)`.
* §2 — the normalised fluctuation is invariant, hence constant; link to r212's σ.
* §3 — the log-period, the log-frequency, the phase advance, the modulation.
* §4 — NON-VACUITY: `ω = i` and `ω = −1`, with explicit numeric instances.
* §5 — P2: the r218 matrix promotion.  Same period `ln 3`; the frequency
  content enriches to the spectrum of `χ_M`, witnessed by a concrete `2 × 2`
  example with two distinct eigen-phases.

## Cross-references

* `codex/COSMOLOGY_W_BRIDGE_2026-08-10.md`
* `PF/SigmaAbscissa_r212.lean` — `digitBlock_sum`, `sigma`
* `PF/EulerFactorThree_r214.lean` — `digitSum3`, `digitSum3_pow_mul`
* `PF/DigitWordSystem_r218.lean` — `sum_wordWeight`, `chi`

No `sorry`, no `native_decide`, no `axiom`, no `Prop := True`.
Axiom audit at the end of the file.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import PF.SigmaAbscissa_r212
import PF.EulerFactorThree_r214
import PF.DigitWordSystem_r218

open scoped Real

namespace PrincipiaTractalis.LogPeriodicity

open PrincipiaTractalis.EulerFactorThree (digitSum3)

/-! ## §1 The summatory function and its EXACT scaling

`S(ω, N) = Σ_{n < N} ω^{D₃(n)}`, and the block factor `χ(ω) = 1 + ω + ω²`.

The renormalisation relation below is exact at every power of 3.  It is r212's
`digitBlock_sum` read as a recursion in `k` rather than as a closed form. -/

/-- **The summatory function of the ternary digit character.**
`S(ω, N) = Σ_{n < N} ω^{D₃(n)}`, with `D₃ = digitSum3` from r214. -/
noncomputable def S (ω : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, ω ^ (digitSum3 n)

/-- **The block factor** `χ(ω) = 1 + ω + ω²`.  This is r212's `1 + ω + ω²` and
r218's `chi` in the scalar (`1 × 1`) case. -/
noncomputable def chi (ω : ℂ) : ℂ := 1 + ω + ω ^ 2

@[simp] theorem S_zero (ω : ℂ) : S ω 0 = 0 := by simp [S]

@[simp] theorem S_one (ω : ℂ) : S ω 1 = 1 := by simp [S, digitSum3]

/-- **The closed form.**  `S(ω, 3^k) = χ(ω)^k`.  This is exactly r212's
`digitBlock_sum`; `digitSum3` is by definition `(Nat.digits 3 ·).sum`. -/
theorem S_pow_three_eq_chi_pow (ω : ℂ) (k : ℕ) : S ω (3 ^ k) = chi ω ^ k :=
  PrincipiaTractalis.SigmaAbscissa.digitBlock_sum ω k

/-- Trivial but load-bearing: `χ^{k+1} = χ · χ^k`.  The multiplicative fact that
underlies every phase statement in §3. -/
theorem chi_pow_succ (ω : ℂ) (k : ℕ) : chi ω ^ (k + 1) = chi ω * chi ω ^ k :=
  pow_succ' (chi ω) k

/-- **THE EXACT RENORMALISATION RELATION.**

    S(ω, 3^{k+1})  =  χ(ω) · S(ω, 3^k)

for every `ω : ℂ` and every `k`.  Exact — no error term, no asymptotics, no
hypothesis on `ω`.  The summatory function of the base-3 digit character is
exactly self-similar under `N ↦ 3N` along the powers of the base. -/
theorem S_three_mul (ω : ℂ) (k : ℕ) : S ω (3 ^ (k + 1)) = chi ω * S ω (3 ^ k) := by
  rw [S_pow_three_eq_chi_pow, S_pow_three_eq_chi_pow, chi_pow_succ]

/-- The same relation written the way it is quoted: `S(3N) = χ · S(N)`, at
`N = 3^k`. -/
theorem S_three_mul_scale (ω : ℂ) (k : ℕ) : S ω (3 * 3 ^ k) = chi ω * S ω (3 ^ k) := by
  rw [show (3 : ℕ) * 3 ^ k = 3 ^ (k + 1) from (pow_succ' 3 k).symm]
  exact S_three_mul ω k

/-! ## §2 The normalised fluctuation is invariant

Dividing out the deterministic factor `χ^k` leaves something that does not move
at all: the fluctuation is *exactly* scale-invariant, not merely
scale-invariant in distribution or in the limit. -/

/-- **The normalised summatory function repeats under `N ↦ 3N`.** -/
theorem normalised_S_invariant (ω : ℂ) (hχ : chi ω ≠ 0) (k : ℕ) :
    S ω (3 ^ (k + 1)) / chi ω ^ (k + 1) = S ω (3 ^ k) / chi ω ^ k := by
  rw [S_pow_three_eq_chi_pow, S_pow_three_eq_chi_pow,
    div_self (pow_ne_zero _ hχ), div_self (pow_ne_zero _ hχ)]

/-- **…hence it is constant in `k`.**  The normalisation chosen is `S / χ^k`,
whose value is `S(ω, 1) = 1` — the empty-scale seed.  (This is the cleanest
normalisation: it needs no extra constant, and `S(ω,1) = ω^{D₃(0)} = ω^0 = 1`
for every `ω`.) -/
theorem normalised_S_const (ω : ℂ) (hχ : chi ω ≠ 0) (k : ℕ) :
    S ω (3 ^ k) / chi ω ^ k = S ω 1 := by
  rw [S_pow_three_eq_chi_pow, div_self (pow_ne_zero _ hχ), S_one]

/-- The value, spelled out. -/
theorem normalised_S_eq_one (ω : ℂ) (hχ : chi ω ≠ 0) (k : ℕ) :
    S ω (3 ^ k) / chi ω ^ k = 1 := by
  rw [normalised_S_const ω hχ k, S_one]

/-! ### The link to r212's abscissa σ

At `ω = e^{iπα}` the block factor's modulus is `|1 + 2 cos πα|`, so
`log₃‖χ‖` is literally r212's `sigma`.  The amplitude exponent of the
self-similar scaling and the abscissa of convergence of `R_f` are the same
number. -/

/-- The framework's `ω = e^{iπα}`. -/
noncomputable def omega (α : ℝ) : ℂ := Complex.exp (((π * α : ℝ) : ℂ) * Complex.I)

/-- `‖χ(e^{iπα})‖ = |1 + 2 cos(πα)|` — r212 §2, restated for `chi`. -/
theorem norm_chi_omega (α : ℝ) : ‖chi (omega α)‖ = |1 + 2 * Real.cos (π * α)| :=
  PrincipiaTractalis.SigmaAbscissa.norm_one_add_exp_add_exp_sq_pi_mul α

/-- **σ is the amplitude exponent.**  r212's abscissa `σ(α) = log₃|1 + 2cos πα|`
is exactly `log₃‖χ(e^{iπα})‖`, the exponent governing `‖S(ω, 3^k)‖ = ‖χ‖^k`. -/
theorem sigma_eq_logb_norm_chi (α : ℝ) :
    PrincipiaTractalis.SigmaAbscissa.sigma α = Real.logb 3 ‖chi (omega α)‖ := by
  rw [norm_chi_omega]
  rfl

/-- `3^{σ(α)} = ‖χ‖`, away from the degenerate point `1 + 2cos πα = 0`
(where mathlib's `logb b 0 = 0` makes `σ` vanish for a reason unrelated to the
scaling — see r212's header). -/
theorem rpow_sigma_eq_norm_chi (α : ℝ) (hne : 1 + 2 * Real.cos (π * α) ≠ 0) :
    (3 : ℝ) ^ (PrincipiaTractalis.SigmaAbscissa.sigma α) = ‖chi (omega α)‖ := by
  have hpos : 0 < ‖chi (omega α)‖ := by
    rw [norm_chi_omega]
    exact abs_pos.mpr hne
  rw [sigma_eq_logb_norm_chi]
  exact Real.rpow_logb (by norm_num) (by norm_num) hpos

/-! ## §3 THE LOG-PERIODICITY

The exponent `k` in `S(ω, 3^k) = χ^k` is `log₃ N`.  Splitting `χ^k` into
modulus and phase,

    χ^k  =  ‖χ‖^k · e^{i k arg χ}  =  N^{log₃‖χ‖} · e^{i (arg χ) log₃ N} ,

so the amplitude is a pure power law in `N` and the phase is **linear in
`log₃ N`** — i.e. the modulation is periodic in `ln N` with period `ln 3`.
-/

/-- **The log-period.**  `ln 3 = 1.0986122886681098`. -/
noncomputable def logPeriod : ℝ := Real.log 3

/-- **The log-frequency.**  `2π / ln 3 = 5.719202...`  No free parameter: only
the base 3 enters. -/
noncomputable def logFrequency : ℝ := 2 * π / Real.log 3

theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem log_three_ne_zero : Real.log 3 ≠ 0 := ne_of_gt log_three_pos

theorem logPeriod_pos : 0 < logPeriod := log_three_pos

/-- **THE PARAMETER-FREE IDENTITY.**  `logFrequency · logPeriod = 2π`.

The frequency is fixed by the base alone.  Nothing is fitted. -/
theorem logFrequency_mul_logPeriod : logFrequency * logPeriod = 2 * π := by
  unfold logFrequency logPeriod
  field_simp

/-- **One full period per factor of 3 in scale**, on the `log₃` axis. -/
theorem logb_three_mul (x : ℝ) (hx : 0 < x) :
    Real.logb 3 (3 * x) = 1 + Real.logb 3 x := by
  rw [Real.logb_mul (by norm_num) (ne_of_gt hx), Real.logb_self_eq_one (by norm_num)]

/-- The statement in the form the brief names: for natural `N > 0`,
`log₃(3N) = 1 + log₃ N`. -/
theorem log_period_eq_log_three : ∀ N : ℕ, 0 < N → Real.logb 3 (3 * (N : ℝ)) = 1 + Real.logb 3 N :=
  fun N hN => logb_three_mul (N : ℝ) (by exact_mod_cast hN)

/-- The same on the `ln` axis: the period is `ln 3` exactly. -/
theorem log_three_mul (x : ℝ) (hx : 0 < x) :
    Real.log (3 * x) = logPeriod + Real.log x :=
  Real.log_mul (by norm_num) (ne_of_gt hx)

/-- The exponent `k` in `S(ω, 3^k)` IS `log₃ N`.  This is the identification
that turns the discrete recursion of §1 into a statement about a continuous
log-scale variable. -/
theorem logb_three_pow (k : ℕ) : Real.logb 3 ((3 : ℝ) ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-! ### Amplitude: a pure power law in `N` -/

/-- `‖S(ω, 3^k)‖ = ‖χ(ω)‖^k`. -/
theorem norm_S_pow_three (ω : ℂ) (k : ℕ) : ‖S ω (3 ^ k)‖ = ‖chi ω‖ ^ k := by
  rw [S_pow_three_eq_chi_pow, norm_pow]

/-- The amplitude written against the continuous variable: at scale
`N = 3^k`, `‖S‖ = ‖χ‖^{log₃ N}`. -/
theorem norm_S_rpow_logb (ω : ℂ) (k : ℕ) :
    ‖S ω (3 ^ k)‖ = ‖chi ω‖ ^ (Real.logb 3 ((3 : ℝ) ^ k)) := by
  rw [logb_three_pow, norm_S_pow_three, Real.rpow_natCast]

/-! ### Phase: linear in `log₃ N`, hence log-periodic

`Complex.arg` is valued in `(−π, π]`, so the subtraction statement is made in
`Real.Angle = ℝ / 2πℤ`, where it is exactly true.  See §0.4. -/

/-- **THE PHASE ADVANCE, exactly, mod 2π.**

    arg(χ^{k+1}) − arg(χ^k) = arg(χ)      in ℝ / 2πℤ

The phase advances by `arg χ` per factor of 3 in `N`.  Unconditional: no
hypothesis on `ω`, because `Complex.arg 0 = 0` makes the degenerate case
`χ = 0` true as well.

The name says "triadic step" because that is what it is: one step of the
ternary scaling, a factor of 3 in `N`.  An earlier draft called this
`phase_advance_per_octave`, which was wrong — an octave is a factor of 2.  A
theorem name that misstates its own content is the defect this corpus spent
2026-08-06 ledgering (`smoothness` delivering boundedness,
`divergenceFreePreserved` discarding its solution argument); it is not
reintroduced here. -/
theorem phase_advance_per_triadic_step (ω : ℂ) (k : ℕ) :
    (Complex.arg (chi ω ^ (k + 1)) : Real.Angle) - (Complex.arg (chi ω ^ k) : Real.Angle)
      = (Complex.arg (chi ω) : Real.Angle) := by
  rw [Complex.arg_pow_coe_angle, Complex.arg_pow_coe_angle, succ_nsmul]
  abel

/-- **The phase of the summatory function is `k · arg χ`**, i.e. linear in
`k = log₃ N`.  This is what "log-periodic" means, stated on the nose. -/
theorem arg_S_pow_three (ω : ℂ) (k : ℕ) :
    (Complex.arg (S ω (3 ^ k)) : Real.Angle) = k • (Complex.arg (chi ω) : Real.Angle) := by
  rw [S_pow_three_eq_chi_pow, Complex.arg_pow_coe_angle]

/-- Consecutive scales differ in phase by exactly `arg χ`. -/
theorem arg_S_advance (ω : ℂ) (k : ℕ) :
    (Complex.arg (S ω (3 ^ (k + 1))) : Real.Angle) - (Complex.arg (S ω (3 ^ k)) : Real.Angle)
      = (Complex.arg (chi ω) : Real.Angle) := by
  rw [S_pow_three_eq_chi_pow, S_pow_three_eq_chi_pow]
  exact phase_advance_per_triadic_step ω k

/-! ### The modulation, in the form the physics uses -/

/-- The log-periodic modulation with phase offset `φ₀`:
`cos( (2π/ln 3) · ln x + φ₀ )`. -/
noncomputable def logModulation (φ₀ : ℝ) (x : ℝ) : ℝ :=
  Real.cos (logFrequency * Real.log x + φ₀)

/-- The argument advances by exactly `2π` when the scale is multiplied by 3. -/
theorem logFrequency_log_three_mul (x : ℝ) (hx : 0 < x) :
    logFrequency * Real.log (3 * x) = logFrequency * Real.log x + 2 * π := by
  rw [Real.log_mul (by norm_num) (ne_of_gt hx), mul_add]
  have h : logFrequency * Real.log 3 = 2 * π := by
    unfold logFrequency
    field_simp
  rw [h]
  ring

/-- **THE LOG-PERIODICITY THEOREM, physics form.**

    cos( (2π / ln 3) · ln x + φ₀ )   is invariant under   x ↦ 3x

for every offset `φ₀` and every `x > 0`.  One full period of the modulation per
factor of 3 in scale, with the period in `ln`-scale being exactly
`ln 3 = 1.0986122886681098` and the frequency exactly `2π/ln 3 = 5.719202...`
— fixed by the base alone. -/
theorem logModulation_three_mul (φ₀ x : ℝ) (hx : 0 < x) :
    logModulation φ₀ (3 * x) = logModulation φ₀ x := by
  unfold logModulation
  rw [show logFrequency * Real.log (3 * x) + φ₀
      = (logFrequency * Real.log x + φ₀) + 2 * π by
    rw [logFrequency_log_three_mul x hx]; ring]
  exact Real.cos_add_two_pi _

/-- Iterated: invariant under `x ↦ 3^j x` for every `j`. -/
theorem logModulation_three_pow_mul (φ₀ x : ℝ) (hx : 0 < x) (j : ℕ) :
    logModulation φ₀ ((3 : ℝ) ^ j * x) = logModulation φ₀ x := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hpos : (0 : ℝ) < (3 : ℝ) ^ j * x := by positivity
      rw [show ((3 : ℝ) ^ (j + 1) * x) = 3 * ((3 : ℝ) ^ j * x) by ring,
        logModulation_three_mul φ₀ _ hpos, ih]

/-! ## §4 NON-VACUITY

None of the hypotheses above is empty, and `S` is genuinely non-constant.

`ω = i` is the sharpest witness: `χ(i) = i`, so `S(i, 3^k) = i^k` rotates by a
quarter turn per factor of 3 — a log-period of exactly four factors of 3
(N ↦ 81N) in the *sign pattern*, while the underlying modulation period is
`ln 3`.  `ω = −1` gives `χ(−1) = 1`, a non-constant `S` with trivial block
factor. -/

/-- `χ(i) = 1 + i + i² = i`. -/
@[simp] theorem chi_I : chi Complex.I = Complex.I := by
  unfold chi
  rw [Complex.I_sq]
  ring

theorem chi_I_ne_zero : chi Complex.I ≠ 0 := by
  rw [chi_I]
  exact Complex.I_ne_zero

/-- `S(i, 3^k) = i^k`. -/
theorem S_I_pow_three (k : ℕ) : S Complex.I (3 ^ k) = Complex.I ^ k := by
  rw [S_pow_three_eq_chi_pow, chi_I]

/-- **Explicit numeric instance of §1, computed directly from the definition**
(not via `S_pow_three_eq_chi_pow`): `S(i, 3) = i^0 + i^1 + i^2 = i`. -/
theorem S_I_three_direct : S Complex.I 3 = Complex.I := by
  show (∑ n ∈ Finset.range 3, Complex.I ^ (digitSum3 n)) = Complex.I
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [digitSum3, Complex.I_sq]

/-- **Explicit numeric instance, one scale up**, again computed directly:
`S(i, 9) = −1 = χ(i)²`.  The digit sums over `n < 9` are
`0,1,2,1,2,3,2,3,4`. -/
theorem S_I_nine_direct : S Complex.I 9 = -1 := by
  show (∑ n ∈ Finset.range 9, Complex.I ^ (digitSum3 n)) = -1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [digitSum3, pow_succ, Complex.I_sq]
  ring

/-- **The renormalisation relation, verified numerically at `k = 1`:**
`S(i, 9) = χ(i) · S(i, 3)`, both sides computed from the definition. -/
theorem S_I_three_mul_numeric : S Complex.I 9 = chi Complex.I * S Complex.I 3 := by
  rw [S_I_nine_direct, S_I_three_direct, chi_I, Complex.I_mul_I]

/-- `S(i, ·)` is genuinely non-constant along the powers of 3: `S(i,1) = 1` but
`S(i,3) = i`. -/
theorem S_I_nonconstant : S Complex.I (3 ^ 0) ≠ S Complex.I (3 ^ 1) := by
  rw [S_I_pow_three, S_I_pow_three]
  simp [Complex.ext_iff]

/-- The phase advance at `ω = i` is a quarter turn: `arg χ(i) = π/2`. -/
theorem arg_chi_I : Complex.arg (chi Complex.I) = π / 2 := by
  rw [chi_I]
  exact Complex.arg_I

/-- `χ(−1) = 1 − 1 + 1 = 1`. -/
@[simp] theorem chi_neg_one : chi (-1 : ℂ) = 1 := by
  unfold chi
  ring

theorem chi_neg_one_ne_zero : chi (-1 : ℂ) ≠ 0 := by
  rw [chi_neg_one]
  exact one_ne_zero

/-- At `ω = −1` the block factor is trivial, yet `S` is still non-constant in
`N` off the powers of 3: `S(−1, 1) = 1` but `S(−1, 2) = 0`. -/
theorem S_neg_one_nonconstant : S (-1 : ℂ) 1 ≠ S (-1 : ℂ) 2 := by
  have h2 : S (-1 : ℂ) 2 = 0 := by
    show (∑ n ∈ Finset.range 2, (-1 : ℂ) ^ (digitSum3 n)) = 0
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [digitSum3]
  rw [S_one, h2]
  exact one_ne_zero

/-- Non-vacuity of §2 and §3 bundled: the hypothesis `χ(ω) ≠ 0` is satisfiable,
the normalised quantity is constant there, and the phase genuinely advances. -/
theorem nonvacuous_witness :
    chi Complex.I ≠ 0 ∧
    (∀ k : ℕ, S Complex.I (3 ^ k) / chi Complex.I ^ k = 1) ∧
    S Complex.I (3 ^ 0) ≠ S Complex.I (3 ^ 1) ∧
    Complex.arg (chi Complex.I) ≠ 0 :=
  ⟨chi_I_ne_zero,
   fun k => normalised_S_eq_one Complex.I chi_I_ne_zero k,
   S_I_nonconstant,
   by rw [arg_chi_I]; positivity⟩

/-! ## §5 (P2) THE MATRIX PROMOTION — r218

r218 replaces the scalar digit weight by an element `M d` of a possibly
non-commutative semiring and takes the ORDERED product over digit positions.
Its `sum_wordWeight` says the block sum over all `3^k` length-`k` digit words is
`χ_M^k` with `χ_M = M₀ + M₁ + M₂`.

Everything in §1 survives verbatim with `χ` a matrix: the recursion is still
`S_M(k+1) = χ_M · S_M(k)`, the scale is still `3^k` words, so the log-period is
still `ln 3`.  **What enriches is the frequency content**: `χ_M` has a spectrum
rather than a single value, so the phase decomposes into one log-frequency
`arg λ / ln 3` per eigenvalue `λ`.  §5.2 exhibits a concrete `2 × 2` weight
whose `χ_M` has two eigenvalues with *distinct* arguments — two independent
log-frequencies at one and the same log-period. -/

/-- The matrix analogue of `S`: the sum of ordered word weights over all `3^k`
base-3 digit words of length `k` (r218's index set). -/
noncomputable def SM {R : Type*} [Semiring R] (M : Fin 3 → R) (k : ℕ) : R :=
  ∑ d : Fin k → Fin 3, PrincipiaTractalis.DigitWordSystem.wordWeight M d

/-- `S_M(k) = χ_M^k` — this is r218's `sum_wordWeight`, quoted. -/
theorem SM_eq_chi_pow {R : Type*} [Semiring R] (M : Fin 3 → R) (k : ℕ) :
    SM M k = PrincipiaTractalis.DigitWordSystem.chi M ^ k :=
  PrincipiaTractalis.DigitWordSystem.sum_wordWeight M k

/-- **THE RENORMALISATION RELATION SURVIVES THE PROMOTION.**

    S_M(k+1) = χ_M · S_M(k)

with `χ_M = M₀ + M₁ + M₂` a possibly non-commuting semiring element.  Same
exactness, same scale factor 3, same log-period `ln 3`. -/
theorem SM_three_mul {R : Type*} [Semiring R] (M : Fin 3 → R) (k : ℕ) :
    SM M (k + 1) = PrincipiaTractalis.DigitWordSystem.chi M * SM M k := by
  rw [SM_eq_chi_pow, SM_eq_chi_pow, pow_succ']

/-- The scale really is `3^k`: there are exactly `3^k` digit words of length
`k`, so the index `k` is `log₃` of the number of words, exactly as in §3. -/
theorem word_count (k : ℕ) : Fintype.card (Fin k → Fin 3) = 3 ^ k := by
  simp

/-! ### §5.2 Two distinct log-frequencies at one log-period

`M d = diag(i^d, (−1)^d)` — the direct sum of the `ω = i` and `ω = −1` scalar
systems of §4.  Then `χ_M = diag(i, 1)`: two eigenvalues, arguments `π/2` and
`0`.  The log-period is `ln 3` for both; the log-frequencies differ. -/

/-- The concrete `2 × 2` digit weight: `M 0 = 1`, `M 1 = diag(i, −1)`,
`M 2 = diag(−1, 1)`. -/
noncomputable def Mtwo : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![Complex.I, 0; 0, -1], !![-1, 0; 0, 1]]

/-- `χ_{Mtwo} = diag(i, 1)`. -/
theorem chi_Mtwo :
    PrincipiaTractalis.DigitWordSystem.chi Mtwo = !![Complex.I, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PrincipiaTractalis.DigitWordSystem.chi, Mtwo]

/-- `(1, 0)` is an eigenvector of `χ_{Mtwo}` with eigenvalue `i`. -/
theorem chi_Mtwo_eigen_I :
    (PrincipiaTractalis.DigitWordSystem.chi Mtwo).mulVec ![1, 0]
      = Complex.I • (![1, 0] : Fin 2 → ℂ) := by
  rw [chi_Mtwo]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- `(0, 1)` is an eigenvector of `χ_{Mtwo}` with eigenvalue `1`. -/
theorem chi_Mtwo_eigen_one :
    (PrincipiaTractalis.DigitWordSystem.chi Mtwo).mulVec ![0, 1]
      = (1 : ℂ) • (![0, 1] : Fin 2 → ℂ) := by
  rw [chi_Mtwo]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **The two eigen-phases are distinct.**  `arg i = π/2 ≠ 0 = arg 1`.

So the matrix system carries TWO independent log-frequencies,
`arg(i)/ln 3` and `arg(1)/ln 3 = 0`, at the SAME log-period `ln 3`.  In the
scalar system (§1–§4) there is exactly one. -/
theorem Mtwo_two_log_frequencies :
    Complex.arg Complex.I ≠ Complex.arg (1 : ℂ) := by
  rw [Complex.arg_I, Complex.arg_one]
  positivity

/-- The promotion, bundled: the exact renormalisation holds for `Mtwo`, its
`χ` has two eigenvalues with distinct arguments, and the scale factor — hence
the log-period — is unchanged at 3. -/
theorem matrix_promotion_summary :
    (∀ k : ℕ, SM Mtwo (k + 1)
        = PrincipiaTractalis.DigitWordSystem.chi Mtwo * SM Mtwo k) ∧
    (PrincipiaTractalis.DigitWordSystem.chi Mtwo).mulVec ![1, 0]
        = Complex.I • (![1, 0] : Fin 2 → ℂ) ∧
    (PrincipiaTractalis.DigitWordSystem.chi Mtwo).mulVec ![0, 1]
        = (1 : ℂ) • (![0, 1] : Fin 2 → ℂ) ∧
    Complex.arg Complex.I ≠ Complex.arg (1 : ℂ) ∧
    (∀ k : ℕ, Fintype.card (Fin k → Fin 3) = 3 ^ k) :=
  ⟨SM_three_mul Mtwo, chi_Mtwo_eigen_I, chi_Mtwo_eigen_one,
   Mtwo_two_log_frequencies, word_count⟩

/-! ## §6 The capstone -/

/-- **THE STONE.**

1. The exact renormalisation `S(ω, 3^{k+1}) = χ(ω) · S(ω, 3^k)`, for every `ω`.
2. The normalised fluctuation is invariant, hence constant, wherever `χ ≠ 0`.
3. The phase advances by exactly `arg χ` per factor of 3 (in `ℝ/2πℤ`).
4. The log-period is `ln 3` and the log-frequency is `2π/ln 3`, and their
   product is `2π` — **no free parameter**.
5. The modulation `cos((2π/ln 3)·ln x + φ₀)` is invariant under `x ↦ 3x`.

This says nothing about the CMB, nothing about cosmic structure, and nothing
about physical reality.  See §0.2 and §0.3. -/
theorem log_periodicity_stone :
    (∀ (ω : ℂ) (k : ℕ), S ω (3 ^ (k + 1)) = chi ω * S ω (3 ^ k)) ∧
    (∀ (ω : ℂ), chi ω ≠ 0 → ∀ k : ℕ, S ω (3 ^ k) / chi ω ^ k = 1) ∧
    (∀ (ω : ℂ) (k : ℕ),
      (Complex.arg (S ω (3 ^ (k + 1))) : Real.Angle)
        - (Complex.arg (S ω (3 ^ k)) : Real.Angle)
        = (Complex.arg (chi ω) : Real.Angle)) ∧
    (logFrequency * logPeriod = 2 * π) ∧
    (∀ (φ₀ x : ℝ), 0 < x → logModulation φ₀ (3 * x) = logModulation φ₀ x) :=
  ⟨S_three_mul,
   fun ω hχ k => normalised_S_eq_one ω hχ k,
   arg_S_advance,
   logFrequency_mul_logPeriod,
   fun φ₀ x hx => logModulation_three_mul φ₀ x hx⟩

end PrincipiaTractalis.LogPeriodicity

/-! ## §7 — kernel axiom audit

House rule: the audit lives IN the file, so `lake build` re-runs it.  Every
declaration below must report exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms PrincipiaTractalis.LogPeriodicity.S_zero
#print axioms PrincipiaTractalis.LogPeriodicity.S_one
#print axioms PrincipiaTractalis.LogPeriodicity.S_pow_three_eq_chi_pow
#print axioms PrincipiaTractalis.LogPeriodicity.chi_pow_succ
#print axioms PrincipiaTractalis.LogPeriodicity.S_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.S_three_mul_scale
#print axioms PrincipiaTractalis.LogPeriodicity.normalised_S_invariant
#print axioms PrincipiaTractalis.LogPeriodicity.normalised_S_const
#print axioms PrincipiaTractalis.LogPeriodicity.normalised_S_eq_one
#print axioms PrincipiaTractalis.LogPeriodicity.norm_chi_omega
#print axioms PrincipiaTractalis.LogPeriodicity.sigma_eq_logb_norm_chi
#print axioms PrincipiaTractalis.LogPeriodicity.rpow_sigma_eq_norm_chi
#print axioms PrincipiaTractalis.LogPeriodicity.log_three_pos
#print axioms PrincipiaTractalis.LogPeriodicity.log_three_ne_zero
#print axioms PrincipiaTractalis.LogPeriodicity.logPeriod_pos
#print axioms PrincipiaTractalis.LogPeriodicity.logFrequency_mul_logPeriod
#print axioms PrincipiaTractalis.LogPeriodicity.logb_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.log_period_eq_log_three
#print axioms PrincipiaTractalis.LogPeriodicity.log_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.logb_three_pow
#print axioms PrincipiaTractalis.LogPeriodicity.norm_S_pow_three
#print axioms PrincipiaTractalis.LogPeriodicity.norm_S_rpow_logb
#print axioms PrincipiaTractalis.LogPeriodicity.phase_advance_per_triadic_step
#print axioms PrincipiaTractalis.LogPeriodicity.arg_S_pow_three
#print axioms PrincipiaTractalis.LogPeriodicity.arg_S_advance
#print axioms PrincipiaTractalis.LogPeriodicity.logFrequency_log_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.logModulation_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.logModulation_three_pow_mul
#print axioms PrincipiaTractalis.LogPeriodicity.chi_I
#print axioms PrincipiaTractalis.LogPeriodicity.chi_I_ne_zero
#print axioms PrincipiaTractalis.LogPeriodicity.S_I_pow_three
#print axioms PrincipiaTractalis.LogPeriodicity.S_I_three_direct
#print axioms PrincipiaTractalis.LogPeriodicity.S_I_nine_direct
#print axioms PrincipiaTractalis.LogPeriodicity.S_I_three_mul_numeric
#print axioms PrincipiaTractalis.LogPeriodicity.S_I_nonconstant
#print axioms PrincipiaTractalis.LogPeriodicity.arg_chi_I
#print axioms PrincipiaTractalis.LogPeriodicity.chi_neg_one
#print axioms PrincipiaTractalis.LogPeriodicity.chi_neg_one_ne_zero
#print axioms PrincipiaTractalis.LogPeriodicity.S_neg_one_nonconstant
#print axioms PrincipiaTractalis.LogPeriodicity.nonvacuous_witness
#print axioms PrincipiaTractalis.LogPeriodicity.SM_eq_chi_pow
#print axioms PrincipiaTractalis.LogPeriodicity.SM_three_mul
#print axioms PrincipiaTractalis.LogPeriodicity.word_count
#print axioms PrincipiaTractalis.LogPeriodicity.chi_Mtwo
#print axioms PrincipiaTractalis.LogPeriodicity.chi_Mtwo_eigen_I
#print axioms PrincipiaTractalis.LogPeriodicity.chi_Mtwo_eigen_one
#print axioms PrincipiaTractalis.LogPeriodicity.Mtwo_two_log_frequencies
#print axioms PrincipiaTractalis.LogPeriodicity.matrix_promotion_summary
#print axioms PrincipiaTractalis.LogPeriodicity.log_periodicity_stone
