/-
# Ch 09 Quantum-Enhancement Refutation (2026-10-05)

## Manuscript claim

`Principia_Fractalis_master_folder/chapters/ch09_spectral_unity.tex`,
§"Experimental Signatures", item 1 ("Quantum computers and consciousness"),
supplies the predicted enhancement factor

  `η_enhance = exp( (π/10) · Δ · N_qubits )`

and asserts: "For `N_qubits = 1000`, this gives `η ≈ 1.31`, a 31% speedup
detectable with existing hardware."

The chapter's `Δ` is the empirical spectral gap defined at its line 122,
`Δ = 0.2221441469 − 0.1330222423 = 0.0891219046`.

## The arithmetic

  `(π/10) · 0.0891219046 = 0.0279984721`
  exponent at `N = 1000`  :  `27.9984721`
  `η(1000) = exp(27.998…) = 1.444 × 10¹²`

not `1.31`. The claim is wrong by twelve orders of magnitude, and it is wrong
in the direction of UNDERSTATING the framework's own formula: read literally,
the formula predicts an enhancement of `10¹²` at a thousand qubits, which is a
far stronger assertion than "a 31% speedup".

## Where 1.31 comes from

`η = 1.31` is reached at about **ten** qubits, not a thousand:

  `η(9)  = 1.2866`
  `η(10) = 1.3231`

So `ln(1.31) / 0.0279984721 = 9.644`. The figure "31%" is the value of the
chapter's own formula in the neighbourhood of `N ≈ 10`. The defect is the
substituted qubit count, not the exponential law.

## Robustness to the `Δ` ambiguity

ch09's own rigor ledger (its line 486) records that the empirical
`λ₀(H_NP) ≈ 0.1330` "does *not* match the certified closed form
`π/(10(φ+1/4)) ≈ 0.1682`". Using the certified closed forms instead gives
`Δ = 0.2221441469 − 0.168176418 = 0.0539677`, hence

  `η(1000) = 2.308 × 10⁷`,  and `η = 1.31` at `N = 15.93`.

Both readings agree on the only thing that matters here: at `N = 1000` the
formula returns an astronomically large number, and `1.31` corresponds to a
qubit count in the range of ten to sixteen. The refutation below is proved for
the empirical `Δ` the chapter actually substitutes, and the conclusion is
unchanged under the certified one.

## What this file proves (axiom-free)

1. `exponent_at_1000_gt_27` — the exponent at `N = 1000` exceeds `27`.
   Strategy: the exponent is `π · (Δ · 100)` with an explicit positive
   rational factor; bound `π > 3.141592` (`Real.pi_gt_d6`).

2. `etaEnhance_1000_gt_1e11` — hence `η(1000) > 10¹¹`.
   Strategy: `exp` is monotone, `exp 27 = (exp 1)^27`, and
   `exp 1 > 2.7182818283` (`Real.exp_one_gt_d9`) gives
   `(exp 1)^27 > 2.7182818³… > 10¹¹`.

3. `etaEnhance_1000_ne_claimed` — hence `η(1000) ≠ 1.31`.

4. `etaEnhance_strictMono` — `η` is strictly increasing in `N_qubits`.

5. `claimedEta_lt_etaEnhance_ten` — **ten qubits already exceed the claim.**
   Strategy: `exp x = (exp (x/8))^8` and `1 + x/8 ≤ exp (x/8)`
   (`Real.add_one_le_exp`) give `exp x ≥ (1 + x/8)^8`, and at `N = 10` that
   rational bound already exceeds `131/100`.
   With (4) this places the qubit count that actually yields `1.31` strictly
   BELOW ten, quantifying the substitution error as a factor of about `100`
   in `N` — and as twelve orders of magnitude in `η`.

## What survives, and what does not

Survives: an exponential enhancement law `η = exp(c·N)` with
`c = (π/10)·Δ` is a legitimate framework output, and the chapter's claim that
the effect is reachable "with existing hardware" survives in a stronger form
than stated — ten qubits suffice for a 32% enhancement under this law.

Does not: the pairing of `N = 1000` with `η ≈ 1.31`. Those two numbers are not
compatible under the chapter's own formula, and the sentence drawing a
"31% speedup" from a thousand qubits is false.

This is a NEGATIVE result about one experimental-signature estimate. It touches
no rigor-ledger label elsewhere, and in particular says nothing about the
P-vs-NP material, which ch09 already files as CONDITIONAL REDUCTION.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch09Refutation

/-! ## §1 — The chapter's inputs, verbatim -/

/-- The empirical spectral gap ch09 defines at its line 122 and substitutes
    here: `0.2221441469 − 0.1330222423 = 0.0891219046`. -/
noncomputable def Delta_ch09 : ℝ := 891219046 / 10 ^ 10

/-- The chapter's enhancement law, as a function of the qubit count. -/
noncomputable def etaEnhance (N : ℝ) : ℝ :=
  Real.exp (Real.pi / 10 * Delta_ch09 * N)

/-- The chapter's claimed value, `η ≈ 1.31`. -/
noncomputable def claimedEta : ℝ := 131 / 100

/-! ## §2 — The value at the stated thousand qubits -/

/-- **(1)** The exponent at `N = 1000` exceeds `27`. -/
theorem exponent_at_1000_gt_27 :
    (27 : ℝ) < Real.pi / 10 * Delta_ch09 * 1000 := by
  unfold Delta_ch09
  nlinarith [Real.pi_gt_d6]

/-- **(2)** Hence `η(1000) > 10¹¹`. -/
theorem etaEnhance_1000_gt_1e11 : (10 : ℝ) ^ 11 < etaEnhance 1000 := by
  have hmono : Real.exp 27 < etaEnhance 1000 := by
    unfold etaEnhance
    exact Real.exp_lt_exp.mpr exponent_at_1000_gt_27
  have hpow : Real.exp 27 = Real.exp 1 ^ 27 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he : (2.7182818 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have hlow : (10 : ℝ) ^ 11 < Real.exp 1 ^ 27 := by
    have hstep : (2.7182818 : ℝ) ^ 27 ≤ Real.exp 1 ^ 27 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt he) 27
    have hnum : (10 : ℝ) ^ 11 < (2.7182818 : ℝ) ^ 27 := by norm_num
    linarith
  rw [hpow] at hmono
  linarith

/-- **(3)** Hence the value at a thousand qubits is not the claimed `1.31`. -/
theorem etaEnhance_1000_ne_claimed : etaEnhance 1000 ≠ claimedEta := by
  intro h_eq
  have h := etaEnhance_1000_gt_1e11
  rw [h_eq] at h
  unfold claimedEta at h
  norm_num at h

/-! ## §3 — Monotonicity in the qubit count -/

/-- **(4)** The enhancement factor is strictly increasing in `N_qubits`. -/
theorem etaEnhance_strictMono : StrictMono etaEnhance := by
  intro a b hab
  unfold etaEnhance
  refine Real.exp_lt_exp.mpr ?_
  have hc : (0 : ℝ) < Real.pi / 10 * Delta_ch09 := by
    unfold Delta_ch09
    have := Real.pi_pos
    positivity
  exact mul_lt_mul_of_pos_left hab hc

/-! ## §4 — Ten qubits already exceed the claim -/

/-- **(5)** `η(10) > 1.31`: **ten** qubits already exceed the enhancement the
    chapter attributes to a thousand. With `etaEnhance_strictMono` this places
    the qubit count that actually yields `1.31` strictly below ten. -/
theorem claimedEta_lt_etaEnhance_ten : claimedEta < etaEnhance 10 := by
  unfold etaEnhance claimedEta Delta_ch09
  set x : ℝ := Real.pi / 10 * (891219046 / 10 ^ 10) * 10 with hxdef
  have hxlb : (0.27998465 : ℝ) < x := by
    rw [hxdef]
    nlinarith [Real.pi_gt_d6]
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hsplit : Real.exp (x / 8) ^ 8 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hlin : 1 + x / 8 ≤ Real.exp (x / 8) := by
    have := Real.add_one_le_exp (x / 8)
    linarith
  have hpow : (1 + x / 8) ^ 8 ≤ Real.exp x := by
    rw [← hsplit]
    exact pow_le_pow_left₀ (by linarith) hlin 8
  have hmono : (1 + (0.27998465 : ℝ) / 8) ^ 8 ≤ (1 + x / 8) ^ 8 := by
    refine pow_le_pow_left₀ (by norm_num) ?_ 8
    linarith
  have hnum : (131 / 100 : ℝ) < (1 + (0.27998465 : ℝ) / 8) ^ 8 := by norm_num
  linarith

/-! ## §5 — Capstone -/

/-- **★ Ch 09 quantum-enhancement numerical refutation capstone ★**

    At the chapter's stated thousand qubits the enhancement exceeds `10¹¹`, so
    it is not the claimed `1.31`; the factor is strictly increasing in the
    qubit count; and ten qubits already exceed the claim, so the qubit count
    that actually produces `1.31` is below ten rather than a thousand. -/
theorem Ch09QuantumEnhancementRefutation_capstone :
    (10 : ℝ) ^ 11 < etaEnhance 1000 ∧
    etaEnhance 1000 ≠ claimedEta ∧
    StrictMono etaEnhance ∧
    claimedEta < etaEnhance 10 :=
  ⟨etaEnhance_1000_gt_1e11,
   etaEnhance_1000_ne_claimed,
   etaEnhance_strictMono,
   claimedEta_lt_etaEnhance_ten⟩

/-! ## §6 — Non-vacuity witnesses -/

/-- Non-vacuity: the enhancement factor is strictly positive, so the bounds
    above are not bounds on zero. -/
theorem etaEnhance_pos (N : ℝ) : 0 < etaEnhance N := Real.exp_pos _

/-- Non-vacuity for `etaEnhance_strictMono`: its hypothesis is satisfiable,
    witnessed by the two qubit counts the argument above compares. -/
theorem etaEnhance_strictMono_witness : etaEnhance 10 < etaEnhance 1000 :=
  etaEnhance_strictMono (by norm_num)

end PrincipiaTractalis.Ch09Refutation

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch09Refutation.exponent_at_1000_gt_27
#print axioms PrincipiaTractalis.Ch09Refutation.etaEnhance_1000_gt_1e11
#print axioms PrincipiaTractalis.Ch09Refutation.etaEnhance_1000_ne_claimed
#print axioms PrincipiaTractalis.Ch09Refutation.etaEnhance_strictMono
#print axioms PrincipiaTractalis.Ch09Refutation.claimedEta_lt_etaEnhance_ten
#print axioms PrincipiaTractalis.Ch09Refutation.Ch09QuantumEnhancementRefutation_capstone
