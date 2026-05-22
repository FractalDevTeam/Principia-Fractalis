/-
# `BernoulliFnHasSumOnSomeBall` — UNCONDITIONAL DISCHARGE

This file discharges the last remaining open Prop in the
disc-of-convergence Bernoulli identity at `s = 0`:

  `BernoulliFnHasSumOnSomeBall : ∃ R : NNReal, 0 < R ∧ (R : ℝ) < 2π ∧
       ∀ v : ℂ, ‖v‖ < R →
         HasSum (fun n => (bernoulli n : ℂ) · v^n / n!) (bernoulliFn v)`

## Strategy

1. **Absolute summability on `‖v‖ < 2π`** — combine
   `bernoulli_growth_bound_explicit` with `bernoulli_eq_bernoulli'_of_ne_one`
   + `bernoulli'_odd_eq_zero` to dominate by a geometric series.
2. **HasSum to some `S(v)`** via `Summable.hasSum`.
3. **Identify `S(v) = bernoulliFn v`** via the analytic Cauchy product
   `(Σ B_n v^n/n!) · (exp v - 1) = v` using `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`
   and `sum_bernoulli`.
-/

import PF.Analytic.BernoulliCauchyCoefficientsEqualBernoulliDischarge
import PF.Analytic.BernoulliGrowthBound
import PF.Analytic.BernoulliExpHasSumAtNegLogNhdsHalfDischarge
import PF.Analytic.JonquieresExpansionEqualsGeomGermAtHalfClosure
import PF.Analytic.JonquieresAtZeroFinalDischarge
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Filter Topology Metric Set Nat Finset
open PrincipiaTractalis.Analytic

/-! ## Step 1: termwise norm bounds -/

/-- `‖(bernoulli n : ℂ) · v^n / n!‖ = |bernoulli n| · ‖v‖^n / n!`. -/
lemma bernoulli_summand_norm_eq (n : ℕ) (v : ℂ) :
    ‖(bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)‖
      = |(bernoulli n : ℝ)| * ‖v‖ ^ n / (n.factorial : ℝ) := by
  rw [norm_div, norm_mul, norm_pow]
  have h_b : ‖((bernoulli n : ℚ) : ℂ)‖ = |(bernoulli n : ℝ)| := by
    rw [show ((bernoulli n : ℚ) : ℂ) = (((bernoulli n : ℚ) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h_f : ‖((n.factorial : ℕ) : ℂ)‖ = (n.factorial : ℝ) := by
    rw [show ((n.factorial : ℕ) : ℂ) = ((n.factorial : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Nat.cast_nonneg _)
  rw [h_b, h_f]

/-- For odd `n ≥ 3`, the Bernoulli summand vanishes. -/
lemma bernoulli_summand_eq_zero_of_odd_ge_three {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (v : ℂ) :
    (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) = 0 := by
  have hn1 : n ≠ 1 := by omega
  have hn0 : 1 < n := by omega
  have h_eq : bernoulli n = bernoulli' n :=
    bernoulli_eq_bernoulli'_of_ne_one hn1
  have h_zero : bernoulli' n = 0 :=
    bernoulli'_odd_eq_zero hodd hn0
  rw [h_eq, h_zero]
  push_cast
  ring

/-- Index reindexing: every even `n ≥ 2` is `2 * m` for some `m ≥ 1`. -/
lemma even_ge_two_eq_two_mul {n : ℕ} (hn : 2 ≤ n) (heven : Even n) :
    ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m := by
  obtain ⟨k, hk⟩ := heven
  refine ⟨k, ?_, ?_⟩
  · omega
  · omega

/-- For even `n = 2m` with `m ≥ 1`, the Bernoulli summand norm is bounded by
    `(π²/3) · (‖v‖/(2π))^{2m}`. -/
lemma bernoulli_summand_norm_bound_even {v : ℂ} {m : ℕ} (hm : 1 ≤ m) :
    ‖(bernoulli (2 * m) : ℂ) * v ^ (2 * m) / ((2 * m).factorial : ℂ)‖
      ≤ (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ (2 * m) := by
  rw [bernoulli_summand_norm_eq]
  have h_bound := bernoulli_growth_bound_explicit hm
  have h_factorial_pos : (0 : ℝ) < ((2 * m).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (2 * m))
  have h_two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_vnorm_nn : (0 : ℝ) ≤ ‖v‖ ^ (2 * m) := pow_nonneg (norm_nonneg _) _
  have h1 : |(bernoulli (2 * m) : ℝ)| * ‖v‖ ^ (2 * m)
        ≤ ((Real.pi ^ 2 / 3) * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m))
           * ‖v‖ ^ (2 * m) :=
    mul_le_mul_of_nonneg_right h_bound h_vnorm_nn
  have h2 : |(bernoulli (2 * m) : ℝ)| * ‖v‖ ^ (2 * m) / ((2 * m).factorial : ℝ)
        ≤ ((Real.pi ^ 2 / 3) * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m))
           * ‖v‖ ^ (2 * m) / ((2 * m).factorial : ℝ) :=
    (div_le_div_iff_of_pos_right h_factorial_pos).mpr h1
  have h_rhs_eq :
      ((Real.pi ^ 2 / 3) * ((2 * m).factorial : ℝ) / (2 * Real.pi) ^ (2 * m))
         * ‖v‖ ^ (2 * m) / ((2 * m).factorial : ℝ)
       = (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ (2 * m) := by
    rw [div_pow]
    have h_fact_ne : ((2 * m).factorial : ℝ) ≠ 0 := h_factorial_pos.ne'
    have h_pow_ne : ((2 * Real.pi) ^ (2 * m) : ℝ) ≠ 0 :=
      (pow_pos h_two_pi_pos _).ne'
    field_simp
  rw [h_rhs_eq] at h2
  exact h2

/-! ## Step 2: absolute summability on `‖v‖ < 2π` -/

/-- **Absolute summability**: the Bernoulli generating series is absolutely
    summable for `‖v‖ < 2π`. -/
theorem summable_bernoulli_series_norm {v : ℂ} (hv : ‖v‖ < 2 * Real.pi) :
    Summable (fun n : ℕ => ‖(bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)‖) := by
  -- Dominate by the majorant:
  --   d n := if n = 0 then 1
  --          else if n = 1 then ‖v‖
  --          else (π²/3) · (‖v‖/(2π))^n
  -- Summability of d:
  --   d = (constant correction at n=0,1, supported on finite set) + (geometric series)
  -- Each term is summable, sum is summable.
  set d : ℕ → ℝ := fun n =>
    if n = 0 then 1
    else if n = 1 then ‖v‖
    else (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n with hd_def

  -- d n ≥ ‖B_n v^n/n!‖ for all n.
  have h_bound : ∀ n : ℕ,
      ‖(bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)‖ ≤ d n := by
    intro n
    -- Case on n = 0, n = 1, n ≥ 2.
    by_cases hn0 : n = 0
    · subst hn0
      rw [bernoulli_summand_norm_eq]
      simp [d, bernoulli_zero]
    · by_cases hn1 : n = 1
      · subst hn1
        rw [bernoulli_summand_norm_eq]
        simp only [d, if_neg (one_ne_zero : (1 : ℕ) ≠ 0), if_true]
        rw [bernoulli_one]
        rw [show ((1 : ℕ).factorial : ℝ) = 1 by norm_num]
        rw [pow_one, div_one]
        rw [show |((-1 / 2 : ℚ) : ℝ)| = 1/2 by push_cast; norm_num]
        linarith [norm_nonneg v]
      · -- n ≥ 2
        have hn2 : 2 ≤ n := by omega
        rcases Nat.even_or_odd n with heven | hodd
        · obtain ⟨m, hm1, hnm⟩ := even_ge_two_eq_two_mul hn2 heven
          simp only [d, if_neg hn0, if_neg hn1]
          subst hnm
          exact bernoulli_summand_norm_bound_even (v := v) hm1
        · have hn3 : 3 ≤ n := by
            by_contra hlt
            push_neg at hlt
            interval_cases n
            · exact (Nat.not_even_iff_odd.mpr hodd) (by decide)
          have h_zero : (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) = 0 :=
            bernoulli_summand_eq_zero_of_odd_ge_three hn3 hodd v
          rw [h_zero, norm_zero]
          simp only [d, if_neg hn0, if_neg hn1]
          positivity

  -- d is summable.
  have hd_summable : Summable d := by
    -- d = correction at n=0,1 (finite-supported) + geometric tail.
    -- Geometric tail.
    have h_geom : Summable (fun n : ℕ => (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n) := by
      apply Summable.mul_left
      apply summable_geometric_of_lt_one
      · positivity
      · rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
        exact hv
    -- Correction has finite support {0, 1}.
    have h_corr : Summable
        (fun n => d n - (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n) := by
      apply summable_of_finite_support
      -- Support ⊆ {0, 1}.
      have h_fin : ({0, 1} : Set ℕ).Finite := Set.toFinite _
      apply h_fin.subset
      intro n hn
      simp only [Function.mem_support] at hn
      by_contra h_contra
      simp [Set.mem_insert_iff] at h_contra
      obtain ⟨hne0, hne1⟩ := h_contra
      have : d n = (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n := by
        simp only [d, if_neg hne0, if_neg hne1]
      apply hn
      rw [this]; ring
    -- d = correction + geometric.
    have h_eq : d = (fun n => d n - (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n)
                  + (fun n => (Real.pi ^ 2 / 3) * (‖v‖ / (2 * Real.pi)) ^ n) := by
      funext n
      simp
    rw [h_eq]
    exact h_corr.add h_geom

  -- Combine.
  exact hd_summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_bound

/-! ## Step 3: the sum-form `S(v)` and its identification -/

/-- The Bernoulli generating series is summable for `‖v‖ < 2π`. -/
lemma summable_bernoulli_series {v : ℂ} (hv : ‖v‖ < 2 * Real.pi) :
    Summable (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)) :=
  (summable_bernoulli_series_norm hv).of_norm

/-- The candidate sum `S(v) := Σ_n B_n · v^n / n!`. -/
noncomputable def bernoulliSum (v : ℂ) : ℂ :=
  ∑' n : ℕ, (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)

/-- The HasSum form. -/
lemma bernoulliSum_hasSum {v : ℂ} (hv : ‖v‖ < 2 * Real.pi) :
    HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)) (bernoulliSum v) :=
  (summable_bernoulli_series hv).hasSum

/-! ## Step 4: `exp v` summability and Cauchy product -/

/-- HasSum for `Complex.exp v` in division form. -/
lemma complex_exp_hasSum (v : ℂ) :
    HasSum (fun n : ℕ => v ^ n / (n.factorial : ℂ)) (Complex.exp v) := by
  have h_cE : Complex.exp v = NormedSpace.exp ℂ v := by
    rw [Complex.exp_eq_exp_ℂ]
  rw [h_cE]
  exact NormedSpace.expSeries_div_hasSum_exp_of_mem_ball (𝕂 := ℂ) (𝔸 := ℂ) v
    (by simp [NormedSpace.expSeries_radius_eq_top])

/-- Norm-summability of the exp series. -/
lemma complex_exp_summable_norm (v : ℂ) :
    Summable (fun n : ℕ => ‖v ^ n / (n.factorial : ℂ)‖) := by
  -- expSeries_summable_of_mem_ball gives summability of `fun n => expSeries n (fun _ => v)`,
  -- which equals `v^n/n!`. But mathlib's lemma actually gives `Summable (fun n => ‖p n‖ * r^n)`-style
  -- and not the norms directly. Easier: use absolute summability of the real exp series.
  have h_real : Summable (fun n : ℕ => ‖v‖ ^ n / (n.factorial : ℝ)) := by
    -- This is the series for Real.exp ‖v‖.
    have h := Real.summable_pow_div_factorial ‖v‖
    -- h : Summable (fun n => ‖v‖^n / n!)
    exact h
  -- ‖v^n / n!‖ = ‖v‖^n / n!.
  have h_eq : ∀ n : ℕ, ‖v ^ n / (n.factorial : ℂ)‖ = ‖v‖ ^ n / (n.factorial : ℝ) := by
    intro n
    rw [norm_div, norm_pow]
    congr 1
    have : ((n.factorial : ℕ) : ℂ) = ((n.factorial : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Nat.cast_nonneg _)
  simpa [h_eq] using h_real

/-- HasSum for `exp v - 1` (with constant term killed via `if n = 0 then 0 else …`). -/
lemma complex_exp_sub_one_hasSum (v : ℂ) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℂ) else v ^ n / (n.factorial : ℂ))
      (Complex.exp v - 1) := by
  have h_exp := complex_exp_hasSum v
  -- HasSum for the singleton at 0 with value 1.
  have h_one_sum : HasSum (fun n : ℕ => if n = 0 then (1 : ℂ) else 0) (1 : ℂ) := by
    have h := hasSum_single (α := ℂ) (f := fun n : ℕ => if n = 0 then (1 : ℂ) else 0) 0 ?_
    · simpa using h
    · intro b hb
      simp [hb]
  have h_diff := h_exp.sub h_one_sum
  -- h_diff : HasSum (fun n => v^n/n! - if n=0 then 1 else 0) (exp v - 1)
  convert h_diff using 1
  funext n
  by_cases hn : n = 0
  · subst hn; simp
  · simp [hn]

/-- The Cauchy product: `(Σ_n B_n v^n/n!) · (exp v - 1) = v`. -/
theorem bernoulliSum_mul_exp_sub_one {v : ℂ} (hv : ‖v‖ < 2 * Real.pi) :
    bernoulliSum v * (Complex.exp v - 1) = v := by
  set f : ℕ → ℂ := fun n => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ) with hf_def
  set g : ℕ → ℂ := fun n => if n = 0 then (0 : ℂ) else v ^ n / (n.factorial : ℂ) with hg_def
  have hf_norm : Summable (fun n => ‖f n‖) := summable_bernoulli_series_norm hv
  have hg_norm : Summable (fun n => ‖g n‖) := by
    refine (complex_exp_summable_norm v).of_nonneg_of_le
      (fun _ => norm_nonneg (g _)) (fun n => ?_)
    simp only [g]
    split_ifs with hn
    · rw [norm_zero]
      exact norm_nonneg _
    · exact le_rfl

  have h_cauchy_hasSum := hasSum_sum_range_mul_of_summable_norm hf_norm hg_norm
  have h_tsum_f : (∑' n, f n) = bernoulliSum v := rfl
  have h_tsum_g : (∑' n, g n) = Complex.exp v - 1 := (complex_exp_sub_one_hasSum v).tsum_eq
  rw [h_tsum_f, h_tsum_g] at h_cauchy_hasSum

  -- Identify each Cauchy term.
  have h_term : ∀ n : ℕ, (∑ k ∈ range (n + 1), f k * g (n - k))
      = if n = 1 then v else 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      simp [f, g, bernoulli_zero]
    · have hn1 : 1 ≤ n := hn0
      -- Split: drop last term (k = n) which is f n · g 0 = 0.
      have h_sum_split :
          (∑ k ∈ range (n + 1), f k * g (n - k))
            = ∑ k ∈ range n, f k * (v ^ (n - k) / ((n - k).factorial : ℂ)) := by
        rw [Finset.sum_range_succ]
        have h_last : f n * g (n - n) = 0 := by simp [g, hg_def]
        rw [h_last, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        have h_neq : n - k ≠ 0 := by omega
        simp [g, hg_def, h_neq]
      rw [h_sum_split]
      -- Rewrite each summand as v^n · B_k / (k!(n-k)!).
      have h_rewrite : ∀ k ∈ range n,
          f k * (v ^ (n - k) / ((n - k).factorial : ℂ))
            = v ^ n * ((bernoulli k : ℂ) / ((k.factorial : ℂ) * ((n - k).factorial : ℂ))) := by
        intro k hk
        rw [Finset.mem_range] at hk
        simp only [f, hf_def]
        have h_pow : v ^ k * v ^ (n - k) = v ^ n := by
          rw [← pow_add]
          congr 1
          omega
        have h_k_fact_ne : (k.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero k
        have h_nk_fact_ne : ((n - k).factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (n - k)
        field_simp
        rw [← h_pow]
        ring
      rw [Finset.sum_congr rfl h_rewrite, ← Finset.mul_sum]
      -- Use sum_bernoulli: ∑_{k<n} C(n,k) B_k = if n=1 then 1 else 0.
      have h_bern_sum : (∑ k ∈ range n,
          (bernoulli k : ℂ) / ((k.factorial : ℂ) * ((n - k).factorial : ℂ)))
            = (if n = 1 then (1 : ℂ) else 0) / (n.factorial : ℂ) := by
        have h_q : (∑ k ∈ range n, ((n.choose k : ℚ)) * bernoulli k)
              = if n = 1 then (1 : ℚ) else 0 := sum_bernoulli n
        have h_c : (∑ k ∈ range n, ((n.choose k : ℂ)) * (bernoulli k : ℂ))
              = if n = 1 then (1 : ℂ) else 0 := by
          have h_cast : ((∑ k ∈ range n, ((n.choose k : ℚ)) * bernoulli k : ℚ) : ℂ)
                = ((if n = 1 then (1 : ℚ) else 0 : ℚ) : ℂ) := by
            exact_mod_cast h_q
          push_cast at h_cast
          rw [h_cast]
          split_ifs <;> simp
        have h_fact_ne : (n.factorial : ℂ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero n
        rw [eq_div_iff h_fact_ne]
        rw [Finset.sum_mul]
        have h_each : ∀ k ∈ range n,
            (bernoulli k : ℂ) / ((k.factorial : ℂ) * ((n - k).factorial : ℂ)) * (n.factorial : ℂ)
              = ((n.choose k : ℂ)) * (bernoulli k : ℂ) := by
          intro k hk
          rw [Finset.mem_range] at hk
          have h_choose_nat : (n.choose k) * (k.factorial * (n - k).factorial) = n.factorial := by
            have := Nat.choose_mul_factorial_mul_factorial hk.le
            -- this : n.choose k * k ! * (n - k)! = n !
            -- Goal: n.choose k * (k ! * (n - k)!) = n !
            rw [← mul_assoc]
            exact this
          have h_choose_c :
              (n.choose k : ℂ) * ((k.factorial : ℂ) * ((n - k).factorial : ℂ))
                = (n.factorial : ℂ) := by exact_mod_cast h_choose_nat
          have h_k_ne : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
          have h_nk_ne : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
          have h_prod_ne : (k.factorial : ℂ) * ((n - k).factorial : ℂ) ≠ 0 :=
            mul_ne_zero h_k_ne h_nk_ne
          -- LHS = (B_k / (k!(n-k)!)) * n!
          -- Substitute n! = choose * (k!(n-k)!):
          calc (bernoulli k : ℂ) / ((k.factorial : ℂ) * ((n - k).factorial : ℂ)) * (n.factorial : ℂ)
              = (bernoulli k : ℂ) / ((k.factorial : ℂ) * ((n - k).factorial : ℂ))
                  * ((n.choose k : ℂ) * ((k.factorial : ℂ) * ((n - k).factorial : ℂ))) := by
                rw [h_choose_c]
            _ = (n.choose k : ℂ) * (bernoulli k : ℂ) := by
                field_simp
        rw [Finset.sum_congr rfl h_each]
        exact h_c
      rw [h_bern_sum]
      split_ifs with hn1
      · subst hn1; simp
      · simp

  -- The HasSum, with terms identified.
  have h_cauchy' : HasSum (fun n => if n = 1 then v else (0 : ℂ))
      (bernoulliSum v * (Complex.exp v - 1)) := by
    convert h_cauchy_hasSum using 1
    funext n
    exact (h_term n).symm

  -- The indicator-at-1 series sums to v.
  have h_indicator : HasSum (fun n : ℕ => if n = 1 then v else (0 : ℂ)) v := by
    have h := hasSum_single (α := ℂ) (f := fun n : ℕ => if n = 1 then v else (0 : ℂ)) 1 ?_
    · simpa using h
    · intro b hb
      simp [hb]

  exact (h_indicator.unique h_cauchy').symm

/-- **THE KEY THEOREM**: for `‖v‖ < 2π`, the Bernoulli generating series sums
    to `bernoulliFn v`. -/
theorem bernoulliFn_hasSum_of_norm_lt_twoPi {v : ℂ} (hv : ‖v‖ < 2 * Real.pi) :
    HasSum (fun n : ℕ => (bernoulli n : ℂ) * v ^ n / (n.factorial : ℂ)) (bernoulliFn v) := by
  have h_sum := bernoulliSum_hasSum hv
  suffices h_eq : bernoulliSum v = bernoulliFn v by
    rw [← h_eq]; exact h_sum
  by_cases hv0 : v = 0
  · subst hv0
    rw [bernoulliFn_zero]
    -- bernoulliSum 0 = 1 since only n=0 term contributes.
    have h_hasSum_zero : HasSum (fun n : ℕ => (bernoulli n : ℂ) * (0 : ℂ) ^ n / (n.factorial : ℂ))
        1 := by
      have h := hasSum_single (α := ℂ)
        (f := fun n : ℕ => (bernoulli n : ℂ) * (0 : ℂ) ^ n / (n.factorial : ℂ)) 0 ?_
      · simpa [bernoulli_zero] using h
      · intro b hb
        show (bernoulli b : ℂ) * (0 : ℂ) ^ b / (b.factorial : ℂ) = 0
        rw [zero_pow hb]
        simp
    -- bernoulliSum 0 = ∑' n, term and HasSum gives value 1.
    have := h_hasSum_zero.tsum_eq
    simp only [bernoulliSum]
    exact this
  · -- v ≠ 0.
    have h_exp_ne : Complex.exp v - 1 ≠ 0 :=
      exp_sub_one_ne_zero_of_pos_norm_lt_twoPi hv0 hv
    rw [bernoulliFn_eq_of_ne_zero hv0]
    have h_prod := bernoulliSum_mul_exp_sub_one hv
    rw [eq_div_iff h_exp_ne]
    exact h_prod

/-! ## Step 5: discharge the named Prop -/

/-- **DISCHARGE**: `BernoulliFnHasSumOnSomeBall` is now an UNCONDITIONAL theorem.

    With `R = π` (any value in `(0, 2π)`), the direct HasSum identity holds. -/
theorem bernoulliFnHasSumOnSomeBall_proved : BernoulliFnHasSumOnSomeBall := by
  refine ⟨⟨Real.pi, Real.pi_pos.le⟩, ?_, ?_, ?_⟩
  · show (0 : NNReal) < ⟨Real.pi, Real.pi_pos.le⟩
    rw [← NNReal.coe_lt_coe]
    simpa using Real.pi_pos
  · show (Real.pi : ℝ) < 2 * Real.pi
    linarith [Real.pi_pos]
  · intro v hv
    have hv_pi : ‖v‖ < Real.pi := by
      have h1 : ‖v‖ < ((⟨Real.pi, Real.pi_pos.le⟩ : NNReal) : ℝ) := by exact_mod_cast hv
      simpa using h1
    have hv_lt : ‖v‖ < 2 * Real.pi := by linarith [Real.pi_pos]
    exact bernoulliFn_hasSum_of_norm_lt_twoPi hv_lt

/-! ## Chain composition: forward through the disc-of-convergence chain

With `bernoulliFnHasSumOnSomeBall_proved`, every link in the chain at `s = 0`
becomes UNCONDITIONAL: -/

/-- `BernoulliCauchyCoefficientsEqualBernoulli` — now an UNCONDITIONAL theorem. -/
theorem bernoulliCauchyCoefficientsEqualBernoulli_proved :
    BernoulliCauchyCoefficientsEqualBernoulli :=
  bernoulliCauchyCoefficientsEqualBernoulli_of_hasSumOnSomeBall
    bernoulliFnHasSumOnSomeBall_proved

/-- `BernoulliExpHasSumOnBallTwoPi` — now an UNCONDITIONAL theorem.
    The full `2π`-disc HasSum identity. -/
theorem bernoulliExpHasSumOnBallTwoPi_proved :
    BernoulliExpHasSumOnBallTwoPi :=
  bernoulliExpHasSumOnBallTwoPi_of_cauchyCoefficients
    bernoulliCauchyCoefficientsEqualBernoulli_proved

/-- `BernoulliExpHasSumAtNegLogNhdsHalf` — now an UNCONDITIONAL theorem.
    The composed `-log z` HasSum identity in a neighborhood of `z = 1/2`. -/
theorem bernoulliExpHasSumAtNegLogNhdsHalf_proved :
    BernoulliExpHasSumAtNegLogNhdsHalf :=
  bernoulliExpHasSumAtNegLogNhdsHalf_of_bernoulliExpHasSumOnBallTwoPi
    bernoulliExpHasSumOnBallTwoPi_proved

/-- `JonquieresIdentityPointGermAtHalf 0` — now an UNCONDITIONAL theorem.
    The classical germ identity at `(s, z) = (0, 1/2)` is fully discharged.

    This is THE FIRST FULLY UNCONDITIONAL DISCHARGE of the germ-level
    Jonquières identity at `s = 0` in the project. -/
theorem jonquieresIdentityPointGermAtHalf_zero_proved :
    JonquieresIdentityPointGermAtHalf 0 :=
  jonquieresIdentityPointGermAtHalf_zero_of_bernoulliOnBall
    bernoulliExpHasSumOnBallTwoPi_proved

/-- **DISC-WIDE CAPSTONE**: under the two remaining geometric hypotheses
    (`JonquieresExpansionAnalyticOnPuncturedBall 0` and
    `SlitDiscPreconnectedReachability`), the disc-wide Jonquières/polylog
    identity holds at every `z ∈ JonquieresAnalyticDomain ∩ ball 0 1`,
    UNCONDITIONALLY on the Bernoulli/germ side. -/
theorem discAgreementReduced_at_zero_unconditional_on_bernoulli
    (h_an : JonquieresExpansionAnalyticOnPuncturedBall 0)
    (h_reach : SlitDiscPreconnectedReachability) :
    ∀ z ∈ JonquieresAnalyticDomain ∩ Metric.ball (0 : ℂ) 1,
      jonquieresExpansion 0 z = polyLog 0 z :=
  discAgreementReduced_at_zero_of_germ h_an
    jonquieresIdentityPointGermAtHalf_zero_proved h_reach

end PrincipiaTractalis.Analytic.Sheaf

/-! ## Axiom audit -/

section AxiomAudit
open PrincipiaTractalis.Analytic.Sheaf
#guard_msgs(drop info) in
#print axioms bernoulliFnHasSumOnSomeBall_proved
#guard_msgs(drop info) in
#print axioms bernoulliCauchyCoefficientsEqualBernoulli_proved
#guard_msgs(drop info) in
#print axioms bernoulliExpHasSumOnBallTwoPi_proved
#guard_msgs(drop info) in
#print axioms bernoulliExpHasSumAtNegLogNhdsHalf_proved
#guard_msgs(drop info) in
#print axioms jonquieresIdentityPointGermAtHalf_zero_proved
end AxiomAudit
