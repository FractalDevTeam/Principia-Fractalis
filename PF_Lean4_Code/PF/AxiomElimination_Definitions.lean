/-
# AXIOM ELIMINATION: Converting Definitional Axioms to Proper Constructions

These "axioms" are actually DEFINITIONS or CONSTRUCTIONS that should be built
from first principles, not assumed.

Author: Pablo Cohen
Date: November 16, 2025

CRITICAL: These are NOT true axioms - they're lazily axiomatized definitions!
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import PF.Basic
-- `tapeProd_injective` (the content of `encodeConfig_tape_eq`) was proved on
-- 2026-11-22 for the verbatim mirrors of `TMConfig`/`encodeConfig`.  Cited here
-- rather than re-proved, per that file's own instruction.
import PF.Referee.EncodeConfigTapeInjective_2026_11_22

namespace PrincipiaTractalis.AxiomElimination

open Nat (nth)

-- ============================================================================
-- COMPUTATIONAL AXIOMS (for bounds that require complex number theory)
-- These are mathematical facts that hold but require extensive machinery to prove
-- ============================================================================

-- Removed three unused axioms (2026-04-22):
--
-- * prime_bound: n ≥ 6 → nth Prime n ≤ n * (log₂ n + log₂ log₂ n). Classical
--   PNT-adjacent bound. Never referenced as a term, only mentioned in a
--   comment (line ~290 below). If needed, mathlib's `Nat.nth_prime_le_*`
--   family is probably the right entry point.
--
-- * log_conversion: Real.log x ≤ (log₂ ⌊x⌋ + 1) * Real.log 2. Never referenced
--   as a term, only mentioned in a comment (line ~333).
--
-- * empty_tape_bound: ∀ s h, Real.log (2^s * 3^h) ≤ 100 * Real.log 2 * 0.
--   RHS is identically 0, so this claims log(2^s * 3^h) ≤ 0 for all s,h —
--   FALSE (e.g. s=1, h=0 gives log 2 > 0). Never referenced. Removed as a
--   dead, mathematically inconsistent assumption.

-- ============================================================================
-- SECTION 1: Natural Logarithm for Natural Numbers
-- ============================================================================

/-- Natural logarithm for naturals (base b of n)
    REPLACES: axiom nat_log

    This computes ⌊log_b(n)⌋, the number of digits needed to represent n in base b.
-/
def nat_log (b : ℕ) (n : ℕ) : ℕ :=
  if b > 1 ∧ n > 0 then
    Nat.log b n  -- Use Mathlib's implementation if available
  else
    0

/-- On a positive argument with a base `> 1`, `nat_log` is just `Nat.log`. -/
theorem nat_log_eq_natLog {b n : ℕ} (hb : 1 < b) (hn : 0 < n) :
    nat_log b n = Nat.log b n := by
  unfold nat_log
  simp [hb, hn]

/-- Properties of nat_log can be PROVEN, not axiomatized -/
theorem nat_log_monotone (b n m : ℕ) (hb : b > 1) (hnm : n ≤ m) :
  nat_log b n ≤ nat_log b m := by
  unfold nat_log
  by_cases hn : n > 0
  · by_cases hm : m > 0
    · simp [hb, hn, hm]
      apply Nat.log_mono_right hnm
    · omega  -- n > 0 but m = 0 contradicts n ≤ m
  · simp [hn]  -- n = 0, so nat_log b n = 0

-- ============================================================================
-- SECTION 2: Turing Machine Configuration Encoding
-- ============================================================================

/-- Turing machine configuration -/
structure TMConfig where
  state : ℕ
  head : ℕ
  tape : List (Fin 2)

/-- Prime encoding of TM configurations
    CONSTRUCTS the encoding function, doesn't assume it exists!

    encode(q, h, T) = 2^q · 3^h · ∏(p_i^{t_i})
    where p_i is the i-th prime and t_i is the i-th tape symbol
-/
noncomputable def encodeConfig (c : TMConfig) : ℕ :=
  2^(c.state) * 3^(c.head) *
  (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod
  -- Note: nth Prime selects the nth prime number (0-indexed)

/-- THEOREM: Encoding preserves state information
    REPLACES: axiom encodeConfig_state_eq

    This is PROVABLE from the definition of encodeConfig!
-/
theorem encodeConfig_state_eq (c₁ c₂ : TMConfig) :
  encodeConfig c₁ = encodeConfig c₂ → c₁.head = c₂.head → c₁.tape = c₂.tape →
  c₁.state = c₂.state := by
  intro h_enc _ _
  -- Extract state using p-adic valuation base 2
  have extract : ∀ c : TMConfig, padicValNat 2 (encodeConfig c) = c.state := by
    intro c
    haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    -- `encodeConfig` uses `nth Prime`, i.e. `_root_.Prime`, not `Nat.Prime`.
    have hinf : {p : ℕ | Prime p}.Infinite := by
      simpa [Nat.prime_iff] using Nat.infinite_setOf_prime
    have hprime : ∀ j : ℕ, Nat.Prime (nth Prime (j + 2)) := fun j =>
      Nat.prime_iff.mpr (Nat.nth_mem_of_infinite hinf (j + 2))
    unfold encodeConfig
    have h2 : (2 : ℕ) ^ c.state ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : (3 : ℕ) ^ c.head ≠ 0 := pow_ne_zero _ (by norm_num)
    have hprod_pos : 0 < (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := by
      apply List.prod_pos
      intro x hx
      obtain ⟨j, sym, _, rfl⟩ := List.mem_mapIdx.mp hx
      exact Nat.pow_pos (hprime j).pos
    have hP : (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod ≠ 0 := hprod_pos.ne'
    -- every tape prime is p_{j+2}, hence strictly above the first 0 prime(s),
    -- so it is coprime to 2
    have hcop : Nat.Coprime 2 (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro n hn
      obtain ⟨j, sym, _, rfl⟩ := List.mem_mapIdx.mp hn
      refine Nat.Coprime.pow_right _ ?_
      refine (Nat.coprime_primes (by norm_num) (hprime j)).mpr ?_
      have hp0 : Nat.Prime (nth Prime 0) := Nat.prime_iff.mpr
        (Nat.nth_mem_of_infinite hinf 0)
      have h0 : 2 ≤ nth Prime 0 := hp0.two_le
      have hmj : nth Prime 0 < nth Prime (j + 2) :=
        (Nat.nth_lt_nth hinf).mpr (by omega)
      omega
    have hnd : ¬ (2 : ℕ) ∣ (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hcop
    rw [padicValNat.mul (mul_ne_zero h2 h3) hP, padicValNat.mul h2 h3]
    have vOther : padicValNat 2 ((3 : ℕ) ^ c.head) = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hdvd
      have := Nat.Prime.dvd_of_dvd_pow (p := 2) (by norm_num) hdvd
      omega
    have vP : padicValNat 2 (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod = 0 :=
      padicValNat.eq_zero_of_not_dvd hnd
    rw [padicValNat.prime_pow, vOther, vP]
    simp

  calc c₁.state = padicValNat 2 (encodeConfig c₁) := (extract c₁).symm
    _ = padicValNat 2 (encodeConfig c₂) := by rw [h_enc]
    _ = c₂.state := extract c₂

/-- THEOREM: Encoding preserves head position
    REPLACES: axiom encodeConfig_head_eq

    Provable from unique prime factorization!
-/
theorem encodeConfig_head_eq (c₁ c₂ : TMConfig) :
  encodeConfig c₁ = encodeConfig c₂ → c₁.state = c₂.state → c₁.tape = c₂.tape →
  c₁.head = c₂.head := by
  intro h_enc _ _
  -- Extract head using p-adic valuation base 3
  have extract : ∀ c : TMConfig, padicValNat 3 (encodeConfig c) = c.head := by
    intro c
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    -- `encodeConfig` uses `nth Prime`, i.e. `_root_.Prime`, not `Nat.Prime`.
    have hinf : {p : ℕ | Prime p}.Infinite := by
      simpa [Nat.prime_iff] using Nat.infinite_setOf_prime
    have hprime : ∀ j : ℕ, Nat.Prime (nth Prime (j + 2)) := fun j =>
      Nat.prime_iff.mpr (Nat.nth_mem_of_infinite hinf (j + 2))
    unfold encodeConfig
    have h2 : (2 : ℕ) ^ c.state ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : (3 : ℕ) ^ c.head ≠ 0 := pow_ne_zero _ (by norm_num)
    have hprod_pos : 0 < (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := by
      apply List.prod_pos
      intro x hx
      obtain ⟨j, sym, _, rfl⟩ := List.mem_mapIdx.mp hx
      exact Nat.pow_pos (hprime j).pos
    have hP : (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod ≠ 0 := hprod_pos.ne'
    -- every tape prime is p_{j+2}, hence strictly above the first 1 prime(s),
    -- so it is coprime to 3
    have hcop : Nat.Coprime 3 (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro n hn
      obtain ⟨j, sym, _, rfl⟩ := List.mem_mapIdx.mp hn
      refine Nat.Coprime.pow_right _ ?_
      refine (Nat.coprime_primes (by norm_num) (hprime j)).mpr ?_
      have hp0 : Nat.Prime (nth Prime 0) := Nat.prime_iff.mpr
        (Nat.nth_mem_of_infinite hinf 0)
      have h0 : 2 ≤ nth Prime 0 := hp0.two_le
      have hm0 : nth Prime 0 < nth Prime 1 :=
        (Nat.nth_lt_nth hinf).mpr (by omega)
      have hmj : nth Prime 1 < nth Prime (j + 2) :=
        (Nat.nth_lt_nth hinf).mpr (by omega)
      omega
    have hnd : ¬ (3 : ℕ) ∣ (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mp hcop
    rw [padicValNat.mul (mul_ne_zero h2 h3) hP, padicValNat.mul h2 h3]
    have vOther : padicValNat 3 ((2 : ℕ) ^ c.state) = 0 := by
      refine padicValNat.eq_zero_of_not_dvd ?_
      intro hdvd
      have := Nat.Prime.dvd_of_dvd_pow (p := 3) (by norm_num) hdvd
      omega
    have vP : padicValNat 3 (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod = 0 :=
      padicValNat.eq_zero_of_not_dvd hnd
    rw [vOther, padicValNat.prime_pow, vP]
    simp

  calc c₁.head = padicValNat 3 (encodeConfig c₁) := (extract c₁).symm
    _ = padicValNat 3 (encodeConfig c₂) := by rw [h_enc]
    _ = c₂.head := extract c₂

/-- `encodeConfig` uses `nth Prime` with `_root_.Prime`; the proved
    injectivity lemma is stated with `Nat.nth Nat.Prime`.  The two predicates
    agree on `ℕ` (`Nat.prime_iff`), so the enumerations are literally equal. -/
theorem nth_prime_eq_nth_natPrime (k : ℕ) : nth Prime k = Nat.nth Nat.Prime k := by
  have hpred : (Prime : ℕ → Prop) = Nat.Prime := by
    funext p
    exact propext Nat.prime_iff.symm
  rw [hpred]

/-- THEOREM: Encoding preserves tape contents
    REPLACES: axiom encodeConfig_tape_eq

    Follows from unique prime factorization.

    **2026-11-22.** The proof here previously ended in the tactic
    `by_decidability_instances`, which is declared nowhere in this repository
    or in mathlib, so this theorem was never proved.  The statement is TRUE and
    the proof now runs: the tape product determines the tape, because the
    factorisation of `∏_{i<n} p_{i+2}^(t_i+1)` reads back `t_k + 1` at
    `p_{k+2}` for `k < n` and `0` beyond the end, which pins the length and
    then every entry.

    That argument is `tapeProd_injective` in
    `PF/Referee/EncodeConfigTapeInjective_2026_11_22.lean`, proved on the
    verbatim mirrors of `TMConfig` and `encodeConfig`.  It is cited rather than
    re-proved, exactly as that file instructs. -/
theorem encodeConfig_tape_eq (c₁ c₂ : TMConfig) :
  encodeConfig c₁ = encodeConfig c₂ → c₁.state = c₂.state → c₁.head = c₂.head →
  c₁.tape = c₂.tape := by
  intro h_enc h_state h_head
  -- Since state and head are equal, the tape product parts must be equal
  unfold encodeConfig at h_enc
  rw [h_state, h_head] at h_enc

  -- Cancel the common factors 2^state and 3^head
  have h2_pos : 0 < 2^c₂.state := Nat.pow_pos (by norm_num)
  have h3_pos : 0 < 3^c₂.head := Nat.pow_pos (by norm_num)

  -- The products must be equal
  have prod_eq : (c₁.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod =
                 (c₂.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := by
    have : 2^c₂.state * 3^c₂.head * (c₁.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod =
           2^c₂.state * 3^c₂.head * (c₂.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod := h_enc
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos h2_pos h3_pos) this

  -- Move to the `Nat.nth Nat.Prime` spelling the injectivity lemma uses, then
  -- read the tape back off the factorisation of the product.
  simp only [nth_prime_eq_nth_natPrime] at prod_eq
  refine PF.Referee.AxiomEliminationDefinitionsRefutation.tapeProd_injective ?_
  rw [← PF.Referee.AxiomEliminationDefinitionsRefutation.tapeProd_eq_mapIdx,
      ← PF.Referee.AxiomEliminationDefinitionsRefutation.tapeProd_eq_mapIdx]
  exact prod_eq

-- ============================================================================
-- SECTION 3: Sizing the encoding — the facts the two bounds below rest on
--
-- 2026-11-22.  The two theorems that followed here were FALSE as stated, and
-- are refuted in the kernel at the configuration `⟨1, 0, []⟩` by
-- `PF/Referee/AxiomEliminationDefinitionsRefutation_2026_11_22.lean`
-- (`polynomial_time_claim_is_false`, `growth_bound_claim_is_false`).
--
-- WHY they were false, in one line: both put a `tape.length` FACTOR on the
-- right, so both right-hand sides vanish on an empty tape while the left-hand
-- sides do not — the encoding still carries `2 ^ state`.  The state and head
-- contributions are ADDITIVE, not multiplicative in the tape length, and
-- `Real.log 1 = 0` makes the second one fail on every length-one tape too.
--
-- This section proves the sizing facts outright, uniformly and
-- unconditionally, and the two theorems are then restated with exactly the
-- hypotheses that make them true.  Nothing is deleted and no statement is
-- weakened to fit a proof: the originals had no content to preserve.
-- ============================================================================

/-- The tape factor of the encoding, named so it can be sized on its own. -/
noncomputable def encodeTapeProd (c : TMConfig) : ℕ :=
  (c.tape.mapIdx (fun j sym => (nth Prime (j + 2))^(sym.val + 1))).prod

theorem encodeConfig_eq (c : TMConfig) :
    encodeConfig c = 2 ^ c.state * 3 ^ c.head * encodeTapeProd c := rfl

theorem encodeTapeProd_pos (c : TMConfig) : 0 < encodeTapeProd c := by
  have hinf : {p : ℕ | Prime p}.Infinite := by
    simpa [Nat.prime_iff] using Nat.infinite_setOf_prime
  unfold encodeTapeProd
  apply List.prod_pos
  intro x hx
  obtain ⟨j, sym, _, rfl⟩ := List.mem_mapIdx.mp hx
  exact Nat.pow_pos (Nat.prime_iff.mpr (Nat.nth_mem_of_infinite hinf (j + 2))).pos

theorem encodeConfig_pos (c : TMConfig) : 0 < encodeConfig c := by
  rw [encodeConfig_eq]
  exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by norm_num))
    (Nat.pow_pos (by norm_num))) (encodeTapeProd_pos c)

/-- Sub-additivity of `Nat.log` over a product.  Mathlib `v4.24.0-rc1` carries
    `log_mul_base`, `log_mono_right`, `pow_log_le_self` and `log_lt_of_lt_pow`,
    but no sub-additivity lemma; it follows in three lines from the last two. -/
theorem natLog_two_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have h1 : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have h2 : b < 2 ^ (Nat.log 2 b + 1) := Nat.lt_pow_succ_log_self (by norm_num) b
  have hlt : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
          Nat.mul_lt_mul_of_lt_of_lt h1 h2
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
          rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero ha hb) hlt
  omega

/-- `log₂ (3 ^ h) ≤ 2 h`, since `3 ^ h ≤ 4 ^ h = 2 ^ (2h)`. -/
theorem natLog_two_three_pow_le (h : ℕ) : Nat.log 2 (3 ^ h) ≤ 2 * h := by
  calc Nat.log 2 (3 ^ h) ≤ Nat.log 2 (4 ^ h) :=
        Nat.log_mono_right (Nat.pow_le_pow_left (by norm_num) h)
    _ = Nat.log 2 (2 ^ (2 * h)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    _ = 2 * h := Nat.log_pow (by norm_num) _

/-- **The uniform, unconditional upper bound.**  The state and head
    contributions are ADDITIVE; only the tape product is left unsized.  This is
    the correct shape of the bound the two false theorems were reaching for. -/
theorem encodeConfig_natLog_le (c : TMConfig) :
    nat_log 2 (encodeConfig c)
      ≤ c.state + 2 * c.head + nat_log 2 (encodeTapeProd c) + 2 := by
  have hT : encodeTapeProd c ≠ 0 := (encodeTapeProd_pos c).ne'
  have h2 : (2 : ℕ) ^ c.state ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (3 : ℕ) ^ c.head ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [nat_log_eq_natLog (by norm_num) (encodeConfig_pos c),
      nat_log_eq_natLog (by norm_num) (encodeTapeProd_pos c), encodeConfig_eq]
  have step1 := natLog_two_mul_le (Nat.mul_ne_zero h2 h3) hT
  have step2 := natLog_two_mul_le h2 h3
  have hq : Nat.log 2 ((2 : ℕ) ^ c.state) = c.state := Nat.log_pow (by norm_num) _
  have hh : Nat.log 2 ((3 : ℕ) ^ c.head) ≤ 2 * c.head := natLog_two_three_pow_le _
  omega

/-- **The lower bound that refutes the old shape.**  `c.state` bounds the
    encoding's bit-length from below for EVERY configuration, the empty tape
    included — which is precisely where both discarded upper bounds put `0` on
    the right. -/
theorem state_le_natLog_encodeConfig (c : TMConfig) :
    c.state ≤ nat_log 2 (encodeConfig c) := by
  rw [nat_log_eq_natLog (by norm_num) (encodeConfig_pos c), encodeConfig_eq]
  calc c.state = Nat.log 2 (2 ^ c.state) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 2 (2 ^ c.state * 3 ^ c.head * encodeTapeProd c) := by
        refine Nat.log_mono_right ?_
        calc (2 : ℕ) ^ c.state = 2 ^ c.state * 1 * 1 := by ring
          _ ≤ 2 ^ c.state * 3 ^ c.head * encodeTapeProd c := by
              gcongr
              · exact Nat.one_le_pow _ _ (by norm_num)
              · exact encodeTapeProd_pos c

/-- **The exact real-logarithm decomposition.**  `Real.log` is additive on
    products of positive reals, so there is nothing to estimate here at all:
    the encoding's size splits exactly into a state term, a head term and a
    tape term.  This identity is what shows the discarded growth bound had the
    wrong shape — no `tape.length` factor multiplies the first two terms. -/
theorem encodeConfig_realLog_eq (c : TMConfig) :
    Real.log (encodeConfig c : ℝ)
      = c.state * Real.log 2 + c.head * Real.log 3
          + Real.log (encodeTapeProd c : ℝ) := by
  have hT : (0 : ℝ) < (encodeTapeProd c : ℝ) := by
    exact_mod_cast encodeTapeProd_pos c
  rw [encodeConfig_eq]
  push_cast
  -- the two `log_mul` splits plus `log_pow` land exactly on the right-hand
  -- side; no further normalisation is needed (a trailing `ring` here errors
  -- with "No goals to be solved")
  rw [Real.log_mul (by positivity) (ne_of_gt hT),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]

-- ============================================================================
-- SECTION 4: the two bounds, restated with the hypotheses that make them true
-- ============================================================================

/-- THEOREM: Encoding is polynomial-time computable
    REPLACES: axiom encodeConfig_polynomial_time

    **CONDITIONAL RESTATEMENT (2026-11-22).**  The unconditional form of this
    statement is FALSE and is refuted in the kernel at `⟨1, 0, []⟩`
    (`polynomial_time_claim_is_false`).  Here it is, with the two hypotheses
    that are exactly what the original proof's comments asserted without proof:

    * `hTape` — the tape product fits in `n log₂ n` bits.  This is the
      prime-size estimate ("the k-th prime is bounded by `k (ln k + ln ln k)`
      for `k ≥ 6`") that the original file appealed to in a comment and never
      formalised.  It is NOT available from mathlib at this pin: mathlib
      `v4.24.0-rc1` has only the LOWER bound `Nat.add_two_le_nth_prime` and
      carries no upper bound on `nth Prime` anywhere.
    * `hSmall` — the state and head contributions also fit.  Without it the
      claim is false outright, since `state` and `head` are unconstrained
      naturals that no function of the tape length can bound.

    The witness `k = 2` is produced explicitly and does NOT depend on `c`, so
    this is a genuine uniform bound under its hypotheses, not an existential
    dodge that picks `k` large after seeing the configuration. -/
theorem encodeConfig_polynomial_time (c : TMConfig)
    (hTape : nat_log 2 (encodeTapeProd c)
      ≤ c.tape.length * nat_log 2 c.tape.length)
    (hSmall : c.state + 2 * c.head + 2
      ≤ c.tape.length * nat_log 2 c.tape.length) :
  ∃ k : ℕ, ∀ n : ℕ, n = c.tape.length →
  nat_log 2 (encodeConfig c) ≤ n * nat_log 2 n * k := by
  refine ⟨2, ?_⟩
  intro n hn
  subst hn
  have hmain := encodeConfig_natLog_le c
  omega

/-- THEOREM: Encoding growth bound
    REPLACES: axiom encodeConfig_growth_bound

    **CONDITIONAL RESTATEMENT (2026-11-22).**  The unconditional form is FALSE
    and is refuted in the kernel at `⟨1, 0, []⟩`
    (`growth_bound_claim_is_false`); because `Real.log 1 = 0` it also fails on
    every length-one tape with a nonzero state, so it is not a lone edge case
    at the empty tape.

    Over `ℝ` there is nothing to estimate about the state and head terms at
    all — `encodeConfig_realLog_eq` splits the encoding's logarithm EXACTLY
    into `state·log 2 + head·log 3 + log(tape product)`.  The two hypotheses
    below are therefore precisely the two things the false statement silently
    assumed, with no slack hidden anywhere:

    * `hTape` — the tape product's logarithm fits in `n log n`;
    * `hSmall` — the state and head terms fit in `n log n`.

    `C = 2` is explicit and independent of `c`. -/
theorem encodeConfig_growth_bound (c : TMConfig)
    (hTape : Real.log (encodeTapeProd c : ℝ)
      ≤ (c.tape.length : ℝ) * Real.log (c.tape.length : ℝ))
    (hSmall : (c.state : ℝ) * Real.log 2 + (c.head : ℝ) * Real.log 3
      ≤ (c.tape.length : ℝ) * Real.log (c.tape.length : ℝ)) :
  ∃ C : ℝ, C > 0 ∧
  Real.log (encodeConfig c : ℝ) ≤ C * c.tape.length * Real.log c.tape.length := by
  refine ⟨2, by norm_num, ?_⟩
  rw [encodeConfig_realLog_eq]
  nlinarith [hTape, hSmall]

-- ============================================================================
-- SECTION 5: how much the two conditional restatements in SECTION 4 cover
--
-- 2026-11-23, measured in this kernel.  The hypotheses added in SECTION 4 are
-- SUFFICIENT -- both theorems are true, both sit on the three-axiom bar -- but
-- they are also very nearly unsatisfiable, so neither restatement yet carries
-- the complexity content the original (false) statements were reaching for.
-- That is recorded here in the kernel rather than in a comment, following the
-- disclosure pattern of
-- `PF/Referee/ToECapstoneVacuityDisclosure_2026_11_22.lean`.
-- Nothing in SECTION 4 is weakened, renamed or removed.
--
-- WHAT IS MEASURED.  `Nat.log 2` of the SMALLEST possible tape product (every
-- symbol 0, so every exponent 1) against the `hTape` right-hand side
-- `n * nat_log 2 n`, where `n` is the tape length:
--
--       n     log2(tape product)     n * log2 n     hTape
--       0                      0              0     holds
--       1                      2              0     FAILS
--       2                      5              2     FAILS
--       4                     12              8     FAILS
--       8                     30             24     FAILS
--      16                     74             64     FAILS
--      64                    430            384     FAILS
--    1024                  11605          10240     FAILS
--    4096                  55769          49152     FAILS
--
-- The gap WIDENS.  Summing over the first `n` primes from `p_2`,
-- `log2 (prod p_(j+2)) = n*log2 n + n*(ln ln n - 1)/ln 2 + O(n)`; the second
-- term is positive and growing from `n = 16` on, while `Nat.log`'s floor only
-- shrinks the right-hand side.  So `hTape` is satisfiable at `n = 0` and
-- (numerically) at no other length -- and `hSmall` is IMPOSSIBLE at `n = 0`.
-- Both halves of that are proved below.
--
-- CONSEQUENCE.  `encodeConfig_polynomial_time` is vacuously true: its two
-- hypotheses cannot hold together.  `encodeConfig_growth_bound` is satisfiable
-- at exactly one configuration, `<0, 0, []>`, where its conclusion reads
-- `0 <= 0`.  Note which configuration that is: the refutation witness for the
-- ORIGINAL unconditional claims is `<1, 0, []>`
-- (`PF/Referee/AxiomEliminationDefinitionsRefutation_2026_11_22.lean`), one
-- state apart.
--
-- REMOVAL CONDITION -- what would make SECTION 4 carry content, in order:
--
--   (a) An UPPER bound on `Nat.nth Nat.Prime`.  mathlib `v4.24.0-rc1` has
--       none; the only directional fact is the LOWER bound
--       `Nat.add_two_le_nth_prime`.  Bertrand
--       (`Nat.exists_prime_lt_and_le_two_mul`) gives `p_(k+1) <= 2 * p_k`,
--       hence `nth Prime k <= 2 ^ (k+1)` by induction.  That sizes the tape
--       product at `2 ^ (n^2 + 5n)`, i.e. `O(n^2)` bits -- enough to justify
--       the word "polynomial", NOT enough for the `n log n` shape asserted.
--
--   (b) For the `n log n` shape: a Chebyshev-type upper bound
--       `nth Prime k = O(k log k)` (equivalently `theta(x) >> x`).  This is
--       the real outstanding formalisation, and it is what the deleted
--       `prime_bound` axiom used to assert without proof.
--
--   (c) A Turing-faithful `TMConfig`.  `state` and `head` are unconstrained
--       `Nat` fields here, so no function of `tape.length` alone can bound the
--       `2 ^ state` factor -- that is exactly what
--       `state_le_natLog_encodeConfig` shows.  A faithful configuration
--       carries `head <= tape.length` as an invariant.
--
-- (b) and (c) together, and only together, let the CONCLUSIONS of SECTION 4 be
-- asserted unconditionally.  Until then the content of this file is the four
-- unconditional sizing theorems of SECTION 3.
-- ============================================================================

/-- `nat_log b 0 = 0`, straight from the definition (the `n > 0` guard fails). -/
theorem nat_log_zero_arg (b : ℕ) : nat_log b 0 = 0 := by
  unfold nat_log; simp

/-- `nat_log b 1 = 0`, since `Nat.log b 1 = 0`. -/
theorem nat_log_one_arg (b : ℕ) : nat_log b 1 = 0 := by
  unfold nat_log; simp

/-- **Coverage fact 1.**  `hSmall` of `encodeConfig_polynomial_time` forces the
tape to have length at least 2 — for every state and every head position.  In
particular it excludes the refutation witness `⟨1, 0, []⟩` of the original
unconditional claim, and every empty or one-cell tape. -/
theorem conditional_hSmall_forces_two_le_length (c : TMConfig)
    (hSmall : c.state + 2 * c.head + 2
      ≤ c.tape.length * nat_log 2 c.tape.length) :
    2 ≤ c.tape.length := by
  by_contra hlt
  have h : c.tape.length = 0 ∨ c.tape.length = 1 := by omega
  rcases h with h0 | h1
  · rw [h0, nat_log_zero_arg] at hSmall; omega
  · rw [h1, nat_log_one_arg] at hSmall; omega

/-- **Coverage fact 2.**  Length `0` is where `hTape` of
`encodeConfig_polynomial_time` does hold: the tape product is `1`, so both
sides are `0`.  Together with coverage fact 1 — which makes `hSmall`
impossible at exactly that length — the two hypotheses never hold together on
any length where `hTape` is satisfiable. -/
theorem conditional_hTape_holds_at_empty_tape (s h : ℕ) :
    nat_log 2 (encodeTapeProd ⟨s, h, []⟩)
      ≤ (TMConfig.mk s h []).tape.length
          * nat_log 2 (TMConfig.mk s h []).tape.length := by
  have hz : encodeTapeProd ⟨s, h, []⟩ = 1 := by unfold encodeTapeProd; simp
  rw [hz, nat_log_one_arg]
  simp

/-- The one configuration at which the REAL-valued restatement's hypotheses
hold. -/
def cfgTrivial : TMConfig := ⟨0, 0, []⟩

theorem encodeTapeProd_cfgTrivial : encodeTapeProd cfgTrivial = 1 := by
  unfold encodeTapeProd cfgTrivial; simp

/-- **Coverage fact 3.**  `encodeConfig_growth_bound` is not vacuous: its two
hypotheses are satisfied at `⟨0, 0, []⟩`.  They are satisfied there and
(numerically, see the table above) nowhere else, and there its conclusion reads
`0 ≤ 0`. -/
theorem conditional_growth_hyps_hold_at_cfgTrivial :
    Real.log (encodeTapeProd cfgTrivial : ℝ)
        ≤ (cfgTrivial.tape.length : ℝ) * Real.log (cfgTrivial.tape.length : ℝ)
      ∧ (cfgTrivial.state : ℝ) * Real.log 2 + (cfgTrivial.head : ℝ) * Real.log 3
        ≤ (cfgTrivial.tape.length : ℝ)
            * Real.log (cfgTrivial.tape.length : ℝ) := by
  constructor
  · rw [encodeTapeProd_cfgTrivial]
    simp [cfgTrivial]
  · simp [cfgTrivial]

/-- **Coverage fact 4.**  The NAT-valued restatement is not satisfiable there
either, so the two restatements do not even share a witness. -/
theorem conditional_nat_hyps_fail_at_cfgTrivial :
    ¬ (cfgTrivial.state + 2 * cfgTrivial.head + 2
        ≤ cfgTrivial.tape.length * nat_log 2 cfgTrivial.tape.length) := by
  intro h
  have := conditional_hSmall_forces_two_le_length cfgTrivial h
  simp [cfgTrivial] at this

/-- **The coverage disclosure, bundled.**  Read together: the nat restatement's
hypotheses exclude every tape of length `≤ 1` while its `hTape` half is only
ever satisfiable at length `0`, so that theorem is vacuous; the real
restatement's hypotheses hold at `⟨0, 0, []⟩`, where its conclusion is
`0 ≤ 0`. -/
theorem conditional_restatements_coverage_disclosed :
    (∀ c : TMConfig,
        c.state + 2 * c.head + 2 ≤ c.tape.length * nat_log 2 c.tape.length →
        2 ≤ c.tape.length)
      ∧ (∀ s h : ℕ, nat_log 2 (encodeTapeProd ⟨s, h, []⟩)
            ≤ (TMConfig.mk s h []).tape.length
                * nat_log 2 (TMConfig.mk s h []).tape.length)
      ∧ ¬ (cfgTrivial.state + 2 * cfgTrivial.head + 2
            ≤ cfgTrivial.tape.length * nat_log 2 cfgTrivial.tape.length) :=
  ⟨conditional_hSmall_forces_two_le_length,
   conditional_hTape_holds_at_empty_tape,
   conditional_nat_hyps_fail_at_cfgTrivial⟩


-- ============================================================================
-- VERIFICATION
-- ============================================================================

/-
ELIMINATED "AXIOMS" (Now Definitions/Theorems):

1. nat_log → DEFINITION (constructed)
2. encodeConfig_state_eq → THEOREM (proved: 2-adic valuation)
3. encodeConfig_head_eq → THEOREM (proved: 3-adic valuation)
4. encodeConfig_tape_eq → THEOREM (proved 2026-11-22 via `tapeProd_injective`;
   the proof formerly ended in the nonexistent tactic
   `by_decidability_instances`)
5. encodeConfig_polynomial_time → THEOREM, **CONDITIONAL** (the unconditional
   form is FALSE; see below)
6. encodeConfig_growth_bound → THEOREM, **CONDITIONAL** (the unconditional
   form is FALSE; see below)

These were NEVER true axioms - just lazy placeholders for constructions!

STATUS OF THE TWO BOUNDS (2026-11-22)
-------------------------------------
Items 5 and 6 were asserted unconditionally and are FALSE in that form.  Both
are refuted in the kernel at the configuration `⟨1, 0, []⟩` by
`PF/Referee/AxiomEliminationDefinitionsRefutation_2026_11_22.lean`.  The cause
is structural, not an edge case: both right-hand sides carry a `tape.length`
FACTOR, so both vanish on an empty tape, while `encodeConfig c` always retains
the factor `2 ^ c.state` (see `state_le_natLog_encodeConfig` above).

They are now stated with the hypotheses that make them true, and those
hypotheses are not decoration — each one names a fact the original proof
asserted in a comment:

* the tape-product size bound IS the prime-size estimate ("the k-th prime is
  bounded by `k (ln k + ln ln k)` for `k ≥ 6`") that the deleted `prime_bound`
  axiom used to carry.  It is NOT derivable from mathlib at this pin: mathlib
  `v4.24.0-rc1` contains an upper bound on `nth Prime` NOWHERE.  The only
  directional fact it has is `Nat.add_two_le_nth_prime`, a LOWER bound, and
  `Mathlib/NumberTheory/Bertrand.lean` gives only
  `exists_prime_lt_and_le_two_mul`.  Deriving `nth Prime k < 2 ^ (k+1)` from
  Bertrand by induction, and then the `O(k log k)` form from Chebyshev, is the
  outstanding formalisation work;
* the state/head bound is genuinely needed: `state` and `head` are
  unconstrained fields of `TMConfig`, so no function of `tape.length` alone can
  bound them.  A Turing-machine-faithful `TMConfig` would carry
  `head ≤ tape.length` as an invariant; this one does not.

WHAT IS NOW PROVED OUTRIGHT, with no hypotheses:
* `encodeConfig_natLog_le` — the uniform additive upper bound
  `log₂(enc) ≤ state + 2·head + log₂(tape product) + 2`;
* `state_le_natLog_encodeConfig` — the lower bound that refutes the old shape;
* `encodeConfig_realLog_eq` — the EXACT real-logarithm decomposition
  `log(enc) = state·log 2 + head·log 3 + log(tape product)`;
* `natLog_two_mul_le` — sub-additivity of `Nat.log` over products, which
  mathlib `v4.24.0-rc1` does not carry.
-/

end PrincipiaTractalis.AxiomElimination
