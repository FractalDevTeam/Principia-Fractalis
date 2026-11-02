/-
# `19/20` Is Not A Ternary Number — The Exclusion, Machine-Checked (2026-11-02)

This module converts a sentence the corpus has been asserting in prose into a
kernel fact, and then states the limits of that fact so it cannot be misread.

## What was already there, and what was only prose

`PF/Ch2ThresholdSelection.lean:326` proves

    nineteen_twentieths_not_a_tower_value :
      (19/20 : ℝ) ≠ 2/3 ∧ ≠ 8/9 ∧ ≠ 26/27 ∧ ≠ 80/81

— four `norm_num` disequalities. Its docstring, and `ch06:679` and `ch07:817`
in the manuscript, state something far stronger: **"`20` is not a ternary
number."** That stronger sentence was never formalized. Four disequalities do
not exclude a fifth value, let alone all of them.

`PF/AlphaFromSubstrateKTheory_r123.lean` supplies the other half:
`MemZ13 x ↔ ∃ m k, x = m/3^k` is the substrate's trace range
(`τ_*(K_0(T∞)) = ℤ[1/3]`, Glimm/Elliott), and
`substrate_attains_every_Z13_trace` proves the range is attained *exactly* —
every `m/3^k` with `m ≤ 3^k` is the normalized trace of an explicit level-`k`
projection. But that file's three exclusion lemmas are `3/2`, `1/5` and
irrationals. **Nothing in the corpus connected `MemZ13` to `19/20`** — verified
by a 14-naming sweep over all 9 490 `PF/*.lean` sources, after the naming-sweep
failure logged on 2026-10-27 and the read-your-own-label failure logged on
2026-11-02. Before this file, `MemZ13` occurred in exactly five of them, all in
the α-skeleton cluster: `AlphaFromSubstrateKTheory_r123`, `AlphaLayerSeparation`,
`AlphaL5PiScalingObstruction_r332`, `AlphaStructuralLawAudit_r334`,
`AlphaStructuralLawAuditI7_r335`. None mentions `19/20`.

## What is proved here

1. **The engine** (§1). `memZ13_den_dvd`: membership forces `b ∣ a·3^k`. From
   it, `not_memZ13_of_prime_den`: any prime `p ∤ 3` dividing the denominator and
   not the numerator excludes the value. The corpus's three ad-hoc exclusions
   become instances of one lemma, and `1/2` — which
   `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md:216` asserts ("no unital qubit in
   the substrate") but which was never formalized — is now proved.

2. **The exclusion** (§2). `not_memZ13_nineteen_twentieths`, by two independent
   proofs: a parity argument in the idiom of `not_memZ13_three_halves`, and a
   second derivation through the general engine at the prime `5`. Two routes to
   one fact, because this is the sentence the manuscript has been asserting.

3. **The characterization** (§3). `memZ13_iff_exists_pow_mul_int` makes
   "exactly `ℤ[1/3]`" usable: `x ∈ ℤ[1/3] ↔ some `3^k·x` is an integer`. Every
   tower value `1 − 3^{-k}` is shown to be in the range.

4. **All levels, not four** (§4). `nineteen_twentieths_not_any_tower_value`:
   `19/20 ≠ 1 − 3^{-k}` for **every** `k`. This is the statement
   `Ch2ThresholdSelection`'s docstring makes and its theorem does not.

5. **The quantitative obstruction** (§5). The sharp separation

       |19/20 − m/3^k| ≥ 1/(20·3^k)   for every k and every integer m,

   with the constant `20` shown optimal (attained at `k = 0` and `k = 4`). This
   is the form that has content: not "the value is absent from a list" but "the
   value is a measured distance from every ternary rational at every level."

6. **And the limit of all of it** (§6). `tower_approximates_nineteen_twentieths`:
   for every `ε > 0` some level-`k` ternary value lies within `ε` of `19/20`.
   **So this module does not say the substrate cannot approach `0.95`.** It
   says `0.95` is never exactly a ternary value, and names the price of each
   finite approximation. Both directions are proved here deliberately, because
   the one-directional reading would be a new overclaim of exactly the kind
   recorded at `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md:219-220` — where
   `not_memZ13_one_fifth` was stretched into "the 5-fold icosahedral structure
   cannot live inside the substrate," which does not follow, since icosahedral
   symmetry needs a 3-dimensional representation and that exists.

## What this module does NOT claim

It does not claim `0.95` is wrong, that the substrate forbids a threshold
there, or that the consciousness threshold is refuted. It settles one question
in both directions: **`0.95` is not forced by the ternary tower, and it is not
forbidden by it either — it is simply not one of the tower's own values.** That
is consistent with, and strictly sharper than, `ch06:464`'s existing
classification of `0.95` as EMPIRICAL HYPOTHESIS — UNTESTED, and with
`ch06`'s *Settled, 2026-10-05* remark that the tower constrains the threshold
to an interval without pinning it. No claim anywhere is downgraded by this
file; one prose assertion is upgraded to a theorem.

The arithmetic is self-contained: no framework constant, no `σ_c`, no
`Phi_threshold`, no appeal to `low_rank_bound_at_sigma_c`. The only inputs are
the integer `19/20` and the powers of `3`.
-/
import PF.AlphaFromSubstrateKTheory_r123
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace Ch2ThresholdZ13

open PrincipiaTractalis.AlphaFromSubstrateKTheory

/-! ## §1 — The engine: one lemma that subsumes the corpus's three exclusions -/

/-- **Membership forces a divisibility.** If `a/b ∈ ℤ[1/3]` then `b ∣ a·3^k`
    for some `k`. Everything in §2 is a corollary. -/
theorem memZ13_den_dvd {a b : ℤ} (hb : b ≠ 0) (h : MemZ13 ((a : ℝ) / b)) :
    ∃ k : ℕ, b ∣ a * 3 ^ k := by
  obtain ⟨m, k, hmk⟩ := h
  refine ⟨k, m, ?_⟩
  have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have h3 : ((3 : ℝ)) ^ k ≠ 0 := by positivity
  rw [div_eq_div_iff hbR h3] at hmk
  have hR : (a : ℝ) * 3 ^ k = (b : ℝ) * (m : ℝ) := by linarith
  exact_mod_cast hR

/-- **The general exclusion.** If a prime `p` divides the denominator, does not
    divide the numerator, and does not divide `3`, the value is outside the
    substrate's trace range. The prime `3` is the only one the substrate sees. -/
theorem not_memZ13_of_prime_den {a b : ℤ} (hb : b ≠ 0) {p : ℤ} (hp : Prime p)
    (hp3 : ¬ p ∣ 3) (hpb : p ∣ b) (hpa : ¬ p ∣ a) : ¬ MemZ13 ((a : ℝ) / b) := by
  intro h
  obtain ⟨k, c, hc⟩ := memZ13_den_dvd hb h
  have hpd : p ∣ a * 3 ^ k := by rw [hc]; exact hpb.mul_right c
  rcases (hp.dvd_mul.mp hpd) with h1 | h2
  · exact hpa h1
  · exact hp3 (hp.dvd_of_dvd_pow h2)

/-! ## §2 — The exclusions, including the one the manuscript has been asserting -/

/-- **`19/20 ∉ ℤ[1/3]`.** The parity proof, in the idiom of
    `not_memZ13_three_halves`: `19·3^k` is odd and `20·m` is even. -/
theorem not_memZ13_nineteen_twentieths : ¬ MemZ13 (19 / 20 : ℝ) := by
  rintro ⟨m, k, hmk⟩
  have h20 : (20 : ℝ) ≠ 0 := by norm_num
  have h3 : ((3 : ℝ)) ^ k ≠ 0 := by positivity
  rw [div_eq_div_iff h20 h3] at hmk
  have hZ : (19 : ℤ) * 3 ^ k = 20 * m := by
    have hR : (19 : ℝ) * 3 ^ k = 20 * (m : ℝ) := by linarith
    exact_mod_cast hR
  have hodd : Odd ((19 : ℤ) * 3 ^ k) :=
    Odd.mul ⟨9, by norm_num⟩ (Odd.pow ⟨1, by norm_num⟩)
  rw [hZ] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) ⟨10 * m, by ring⟩

/-- The same fact through the general engine, at the prime `5`. An independent
    second route to the sentence `ch06:679` and `ch07:817` assert. -/
theorem not_memZ13_nineteen_twentieths_via_engine : ¬ MemZ13 (19 / 20 : ℝ) := by
  have hcast : (19 / 20 : ℝ) = ((19 : ℤ) : ℝ) / ((20 : ℤ) : ℝ) := by norm_num
  rw [hcast]
  exact not_memZ13_of_prime_den (by norm_num) (p := (5 : ℤ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **`1/2 ∉ ℤ[1/3]`** — no projection of trace `1/2`, hence no unital
    `M₂(ℂ) ↪ T∞`. `codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md:216` asserts this
    ("There is no unital qubit in the substrate") and calls it provable from
    `τ(p) ∈ ℤ[1/3]`; it was never formalized. It is an instance of §1. -/
theorem not_memZ13_one_half : ¬ MemZ13 (1 / 2 : ℝ) := by
  have hcast : (1 / 2 : ℝ) = ((1 : ℤ) : ℝ) / ((2 : ℤ) : ℝ) := by norm_num
  rw [hcast]
  exact not_memZ13_of_prime_den (by norm_num) (p := (2 : ℤ)) Int.prime_two
    (by norm_num) (by norm_num) (by norm_num)

/-- The corpus's `not_memZ13_three_halves` is an instance of §1 — recorded to
    show the engine subsumes it, not to replace it. -/
theorem three_halves_via_engine : ¬ MemZ13 (3 / 2 : ℝ) := by
  have hcast : (3 / 2 : ℝ) = ((3 : ℤ) : ℝ) / ((2 : ℤ) : ℝ) := by norm_num
  rw [hcast]
  exact not_memZ13_of_prime_den (by norm_num) (p := (2 : ℤ)) Int.prime_two
    (by norm_num) (by norm_num) (by norm_num)

/-- The corpus's `not_memZ13_one_fifth` is an instance of §1. -/
theorem one_fifth_via_engine : ¬ MemZ13 (1 / 5 : ℝ) := by
  have hcast : (1 / 5 : ℝ) = ((1 : ℤ) : ℝ) / ((5 : ℤ) : ℝ) := by norm_num
  rw [hcast]
  exact not_memZ13_of_prime_den (by norm_num) (p := (5 : ℤ)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-! ## §3 — "Exactly `ℤ[1/3]`", in a usable form -/

/-- **The characterization.** `x ∈ ℤ[1/3]` iff some `3^k · x` is an integer. -/
theorem memZ13_iff_exists_pow_mul_int (x : ℝ) :
    MemZ13 x ↔ ∃ (k : ℕ) (m : ℤ), (3 : ℝ) ^ k * x = (m : ℝ) := by
  constructor
  · rintro ⟨m, k, rfl⟩
    refine ⟨k, m, ?_⟩
    have h3 : ((3 : ℝ)) ^ k ≠ 0 := by positivity
    field_simp
  · rintro ⟨k, m, h⟩
    refine ⟨m, k, ?_⟩
    have h3 : ((3 : ℝ)) ^ k ≠ 0 := by positivity
    rw [← h]
    field_simp

/-- Every value the ternary tower itself distinguishes, `1 − 3^{-k}`, is in the
    substrate's trace range. The tower lives inside `ℤ[1/3]`. -/
theorem memZ13_tower_value (k : ℕ) : MemZ13 (1 - 1 / 3 ^ k) := by
  refine ⟨3 ^ k - 1, k, ?_⟩
  have h3 : ((3 : ℝ)) ^ k ≠ 0 := by positivity
  push_cast
  field_simp

/-- Every level-`k` normalized trace is in the range — the trivial direction,
    stated so §5's separation has both sides of the comparison named. -/
theorem memZ13_level_trace (k : ℕ) (m : ℤ) : MemZ13 ((m : ℝ) / 3 ^ k) :=
  ⟨m, k, rfl⟩

/-! ## §4 — All levels, not four values -/

/-- **★ `19/20` is not a tower value at ANY level. ★**

    `Ch2ThresholdSelection.nineteen_twentieths_not_a_tower_value` checks four
    values; its docstring claims this. Here it is, for every `k`. -/
theorem nineteen_twentieths_not_any_tower_value (k : ℕ) :
    (19 / 20 : ℝ) ≠ 1 - 1 / 3 ^ k := by
  intro h
  exact not_memZ13_nineteen_twentieths (h ▸ memZ13_tower_value k)

/-- **★ `19/20` is the normalized trace of no substrate level projection. ★**

    Paired with `substrate_attains_every_Z13_trace`, which proves every `m/3^k`
    with `m ≤ 3^k` *is* attained by an explicit projection, this says the
    threshold sits outside the attained range, not merely outside a listing. -/
theorem nineteen_twentieths_not_a_level_trace (k : ℕ) (m : ℤ) :
    (19 / 20 : ℝ) ≠ (m : ℝ) / 3 ^ k := by
  intro h
  exact not_memZ13_nineteen_twentieths (h ▸ memZ13_level_trace k m)

/-! ## §5 — The quantitative obstruction, with the constant shown optimal -/

/-- **★ The sharp separation. ★** Every level-`k` ternary rational misses
    `19/20` by at least `1/(20·3^k)`.

    This is the form with content. The numerator `19·3^k − 20m` is a nonzero
    integer — nonzero because `19·3^k` is odd and `20m` is even — hence at least
    `1` in absolute value, and the common denominator is `20·3^k`. -/
theorem nineteen_twentieths_level_separation (k : ℕ) (m : ℤ) :
    1 / (20 * (3 : ℝ) ^ k) ≤ |19 / 20 - (m : ℝ) / 3 ^ k| := by
  have h3pos : (0 : ℝ) < 3 ^ k := by positivity
  have hden : (0 : ℝ) < 20 * 3 ^ k := by positivity
  set N : ℤ := 19 * 3 ^ k - 20 * m with hNdef
  have hNne : N ≠ 0 := by
    intro h0
    have hZ : (19 : ℤ) * 3 ^ k = 20 * m := by omega
    have hodd : Odd ((19 : ℤ) * 3 ^ k) :=
      Odd.mul ⟨9, by norm_num⟩ (Odd.pow ⟨1, by norm_num⟩)
    rw [hZ] at hodd
    exact (Int.not_even_iff_odd.mpr hodd) ⟨10 * m, by ring⟩
  have h1 : (1 : ℤ) ≤ |N| := by
    rcases lt_trichotomy N 0 with hlt | heq | hgt
    · rw [abs_of_neg hlt]; omega
    · exact absurd heq hNne
    · rw [abs_of_pos hgt]; omega
  have hrewrite : (19 : ℝ) / 20 - (m : ℝ) / 3 ^ k = (N : ℝ) / (20 * 3 ^ k) := by
    rw [hNdef]
    push_cast
    field_simp
  rw [hrewrite, abs_div, abs_of_pos hden]
  have habs : (1 : ℝ) ≤ |(N : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  gcongr

/-- **The constant `20` is optimal.** The separation bound is attained — at
    `k = 0` by `m = 1`, and at `k = 4` by `m = 77`. So no larger constant works.

    (The minimum of `|19·3^k − 20m|` over `m` is `1` exactly when `k ≡ 0 mod 4`,
    since `19·3^k mod 20` cycles through `19, 17, 11, 13`; the bound is loose at
    the other three residues. Only the two attaining cases are asserted here.) -/
theorem separation_constant_is_optimal :
    |19 / 20 - ((1 : ℤ) : ℝ) / 3 ^ (0 : ℕ)| = 1 / (20 * (3 : ℝ) ^ (0 : ℕ)) ∧
    |19 / 20 - ((77 : ℤ) : ℝ) / 3 ^ (4 : ℕ)| = 1 / (20 * (3 : ℝ) ^ (4 : ℕ)) := by
  norm_num [abs_of_nonpos, abs_of_nonneg]

/-! ## §6 — And the limit of the obstruction, so it cannot be misread -/

/-- **★ The tower approximates `19/20` arbitrarily well. ★**

    Proved deliberately alongside §5. The exclusion is about *exactness*, never
    about reachability: `ℤ[1/3]` is dense, so no approximation obstruction
    exists and none may be claimed. Witness: `m = ⌊19·3^k/20⌋`, whose error is
    the remainder over `20·3^k`, hence below `3^{-k}`. -/
theorem tower_approximates_nineteen_twentieths (ε : ℝ) (hε : 0 < ε) :
    ∃ (k : ℕ) (m : ℤ), |19 / 20 - (m : ℝ) / 3 ^ k| < ε := by
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 : ℝ) / 3 < 1)
  have h3pos : (0 : ℝ) < 3 ^ k := by positivity
  have hden : (0 : ℝ) < 20 * 3 ^ k := by positivity
  refine ⟨k, (19 * 3 ^ k) / 20, ?_⟩
  set q : ℤ := (19 * 3 ^ k) / 20 with hq
  set r : ℤ := (19 * 3 ^ k) % 20 with hr
  have hsplit : (20 : ℤ) * q + r = 19 * 3 ^ k := by
    rw [hq, hr]; omega
  have hr0 : (0 : ℤ) ≤ r := Int.emod_nonneg _ (by norm_num)
  have hr20 : r < 20 := Int.emod_lt_of_pos _ (by norm_num)
  have hrewrite : (19 : ℝ) / 20 - (q : ℝ) / 3 ^ k = (r : ℝ) / (20 * 3 ^ k) := by
    have hZ : (19 : ℝ) * 3 ^ k - 20 * (q : ℝ) = (r : ℝ) := by
      have := hsplit
      have hR : (20 : ℝ) * (q : ℝ) + (r : ℝ) = 19 * 3 ^ k := by exact_mod_cast this
      linarith
    field_simp
    linarith [hZ]
  rw [hrewrite]
  have hrnonneg : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr0
  have hrlt : (r : ℝ) < 20 := by exact_mod_cast hr20
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r : ℝ) / (20 * 3 ^ k))]
  have hstep : (r : ℝ) / (20 * 3 ^ k) < 1 / 3 ^ k := by
    have hfac : (r : ℝ) / (20 * 3 ^ k) = ((r : ℝ) / 20) * (1 / 3 ^ k) := by
      field_simp
    have hr1 : (r : ℝ) / 20 < 1 := by
      rw [div_lt_one (by norm_num)]
      exact hrlt
    have hinv : (0 : ℝ) < 1 / 3 ^ k := by positivity
    calc (r : ℝ) / (20 * 3 ^ k) = ((r : ℝ) / 20) * (1 / 3 ^ k) := hfac
      _ < 1 * (1 / 3 ^ k) := mul_lt_mul_of_pos_right hr1 hinv
      _ = 1 / 3 ^ k := one_mul _
  have hpow : (1 : ℝ) / 3 ^ k = (1 / 3 : ℝ) ^ k := by
    rw [div_pow]; norm_num
  calc (r : ℝ) / (20 * 3 ^ k) < 1 / 3 ^ k := hstep
    _ = (1 / 3 : ℝ) ^ k := hpow
    _ < ε := hk

/-! ## §7 — The capstone -/

/-- **★ `0.95` is not a ternary number — in both directions. ★**

    Bundled, so a reader gets the whole adjudication and not half of it:

    1. every tower value and every level trace IS in the substrate's range;
    2. `19/20` is NOT;
    3. hence `19/20` is not a tower value at any level;
    4. every level-`k` ternary value misses it by at least `1/(20·3^k)`;
    5. and yet the tower approaches it arbitrarily closely.

    Together: **the ternary tower neither forces `0.95` nor forbids it.** It is
    simply not one of the tower's own values, at a measured distance from each,
    and reachable in the limit. -/
theorem nineteen_twentieths_is_not_a_ternary_number :
    (∀ k : ℕ, MemZ13 (1 - 1 / 3 ^ k)) ∧
    (∀ (k : ℕ) (m : ℤ), MemZ13 ((m : ℝ) / 3 ^ k)) ∧
    ¬ MemZ13 (19 / 20 : ℝ) ∧
    (∀ k : ℕ, (19 / 20 : ℝ) ≠ 1 - 1 / 3 ^ k) ∧
    (∀ (k : ℕ) (m : ℤ),
      1 / (20 * (3 : ℝ) ^ k) ≤ |19 / 20 - (m : ℝ) / 3 ^ k|) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (k : ℕ) (m : ℤ), |19 / 20 - (m : ℝ) / 3 ^ k| < ε) :=
  ⟨memZ13_tower_value,
   memZ13_level_trace,
   not_memZ13_nineteen_twentieths,
   nineteen_twentieths_not_any_tower_value,
   nineteen_twentieths_level_separation,
   tower_approximates_nineteen_twentieths⟩

end Ch2ThresholdZ13
end PrincipiaTractalis

/-! ## Axiom audit — LIVE, not commented out.

The bar is `[propext, Classical.choice, Quot.sound]`: a literal `[]` is
impossible for any statement mentioning `ℝ`. Zero project axioms. -/

#print axioms PrincipiaTractalis.Ch2ThresholdZ13.memZ13_den_dvd
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_of_prime_den
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_nineteen_twentieths
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_nineteen_twentieths_via_engine
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.not_memZ13_one_half
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.three_halves_via_engine
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.one_fifth_via_engine
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.memZ13_iff_exists_pow_mul_int
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.memZ13_tower_value
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.memZ13_level_trace
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.nineteen_twentieths_not_any_tower_value
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.nineteen_twentieths_not_a_level_trace
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.nineteen_twentieths_level_separation
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.separation_constant_is_optimal
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.tower_approximates_nineteen_twentieths
#print axioms PrincipiaTractalis.Ch2ThresholdZ13.nineteen_twentieths_is_not_a_ternary_number
