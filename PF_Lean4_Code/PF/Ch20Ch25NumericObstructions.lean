/-
# Ch 20 and Ch 25 — Numeric and Counting Obstructions (2026-10-05)

Four independent defects, two per chapter, each checkable from the text alone.

## ch20 — Defect A: the scaling formula does not produce its own table

`ch20_riemann_hypothesis.tex:344–350` boxes, as Theorem "Empirical Scaling":

  `s = 10 / (π |λ| α*)`,  `α* = 5 × 10⁻⁶`

and adds "This correspondence is verified at 150-digit precision." The
"High-Precision Verification" block at `:368–373` then displays, verbatim:

```
eigenvalue = 0.143333957275062618978826534396...
alpha = 5e-6
s_predicted = 10 / (pi * eigenvalue * alpha)
# Result: 14.226730417712656...
```

**That computation does not return that result.** With those inputs the
expression exceeds `4.4 × 10⁶` (`formula_output_exceeds_million`), so it is
larger than the printed `14.2267…` by a factor near `3.12 × 10⁵`. The same
factor recurs on every row of the Primary Correspondences table (`:352–363`):

| eigenvalue | printed `t` | formula gives | ratio |
|---|---|---|---|
| `0.14333` | `14.226` | `4 441 636.6` | `312 220` |
| `0.14589` | `13.978` | `4 363 697.1` | `312 183` |
| `0.06955` | `29.321` | `9 153 411.5` | `312 179` |

Agreement of the ratio to four or five significant figures across three
independent rows rules out a one-off typo: the discrepancy is systematic. The
printed `α*` would have to be about `1.561` rather than `5 × 10⁻⁶` to produce
the tabulated values (`required_alpha_bracket`) — a factor of `3.12 × 10⁵`,
the same one.

The quoted `t`-values are themselves used correctly downstream: the chapter's
`|ζ(1/2 + 14.226730417712656 i)| = 0.0735102061930…` is right, and the table's
Distance column (`0.092`, `0.157`, `1.104`) is consistent with the printed `t`
against the true zeros. So the numbers were obtained *somehow*; it is the
displayed derivation that cannot be their source, and "verified at 150-digit
precision" describes a code block that does not compute what it prints.

A minor, separate slip in the same table: `30.425` is labelled "(3rd)". The
third nontrivial zero is `25.0108575…`; `30.4248761…` is the **fourth**.

## ch20 — Defect B: the same section says 9 and 10 for the same object

Section `:470` is titled "…reproduces the full **9-class** α-skeleton", and
`:499`, `:492`, `:642` all speak of "the same **9-tuple**". But `:483` of the
same section says "The **10 canonical** α-skeleton values emerge", enumerates
exactly ten — `α_P, α_NP, α_QG, α_Poincaré, α_HN, α_Hodge, α_YM, α_NS, α_BSD,
α_RH` — and `:489` scores them "3/10, 7/10, 10/10".

**The arithmetic settles which count the experiment used.** The printed total
error is `Δ_Σ = 0.0059`. Summing the ten printed per-class deviations gives
`0.005924`, which rounds to `0.0059`; summing the nine, with `α_HN` removed,
gives `0.005704`, which rounds to `0.0057` (`delta_sigma_matches_ten_not_nine`).
Every tier count also reproduces on ten and not on nine: at the `10⁻³` tier
seven of ten qualify, but only six of nine once `α_HN` is dropped
(`tier_counts_are_ten_based`).

So the run tested ten values, `α_HN = 5` among them, and the "9-class" /
"9-tuple" language is what disagrees with it. This matters because `α_HN` is a
later addition — `PF/CrossMillenniumSharedInvariants.lean` carries nine
α-instances and `PF/AlphaHNPillar_r232.lean` introduces `α_HN = 5` as "the
tenth canonical pillar" — so the section is silently mixing the canonical
nine-tuple with a ten-value experiment and scoring against the larger set while
describing the smaller.

Either reading is repairable, but they give different headline numbers: `3/10,
7/10, 10/10` with `Δ_Σ = 0.0059`, or `3/9, 6/9, 9/9` with `Δ_Σ = 0.0057`.
Which set is the corroboration target is an authorial item.

## ch25 — Defect C: "22 divisors" on a K3 surface is impossible

`ch25_hodge_conjecture.tex:512` tabulates, for a K3 surface, "Cycles Found:
**22 divisors**".

A complex K3 has `b₂ = 22` with Hodge decomposition
`h^{2,0}, h^{1,1}, h^{0,2} = 1, 20, 1` (`k3_betti_decomposition`). By the
chapter's own `def:hodge-class` (`:135–143`) a Hodge class must be rational
*and* of pure type `(p,p)`, so the two-dimensional `H^{2,0} ⊕ H^{0,2}` summand
can contain none. Divisor classes therefore live in `H^{1,1} ∩ H²(X,ℚ)` and the
Picard number satisfies `ρ ≤ h^{1,1} = 20` — attained, but never exceeded.
`22 > 20`, so twenty-two independent divisor classes cannot exist
(`k3_twentytwo_exceeds_picard_bound`).

The chapter contradicts itself about this ten lines later, at `:522`,
describing "K3 surface with `ρ = 20`". And the Lean corpus already carries the
bound: `PF/HodgeK3Dim2Substrate.lean:172` has
`picard_le_twenty : picard_number ≤ 20`, with `b₂ = 22` recorded at `:195`. So
the table violates the chapter's own prose *and* a formalised corpus result.

## ch25 — Defect D: "240 cycles" on an abelian fourfold

`:514` tabulates "Abelian 4-fold … **240 cycles**" with no codimension given.
For a complex abelian variety of dimension `4`, `h^{p,q} = C(4,p)·C(4,q)`, so
the Hodge classes live in the `h^{p,p} = C(4,p)²` pieces, of dimensions
`1, 16, 36, 16, 1` — a total of `70` across **every** codimension
(`abelian_fourfold_total_hodge_dimension`). `240 > 70`, so `240` cannot count
independent classes. It may count dependent cycle representatives, but the text
does not say, and no variety, codimension, or counting convention is specified.

## ch25 — the threshold identity, for the record

`:351–361` states as a Theorem `σ_c = 6/π² + ε_quantum = 0.6079… + 0.3421… =
0.95`, glossing `ε_quantum` as "quantum corrections from the
discrete-continuous transition". `6/π² = 0.60792710…`, so
`ε_quantum = 0.95 − 6/π²` exactly, bracketed in
`(0.3420, 0.3421)` by `epsilon_quantum_is_the_remainder`: it is defined as
whatever reaches a pre-chosen `0.95`, and nothing independently derives either
it or the target. This is **not a new diagnosis** — the same
identity appears at `ch26_cosmological_constant.tex:323` and ch26's own
verification-status section already labels it "ASSERTED (numerology)". The
finding is that ch25's verification-status section (`:614–624`) does not carry
ch26's caveat for its own copy.

## Scope

Arithmetic and counting only. The Hodge-theoretic inputs — the K3 Hodge
numbers, the abelian-variety Hodge numbers, and the fact that Hodge classes are
of pure type `(p,p)` — are standard and are used here as **stated hypotheses**,
not proved; they are not formalized in this file. No rigor-ledger label outside
the cited sites moves, and nothing here bears on the Riemann Hypothesis or the
Hodge Conjecture.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch20Ch25Numerics

/-! ## §1 — ch20 Defect A: the scaling formula -/

/-- The boxed formula of `ch20:347`. -/
noncomputable def scalingFormula (lam alpha : ℝ) : ℝ := 10 / (Real.pi * lam * alpha)

/-- The eigenvalue as tabulated at `ch20:358`. -/
noncomputable def lambda_table : ℝ := 14333 / 100000

/-- The scaling factor the theorem fixes, `5 × 10⁻⁶`. -/
noncomputable def alpha_star : ℝ := 5 / 10 ^ 6

/-- The value the verification block prints, `14.226730417712656`. -/
noncomputable def printed_t : ℝ := 14226730417712656 / 10 ^ 15

/-- **★ The formula's output exceeds a million. ★**

    With the chapter's own `λ` and `α*` the expression is larger than `10⁶`,
    not `14.2267…`. -/
theorem formula_output_exceeds_million :
    (10 : ℝ) ^ 6 < scalingFormula lambda_table alpha_star := by
  have hpi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold scalingFormula lambda_table alpha_star
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [hpi, hpos]

/-- The printed value is below a million, so it is not the formula's output. -/
theorem printed_t_below_million : printed_t < (10 : ℝ) ^ 6 := by
  unfold printed_t; norm_num

/-- **★ The displayed computation does not return the displayed result. ★** -/
theorem formula_output_ne_printed :
    scalingFormula lambda_table alpha_star ≠ printed_t := by
  intro h
  have h1 := formula_output_exceeds_million
  have h2 := printed_t_below_million
  rw [h] at h1
  linarith

/-- What `α` the printed value would require: close to `1.561`, not
    `5 × 10⁻⁶`. The ratio between them is the same `3.12 × 10⁵` seen on every
    row of the table. -/
theorem required_alpha_bracket :
    (156 / 100 : ℝ) < 10 / (Real.pi * lambda_table * printed_t) ∧
    10 / (Real.pi * lambda_table * printed_t) < (157 / 100 : ℝ) := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  unfold lambda_table printed_t
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith [hlo, hhi]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [hlo, hhi]

/-- The `30.425` entry is the **fourth** nontrivial zero, not the third:
    the third is `25.0108…`, recorded here as the separating inequality. -/
theorem zero_index_mislabelled :
    (250108 / 10000 : ℝ) < (304248 / 10000 : ℝ) ∧
    (250108 / 10000 : ℝ) ≠ (304248 / 10000 : ℝ) := by
  constructor <;> norm_num

/-! ## §2 — ch20 Defect B: nine versus ten -/

/-- The ten printed per-class deviations of `ch20:485–487`, in units of
    `10⁻⁶`. -/
def deviations : List ℕ := [43, 44, 77, 200, 220, 230, 910, 1100, 1400, 1700]

/-- `α_HN`'s contribution, the tenth pillar. -/
def deviation_HN : ℕ := 220

/-- **★ The printed `Δ_Σ` matches the ten-value sum, not the nine. ★**

    `0.005924` rounds to the printed `0.0059`; `0.005704` rounds to `0.0057`.
    So the run tested ten classes and the "9-tuple" language disagrees with
    it. -/
theorem delta_sigma_matches_ten_not_nine :
    deviations.sum = 5924 ∧
    deviations.sum - deviation_HN = 5704 ∧
    |(5924 / 10 ^ 6 : ℝ) - 59 / 10 ^ 4| < 5 / 10 ^ 5 ∧
    ¬ |(5704 / 10 ^ 6 : ℝ) - 59 / 10 ^ 4| < 5 / 10 ^ 5 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rw [abs_lt]; constructor <;> norm_num
  · rw [not_lt, le_abs]; right; norm_num

/-- The printed tier scores reproduce on ten and not on nine: at the `10⁻³`
    tier seven of ten qualify, but only six of the nine once `α_HN` is
    dropped. -/
theorem tier_counts_are_ten_based :
    (deviations.filter (· ≤ 100)).length = 3 ∧
    (deviations.filter (· ≤ 1000)).length = 7 ∧
    (deviations.filter (· ≤ 10000)).length = 10 ∧
    ((deviations.erase deviation_HN).filter (· ≤ 1000)).length = 6 ∧
    ((deviations.erase deviation_HN).filter (· ≤ 10000)).length = 9 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## §3 — ch25 Defect C: the K3 Picard bound -/

/-- `b₂(K3) = 22` splits as `1 + 20 + 1` across `h^{2,0}, h^{1,1}, h^{0,2}`. -/
theorem k3_betti_decomposition : 1 + 20 + 1 = 22 := by decide

/-- **★ Twenty-two divisor classes exceed the K3 Picard bound. ★**

    Hodge classes in `H²` are of pure type `(1,1)`, so `ρ ≤ h^{1,1} = 20`; the
    remaining two dimensions of `b₂` carry none. The corpus already records the
    bound at `PF/HodgeK3Dim2Substrate.lean:172`. -/
theorem k3_twentytwo_exceeds_picard_bound :
    20 < 22 ∧ ∀ rho : ℕ, rho ≤ 20 → rho ≠ 22 := by
  refine ⟨by decide, ?_⟩
  intro rho h; omega

/-- The two dimensions unavailable to Hodge classes are exactly the gap between
    the chapter's table entry and its own `ρ = 20`. -/
theorem k3_gap_is_the_non_pp_part : 22 - 20 = 1 + 1 := by decide

/-! ## §4 — ch25 Defect D: the abelian fourfold count -/

/-- `h^{p,p} = C(4,p)²` for a complex abelian fourfold: `1, 16, 36, 16, 1`. -/
def abelianFourfoldHodgeDims : List ℕ :=
  [Nat.choose 4 0 ^ 2, Nat.choose 4 1 ^ 2, Nat.choose 4 2 ^ 2,
   Nat.choose 4 3 ^ 2, Nat.choose 4 4 ^ 2]

/-- **★ Seventy Hodge classes at most, across every codimension. ★**

    So the tabulated `240` cannot be a count of independent classes. -/
theorem abelian_fourfold_total_hodge_dimension :
    abelianFourfoldHodgeDims = [1, 16, 36, 16, 1] ∧
    abelianFourfoldHodgeDims.sum = 70 ∧
    70 < 240 := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## §5 — ch25: the threshold identity -/

/-- **`ε_quantum` is defined as the remainder reaching a pre-chosen `0.95`.**

    `6/π² = 0.6079271…`, and the chapter's `0.3421` is exactly `0.95 − 6/π²`.
    Nothing independently derives either it or the target. -/
theorem epsilon_quantum_is_the_remainder :
    (3420 / 10000 : ℝ) < 95 / 100 - 6 / Real.pi ^ 2 ∧
    95 / 100 - 6 / Real.pi ^ 2 < (3421 / 10000 : ℝ) := by
  have hlo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have hhi : Real.pi < 3.141593 := Real.pi_lt_d6
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (0 : ℝ) < Real.pi ^ 2 := by positivity
  -- pi^2 = 9.8696044..., bracketed with room to spare
  have hb1 : (9.8690 : ℝ) < Real.pi ^ 2 := by nlinarith [hlo, hpos]
  have hb2 : Real.pi ^ 2 < (9.8697 : ℝ) := by nlinarith [hhi, hpos]
  -- hence 6/pi^2 sits strictly between 0.6079 and 0.6080
  have key1 : 6 / Real.pi ^ 2 < 6080 / 10000 := by
    rw [div_lt_iff₀ hsq]; nlinarith [hb1]
  have key2 : (6079 / 10000 : ℝ) < 6 / Real.pi ^ 2 := by
    rw [lt_div_iff₀ hsq]; nlinarith [hb2]
  constructor <;> linarith

/-! ## §6 — Capstone -/

/-- **★ Ch 20 / Ch 25 numeric obstruction capstone ★**

    ch20's boxed formula returns something above `10⁶` where the chapter prints
    `14.2267`; its `Δ_Σ` identifies the tested set as ten, not the nine its
    prose names; ch25's K3 entry exceeds the Picard bound its own prose states;
    and its abelian-fourfold entry exceeds the total available Hodge
    dimension. -/
theorem Ch20Ch25Numerics_capstone :
    (10 : ℝ) ^ 6 < scalingFormula lambda_table alpha_star ∧
    scalingFormula lambda_table alpha_star ≠ printed_t ∧
    deviations.sum = 5924 ∧
    (20 < 22 ∧ ∀ rho : ℕ, rho ≤ 20 → rho ≠ 22) ∧
    abelianFourfoldHodgeDims.sum = 70 :=
  ⟨formula_output_exceeds_million,
   formula_output_ne_printed,
   delta_sigma_matches_ten_not_nine.1,
   k3_twentytwo_exceeds_picard_bound,
   (abelian_fourfold_total_hodge_dimension.2).1⟩

/-! ## §7 — Non-vacuity -/

/-- Non-vacuity: the quantities compared are genuine positive reals, and the
    Picard bound is attainable — `ρ = 20` is permitted, so the obstruction is
    specifically to `22` and not to the whole claim shape. -/
theorem bounds_are_attainable :
    0 < scalingFormula lambda_table alpha_star ∧
    (20 : ℕ) ≤ 20 ∧
    (∃ rho : ℕ, rho ≤ 20 ∧ rho = 20) := by
  refine ⟨?_, le_refl _, ⟨20, le_refl _, rfl⟩⟩
  have h := formula_output_exceeds_million
  have : (0:ℝ) < 10 ^ 6 := by norm_num
  linarith

end PrincipiaTractalis.Ch20Ch25Numerics

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch20Ch25Numerics.formula_output_exceeds_million
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.printed_t_below_million
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.k3_betti_decomposition
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.k3_gap_is_the_non_pp_part
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.formula_output_ne_printed
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.required_alpha_bracket
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.zero_index_mislabelled
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.delta_sigma_matches_ten_not_nine
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.tier_counts_are_ten_based
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.k3_twentytwo_exceeds_picard_bound
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.abelian_fourfold_total_hodge_dimension
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.epsilon_quantum_is_the_remainder
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.Ch20Ch25Numerics_capstone
#print axioms PrincipiaTractalis.Ch20Ch25Numerics.bounds_are_attainable
