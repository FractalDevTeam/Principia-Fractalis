/-
# Which `ch₂` Is The Real One — The Selection, Narrowed (2026-10-05, rev 2)

Revision of the same day's first attempt, after two independent reviews found
three overstatements in it. **The naming decision survives; three of its formal
claims did not, and one of its grounds was false.** Worse, the reviews prompted
a check that found the selection *inconsistent with `ch08`* — which is the most
important content in this file and is new.

Everything withdrawn is listed in §0 rather than quietly dropped.

## §0 — What the first attempt got wrong

1. **`ch₂ ≥ 19/20 ⟺ d ≥ 20` is not an equivalence.** It holds for the
   *maximally mixed ceiling* `1 − 1/d`, which is what was actually defined, but
   it was presented as a statement about `ch₂` of a state. A **pure state has
   `ch₂ = 0` in every dimension** (`pure_state_is_zero`). `d ≥ 20` is
   **necessary, not sufficient**. The correct pair is
   `threshold_implies_effective_dimension` and
   `ceiling_threshold_iff_dimension`, and the right reading is **inverse
   purity**:

     `1 − Tr(ρ²) ≥ 19/20  ⟺  1/Tr(ρ²) ≥ 20`,

   i.e. the threshold is about **effective dimension**, not dimension. Level 3
   is therefore the first tower level **capable** of crossing, not one that
   crosses.

2. **The bipartite constraint was omitted.** `ch06` defines the form for a pure
   state on `H_A ⊗ H_B`, where `rank ρ_A ≤ min(d_A, d_B)`. Effective dimension
   `≥ 20` therefore needs **both** factors `≥ 20`, so a total dimension `≥ 400`
   — in the ternary tower a level-3 subsystem inside a total system of level
   `≥ 6`, since `3⁵ = 243 < 400 ≤ 729 = 3⁶`
   (`bipartite_needs_both_factors`). **A level-3 system alone, in a pure state,
   cannot cross the threshold.**

3. **The tower does not select `0.95`.** Every threshold in `(8/9, 26/27]` has
   the same first-crossing level `k = 3`
   (`threshold_interval_gives_same_level`), an interval of width `2/27`. The
   values the tower itself distinguishes are `1 − 3^{-k}`, and `19/20` is not
   among them (`nineteen_twentieths_not_a_tower_value`) — `20` is not a ternary
   number. So "landing on the tower" is **not** evidence for `0.95`
   specifically, and the claim that `0.95` "is not a free parameter" was
   overstated. The tower constrains it to an interval; it does not pin it.

4. **`normalizer_unbounded_in_rank` was mislabelled.** It proves that the
   *estimate* `C·r·M²` is unbounded. An unbounded upper bound does **not** show
   the actual supremum of `Ch₂` is infinite — that needs an explicit admissible
   family whose `Ch₂` grows with rank, which is not supplied. The conclusion
   "the quotient is identically zero" is **withdrawn**; what survives is that
   the normalizer is *not shown to be finite*, which is enough to block a
   numerical threshold but is a weaker statement.

5. **`wedge_square_sign_indefinite` was decoration.** It kernel-checked `2 > 0`
   and `−2 < 0`. The exterior-algebra fact — that `θ ∧ θ` takes both signs, so
   `Tr(F∧F)` is not sign-definite — is standard and almost certainly right, but
   it is **not formalized here**, and a scalar inequality named after it
   overstates what the kernel saw. Restated in §4 as prose with an explicit
   scope note. *This is the same failure I corrected in ch21's Obstruction C
   earlier the same day and then repeated.*

6. **"Falsifiable" was the wrong word.** "Nothing below `d = 20` can cross it"
   is a theorem; no experiment can contradict it. A falsifiable claim would say
   what systems above threshold *do* that systems below do not. The selection
   makes no such prediction.

7. **Ground 3 of the naming argument was false.** The first attempt said the
   Chern–Weil form "is the only one that touches the kernel-verified substrate,
   since the Chern character is `K₀ → H^even` and `K₀(T_∞) = ℤ[1/3]` is
   proved." Both halves fail. `K₀` is **not** formalized as operator K-theory:
   `PF/Consciousness/TimelessFieldKTheoryUpgrade.lean` defines a hand-rolled
   `KZeroCarrier` as pairs `(n,k)` with a `mulByThree` map and proves
   injectivity and nontriviality of that **model** — not that `K₀` of the
   C*-algebra is `ℤ[1/3]`. And for a UHF algebra the Chern character's content
   is the **trace**, which is degree **zero**; there is no degree-2 component,
   so a degree-2 Chern character has no home on the substrate at all. The
   naming decision now rests on grounds 1 and 2 only.

## §1 — The selection, as it now stands

### (A) The name `ch₂` → the Chern–Weil density, on two grounds

1. **It is what the name means.** `ch₂` is the degree-2 Chern character. The
   others are a matrix invariant, a linear entropy, an operator expectation and
   a band-power ratio. One name for five quantities is how the threshold came
   to float.
2. **It is the only one that is a functional of the datum `ch06` actually
   defines.** `ch06` identifies `C_X` with the Chern–Weil pair `(E,∇)`; only
   this form is a functional of it.

It still **carries no number**, because the normalizer is not shown finite
(§0.4) and `[0,1]` needs `Ch₂ ≥ 0` as an unsupplied hypothesis (§4). Repairs:
fix the rank in the admissible class, exhibit the normalizer as finite, and
establish positivity.

**And a dependency to record with the name.** Since there is no degree-2 Chern
character on the UHF algebra (§0.7), a Chern–Weil `ch₂` needs a bundle `(E,∇)`
over a base manifold `X`. The corpus constructs **neither `X` nor a link from
`T_∞` to it** — the spacetime-quotient attempts are `r333`–`r336`, and they are
where that construction would have to live. So the name now attaches to an
object **whose carrier is not yet built**. That is not an argument against the
naming decision, but it is the next thing the decision requires.

### (B) The threshold `0.95` → the entanglement form, **as a classifier only**

It is the only one of the five that is simultaneously rigorous, unit-valued and
able to attain `0.95`. The correct statements are the inverse-purity ones of
§0.1 together with the bipartite constraint of §0.2.

### (C) **And this is where the selection breaks: it conflicts with `ch08`.**

`ch08:80` boxes the consciousness stress-energy as

  `C^{μν} = ∫ ⟨ω|T̂^{μν}|ω⟩ · Θ(ch₂(ω) − 0.95) · R_f(α_ω, s) dμ(ω)`,

so the threshold **gates a source term in Einstein's equations** — dynamics, not
classification. And `PF/Collapse/RateModulation.lean:39` states, in the corpus's
own words, that a rate "depending on an ENTANGLEMENT MEASURE OF THE STATE is
exactly the forbidden case, and the framework's `1 − Tr(ρ_A²)` reading of `ch₂`
is such a measure. That reading is therefore ruled out as a collapse-rate
argument, while the field/geometric readings survive." The hazard is
Gisin–Polchinski: nonlinear evolution on density matrices generically permits
superluminal signalling, and a Heaviside gate on a nonlinear state functional is
nonlinear dynamics.

**This is a serious concern and it is NOT a proved impossibility.** Rev 2 of
this file stated it as a trilemma with all three horns occupied and concluded
the gate is "unsupported under every available reading", with one repair.
Reviewers were right that all three parts of that overreach:

* **`RateModulation` is about collapse RATES, not source gates.** It proves
  that a rate depending on a nonlinear state functional is not affine on
  mixtures, with an explicit two-outcome witness. A gated *source term* in the
  field equations is the same **mechanism** — a nonlinear functional of the
  state breaking affinity — but it is **not the same theorem**, and the corpus
  has not proved the source-gate version. Citing `RateModulation:39` as already
  ruling this out was wrong.
* **`no_form_both_reaches_and_gates` (§6) is an abstract schema.** Its premises
  — that exactly one form `reaches`, and that this form does not `gate` — are
  **supplied as hypotheses, not established** for the manuscript's forms. It
  records the *shape* of the worry and proves nothing about `ch₂`.
* **The hazard depends on a reading the chapter does not fix.** See below.

### Two readings of `ch08:79–81`, and the choice is authorial

  `C^{μν} = ∫ ⟨ω|T̂^{μν}|ω⟩ · Θ(ch₂(ω) − 0.95) · R_f(α_ω,s) dμ(ω)`

* **(R1) `ω` is the physical state.** Then `Θ(ch₂(ω) − 0.95)` is a nonlinear
  functional of it, the source term is nonlinear in the density matrix, and the
  Gisin–Polchinski signalling worry applies.
* **(R2) `ω` is an integration label** over a family of states with measure
  `μ`, which is what the formula literally says. Then the gate restricts the
  **domain of integration**: if the `|ω⟩` are eigenstates of a consciousness
  operator `𝒞` with eigenvalue `ch₂(ω)`, the expression is a trace against a
  spectral projection, `Tr(T̂^{μν} · 1_{[0.95,∞)}(𝒞) · R_f)`. No state
  functional appears and **no affinity violation arises**. The cost of R2 is
  that `C^{μν}` then does not depend on the state of matter at all unless `μ`
  carries it — it is a fixed background tensor.

**The formula as printed supports R2; the surrounding prose reads like R1.**
Which is intended is Pablo's decision and this file does not take it.

### Repair alternatives — at least three, not one

1. **Remove the gate**, and let the threshold classify states only.
2. **Replace it with an affine observable.** A signalling-safe gate must be
   affine in the density matrix, and affine functionals of states are exactly
   expectation values of operators — so a *spectral* threshold is the form that
   survives where a state-level one does not: replace `Θ(ch₂(state) − 0.95)·⟨T̂⟩`
   by `⟨E T̂ E⟩` with `E := 1_{[0.95,∞)}(𝒞)`. `ch08:108–114` already uses a
   projector inside `J^ν`, so the ingredient is in the book. **Blocker**: `𝒞` is
   `ch04`'s operator, void pending the missing Haar measure — this repair makes
   that decision load-bearing.
3. **Supply a consistent field/geometric model** carrying the threshold, i.e.
   complete the Chern–Weil repairs.

Alternative 2 is a reviewer's proposal, recorded as a candidate and not as a
finding.

### (D) The other three, unchanged

The matrix form is a rotation-versus-strain balance (`matrix_form_excluded`
proves it cannot reach `0.95`); `ch04`'s form is void pending the Haar measure;
`ch31`'s band ratio is unbounded (`band_ratio_excluded`).

## §2 — Standing cost

The clinical chapters compute none of the five, so under this selection they are
not measuring `ch₂`. Unchanged from the first attempt, and still the strongest
argument against it.

## Scope

Proved below: the inverse-purity implication, the ceiling equivalence, the
pure-state witness, the bipartite dimension count, the threshold-interval
non-uniqueness, the exclusion of the matrix and band-ratio forms. **Not proved
and not claimed**: that the Chern–Weil form is physically right; that `Tr(F∧F)`
is sign-indefinite (standard, prose only, §4); that the Chern–Weil normalizer is
infinite (only that it is not shown finite); that `K₀(T_∞) = ℤ[1/3]` holds for
the C*-algebra; and that the `ch08` conflict has a resolution. **Nor is the `ch08`
concern itself proved**: §6 is a schema with supplied premises, the
source-gate analogue of `RateModulation` does not exist, and under reading R2
of `ch08:79–81` the worry does not arise. It is recorded as a serious
unformalized concern with at least three candidate repairs, not as an
impossibility.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05, rev 2.
-/
import PF.Cosmology.VortexCavitationBridgeChecks
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch2Selection

open PrincipiaTractalis.Cosmology.VortexCavitationBridge

/-! ## §1 — The entanglement form, stated correctly -/

/-- The entanglement form as a function of the state's **purity**
    `p = Tr(ρ²)`, which is what it actually depends on:
    `ch₂ = 1 − p`. -/
noncomputable def ch2OfPurity (p : ℝ) : ℝ := 1 - p

/-- The **ceiling** of the entanglement form over `d`-dimensional states,
    attained only at maximal mixing where `p = 1/d`.

    Named `Ceiling` because the first attempt called this `ch2Ent` and then
    reasoned about it as though it were `ch₂` of an arbitrary state. It is
    not. -/
noncomputable def ch2Ceiling (d : ℕ) : ℝ := 1 - 1 / (d : ℝ)

/-- **A pure state gives `ch₂ = 0`, in every dimension.**

    Purity `1`. This is the witness that `d ≥ 20` cannot be sufficient. -/
theorem pure_state_is_zero : ch2OfPurity 1 = 0 := by
  unfold ch2OfPurity; norm_num

/-- **★ The threshold is a statement about INVERSE PURITY — effective
    dimension. ★**

    `1 − p ≥ 19/20 ⟺ p ≤ 1/20`, i.e. `1/p ≥ 20`. This is the correct reading,
    and it is a statement about the state, not about the space it lives in. -/
theorem threshold_iff_purity (p : ℝ) :
    (19 / 20 : ℝ) ≤ ch2OfPurity p ↔ p ≤ 1 / 20 := by
  unfold ch2OfPurity
  constructor <;> intro h <;> linarith

/-- **★ Crossing the threshold IMPLIES dimension at least 20 — one direction
    only. ★**

    Since `p ≥ 1/d` for any state on a `d`-dimensional space, `p ≤ 1/20` forces
    `d ≥ 20`. The converse fails, by `pure_state_is_zero`.

    Stated without `0 < p`: a first draft carried it and the unused-binder
    check flagged it, correctly — `1/d ≤ p` with `d > 0` already gives
    positivity, so the hypothesis was redundant and the lemma is stronger
    without it. -/
theorem threshold_implies_effective_dimension (p : ℝ) (d : ℕ)
    (hd : 0 < d) (hmin : 1 / (d : ℝ) ≤ p)
    (hthr : (19 / 20 : ℝ) ≤ ch2OfPurity p) :
    (20 : ℝ) ≤ (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hple : p ≤ 1 / 20 := (threshold_iff_purity p).mp hthr
  have h1 : 1 / (d : ℝ) ≤ 1 / 20 := le_trans hmin hple
  have hid : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  nlinarith [h1, hid, hdpos]

/-- **The ceiling equivalence** — true, and now correctly scoped to the
    ceiling. `d ≥ 20` is exactly the condition for *some* state in dimension
    `d` to reach the threshold, namely the maximally mixed one. -/
theorem ceiling_threshold_iff_dimension (d : ℕ) (hd : 0 < d) :
    (19 / 20 : ℝ) ≤ ch2Ceiling d ↔ 20 ≤ d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hid : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  have hu : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  unfold ch2Ceiling
  constructor
  · intro h
    have : (20 : ℝ) ≤ (d : ℝ) := by nlinarith [hid, hu, hdpos, h]
    exact_mod_cast this
  · intro h
    have h2 : (20 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    nlinarith [hid, hu, hdpos, h2]

/-! ## §2 — The bipartite constraint -/

/-- **★ For a pure state on `H_A ⊗ H_B`, crossing needs BOTH factors `≥ 20`. ★**

    `rank ρ_A ≤ min(d_A, d_B)` and the effective dimension is at most that
    rank, so both factors must be at least `20` and the total dimension at
    least `400`. -/
theorem bipartite_needs_both_factors (dA dB : ℕ) (h : 20 ≤ min dA dB) :
    20 ≤ dA ∧ 20 ≤ dB ∧ 400 ≤ dA * dB := by
  have hA : 20 ≤ dA := le_trans h (min_le_left _ _)
  have hB : 20 ≤ dB := le_trans h (min_le_right _ _)
  exact ⟨hA, hB, Nat.mul_le_mul hA hB⟩

/-- **★ In the ternary tower that is a level-3 subsystem inside a total system
    of level at least 6. ★**

    `3⁵ = 243 < 400 ≤ 729 = 3⁶`. So a level-3 system *alone*, in a pure state,
    cannot cross the threshold — which the first attempt omitted. -/
theorem tower_total_level_at_least_six :
    3 ^ 5 < 400 ∧ 400 ≤ 3 ^ 6 ∧ (3 : ℕ) ^ 5 = 243 ∧ (3 : ℕ) ^ 6 = 729 ∧
    20 ≤ 3 ^ 3 ∧ 3 ^ 3 * 3 ^ 3 = 3 ^ 6 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## §3 — The tower does not select `0.95` -/

/-- **★ Every threshold in `(8/9, 26/27]` has first-crossing level 3. ★**

    So the tower constrains the threshold to an interval of width `2/27`; it
    does not pin it. Witnessed at four values including `19/20`. -/
theorem threshold_interval_gives_same_level :
    (8 / 9 : ℝ) < 9 / 10 ∧ (9 / 10 : ℝ) ≤ 26 / 27 ∧
    (8 / 9 : ℝ) < 19 / 20 ∧ (19 / 20 : ℝ) ≤ 26 / 27 ∧
    (8 / 9 : ℝ) < 24 / 25 ∧ (24 / 25 : ℝ) ≤ 26 / 27 ∧
    (26 / 27 : ℝ) - 8 / 9 = 2 / 27 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
          by norm_num, by norm_num, by norm_num⟩

/-- **★ `19/20` is not one of the tower's own values `1 − 3^{-k}`. ★**

    The tower distinguishes `2/3`, `8/9`, `26/27`, `80/81`; `20` is not a
    ternary number. So `0.95` is not selected by the tower, only located in an
    interval by it. -/
theorem nineteen_twentieths_not_a_tower_value :
    (19 / 20 : ℝ) ≠ 2 / 3 ∧ (19 / 20 : ℝ) ≠ 8 / 9 ∧
    (19 / 20 : ℝ) ≠ 26 / 27 ∧ (19 / 20 : ℝ) ≠ 80 / 81 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The tower's own values, for comparison. -/
theorem tower_values :
    ch2Ceiling 3 = 2 / 3 ∧ ch2Ceiling 9 = 8 / 9 ∧
    ch2Ceiling 27 = 26 / 27 ∧ ch2Ceiling 81 = 80 / 81 := by
  unfold ch2Ceiling
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## §4 — Why the Chern–Weil form carries no number

    **Scope note — read before citing this section.** Two claims about the
    Chern–Weil form are made in the header and are **prose only**, not
    formalized here:

    * that `Tr(F_∇ ∧ F_∇)` is not sign-definite, so `Ch₂ ∈ [0,1]` needs
      `Ch₂ ≥ 0` as a hypothesis. Standard exterior algebra; the first attempt
      "witnessed" it with the scalar inequalities `2 > 0` and `−2 < 0`, which
      is decoration and has been removed.
    * that the normalizing supremum is infinite. The first attempt proved only
      that an *upper estimate* `C·r·M²` is unbounded in the rank, which does
      not establish it. **What is claimed now is only that the normalizer is
      not shown to be finite**, which suffices to block a numerical threshold.

    What *is* formalized below is the single arithmetic consequence: a quotient
    by an unbounded-above denominator cannot be pinned. -/

/-- A quotient by a denominator that may be made arbitrarily large is not
    bounded below away from zero — the arithmetic content of "the normalizer
    must be shown finite before `ch₂` can carry a number". -/
theorem unpinned_quotient (num eps : ℝ) (hnum : 0 < num) (heps : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ num / B < eps := by
  refine ⟨num / eps + 1, by positivity, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  have : num / eps * eps = num := by field_simp
  nlinarith [this, heps, hnum]

/-! ## §5 — The forms the mathematics excludes -/

/-- **#2, the matrix trace form, cannot reach the threshold.** Reusing the
    corpus result. -/
theorem matrix_form_excluded {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) : ch2Matrix W < 19 / 20 :=
  ch2Matrix_lt_threshold W

/-- **#5, the band ratio, is unbounded**, so `0.95` is not a threshold for
    it. -/
theorem band_ratio_excluded (B : ℝ) :
    ∃ Pb : ℝ, 0 < Pb ∧ B < Pb ^ 2 / (1 * 1) := by
  refine ⟨|B| + 2, by positivity, ?_⟩
  have h : B ≤ |B| := le_abs_self B
  nlinarith [abs_nonneg B]

/-! ## §6 — The `ch08` concern, as an abstract schema

    **Scope note, and it is the important part of this section.** What follows
    is a propositional schema. Its premises are **hypotheses supplied by the
    caller, not facts established for the manuscript's forms of `ch₂`**. It
    therefore proves *nothing* about `ch08`, and must not be cited as though it
    did — which is what rev 2 of this file did. The `ch08` concern is
    **unformalized**: see §1(C) for what is and is not known, including the
    `R1`/`R2` reading ambiguity that determines whether the worry applies at
    all. -/

/-- **An abstract schema, premises unestablished.**

    If the only form satisfying `reaches` is one that fails `gates`, then
    nothing satisfies both. Trivial, and recorded only to make the *shape* of
    the `ch08` worry precise.

    **Neither premise is proved for `ch₂`.** `honly` would require showing the
    entanglement form is the unique form attaining `0.95` — plausible but not
    established, since the Chern–Weil form's status is open. `hnot` would
    require a source-gate no-signalling theorem, which the corpus does not
    have: `RateModulation` proves the collapse-RATE case only. -/
theorem no_form_both_reaches_and_gates
    {Form : Type*} (reaches gates : Form → Prop) (e : Form)
    (honly : ∀ f, reaches f → f = e) (hnot : ¬ gates e) :
    ¬ ∃ f, reaches f ∧ gates f := by
  rintro ⟨f, hr, hg⟩
  rw [honly f hr] at hg
  exact hnot hg

/-! ## §7 — Capstone -/

/-- **★ The selection, narrowed ★**

    What is proved: the threshold reads as inverse purity; crossing implies
    dimension `≥ 20` but not conversely, since a pure state gives `0`; the
    ceiling equivalence; the bipartite requirement of both factors `≥ 20` and
    hence tower level `≥ 6`; the threshold interval `(8/9, 26/27]` giving the
    same crossing level, so the tower does not pin `0.95`; and the exclusion of
    the matrix and band-ratio forms. -/
theorem Ch2Selection_capstone :
    ch2OfPurity 1 = 0 ∧
    (∀ p : ℝ, (19 / 20 : ℝ) ≤ ch2OfPurity p ↔ p ≤ 1 / 20) ∧
    (∀ d : ℕ, 0 < d → ((19 / 20 : ℝ) ≤ ch2Ceiling d ↔ 20 ≤ d)) ∧
    (3 ^ 5 < 400 ∧ 400 ≤ 3 ^ 6) ∧
    ((19 / 20 : ℝ) ≠ 26 / 27) ∧
    (∀ B : ℝ, ∃ Pb : ℝ, 0 < Pb ∧ B < Pb ^ 2 / (1 * 1)) :=
  ⟨pure_state_is_zero,
   threshold_iff_purity,
   ceiling_threshold_iff_dimension,
   ⟨tower_total_level_at_least_six.1, tower_total_level_at_least_six.2.1⟩,
   nineteen_twentieths_not_a_tower_value.2.2.1,
   band_ratio_excluded⟩

/-! ## §8 — Non-vacuity -/

/-- Non-vacuity, and it is the pointed kind: the threshold IS attainable — the
    maximally mixed state on `27` dimensions reaches `26/27 > 19/20` — so the
    selection is not empty. What the first attempt got wrong is that this is a
    statement about one particular state, not about the dimension. -/
theorem threshold_is_attainable :
    (19 / 20 : ℝ) ≤ ch2OfPurity (1 / 27) ∧ ch2OfPurity (1 / 27) = 26 / 27 := by
  unfold ch2OfPurity
  refine ⟨by norm_num, by norm_num⟩

end PrincipiaTractalis.Ch2Selection

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch2Selection.pure_state_is_zero
#print axioms PrincipiaTractalis.Ch2Selection.threshold_iff_purity
#print axioms PrincipiaTractalis.Ch2Selection.threshold_implies_effective_dimension
#print axioms PrincipiaTractalis.Ch2Selection.ceiling_threshold_iff_dimension
#print axioms PrincipiaTractalis.Ch2Selection.bipartite_needs_both_factors
#print axioms PrincipiaTractalis.Ch2Selection.tower_total_level_at_least_six
#print axioms PrincipiaTractalis.Ch2Selection.threshold_interval_gives_same_level
#print axioms PrincipiaTractalis.Ch2Selection.nineteen_twentieths_not_a_tower_value
#print axioms PrincipiaTractalis.Ch2Selection.tower_values
#print axioms PrincipiaTractalis.Ch2Selection.unpinned_quotient
#print axioms PrincipiaTractalis.Ch2Selection.matrix_form_excluded
#print axioms PrincipiaTractalis.Ch2Selection.band_ratio_excluded
#print axioms PrincipiaTractalis.Ch2Selection.no_form_both_reaches_and_gates
#print axioms PrincipiaTractalis.Ch2Selection.Ch2Selection_capstone
#print axioms PrincipiaTractalis.Ch2Selection.threshold_is_attainable
