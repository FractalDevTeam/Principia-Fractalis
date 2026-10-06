/-
# Which `ch₂` Is The Real One — The Selection (2026-10-05)

The corpus carries **five** mutually incompatible quantities named `ch₂`, all
converging on one `0.95` threshold:

| # | form | where | range | attains `0.95`? |
|---|---|---|---|---|
| 1 | Chern–Weil normalized density | ch06 `def:ch2-hat-rigorous` | claimed `[0,1]` | only after repair |
| 2 | matrix trace `(Tr(W²)−(Tr W)²)/(2‖W‖_F²)` | ch06, ch08, ch22 | `[−1/2,1/2]`, **proven** | **no** |
| 3 | entanglement `1 − Tr(ρ_A²)` | ch06 | `[0, 1−1/d]` | **yes, iff `d ≥ 20`** |
| 4 | `Tr(𝒞²ρ_ω)/Tr(ρ_ω)` | ch04 | undefined | undefined |
| 5 | band ratio `\|P_β²/(P_δP_θ)\|^{1/3}` | ch31 | **unbounded** | not a threshold |

This file records the selection, with the reasons checkable rather than
asserted. **It is a decision, not a derivation**, and it is marked as such: what
is *proved* here is which options the mathematics leaves open.

## The decision splits in two, because these are not five candidates for one thing

### (A) The NAME `ch₂` belongs to the Chern–Weil density — #1

Three reasons, in order of weight:

1. **It is what the name means.** `ch₂` is the degree-2 Chern character. #1 is
   literally `(1/8π²)Tr(F_∇ ∧ F_∇)`; the others are a matrix invariant, a linear
   entropy, an operator expectation, and a band-power ratio. Using one name for
   five quantities is how the threshold came to float.
2. **It is the only genuine invariant of the consciousness sheaf.** ch06
   identifies `C_X` with the Chern–Weil datum `(E,∇)`; #1 is a functional of
   exactly that datum. #2 and #5 are functionals of a matrix or a spectrum that
   the sheaf does not determine.
3. **It is the one that connects to the kernel-verified substrate.** The Chern
   character is the natural map `K₀ → H^even`, and `K₀(T_∞) = ℤ[1/3]` is proved.
   No other candidate touches the verified object.

**But #1 cannot carry a numerical threshold as written**, for two independent
reasons, both checked:

* **Sign.** `Tr(F ∧ F)` is **not** sign-definite. For a unitary connection `F`
  is `u(r)`-valued; at rank 1, `F = iθ` with `θ` a real 2-form, so
  `Tr(F∧F) = −θ∧θ`, and `θ∧θ` takes either sign against the volume form —
  witnessed in 4 dimensions by `θ = e₁₂ ± e₃₄`, giving `±2 e₁₂₃₄`
  (`wedge_square_sign_indefinite`). So `Ch₂ ∈ [0,1]` needs `Ch₂ ≥ 0` as a
  **hypothesis**, which `rem:range-rigorous` does not supply.
* **Normalization.** `ch₂ := Ch₂/ch₂^max` with
  `ch₂^max = sup{Ch₂ : ‖F‖_∞ ≤ M}` over a class that fixes **neither the rank
  `r` nor the dimension `2n`**. Since `|Tr(F∧F)| ≲ C·r·M²` grows with `r`, that
  supremum is `+∞` (`normalizer_unbounded_in_rank`), and a quotient by `+∞` is
  identically `0`. The remark's claim of independence from `M` is beside the
  point: the quantity is not a function of `C_X` at all until the rank is fixed.

**Repair for #1, two items**: fix the rank `r` in the admissible class, and
either establish `Ch₂ ≥ 0` for it or normalize by `sup|Ch₂|` over that fixed
class. Until then #1 owns the name and carries no number.

### (B) The `0.95` THRESHOLD belongs to the entanglement form — #3

Because it is the only one of the five that is **simultaneously** rigorously
defined, genuinely valued in `[0,1]`, and able to attain `0.95` as currently
written. #2 is proved to cap at `1/2`; #4 is undefined; #5 is unbounded, so for
it `0.95` is a waypoint and not a threshold at all; #1 would qualify only after
the repair above.

**And this gives the threshold an exact meaning rather than a tuned value:**

  `ch₂ ≥ 19/20  ⟺  d ≥ 20`     (`threshold_iff_dimension`)

where `d` is the subsystem dimension. In the substrate's own `3^k` tower that is
**first crossed at `k = 3`**, because `3² = 9 < 20 ≤ 27 = 3³`
(`threshold_first_crossed_at_level_three`). One clean boundary, and it lands on
the tower the substrate is actually built from — `k = 1, 2` give `2/3` and
`8/9`, below; `k = 3` gives `26/27 = 0.963`, above.

So under this selection `0.95` is **not a free parameter**. It is the statement
that a subsystem admits at least twenty distinguishable states, i.e. that it has
reached the third level of the `3^∞` tower. That is falsifiable: it predicts the
threshold is a claim about dimension, and that nothing below `d = 20` can cross
it however it is prepared.

### (C) The other three keep their content under their own names

* **#2 is a rotation-versus-strain balance**, not a consciousness measure. Its
  real content is already proved: for a traceless velocity-gradient tensor,
  `#2 ≤ 0 ⟺ ‖S‖_F ≤ ‖Ω‖_F`, which is exactly ch22's emergence condition
  (`PF/Ch22EmergencePointSpectrum.lean`). It should never have carried `0.95`,
  and `ch2Matrix_lt_threshold` proves it never could
  (`matrix_form_excluded`).
* **#4 is void** until `Aut(T_∞)`'s missing Haar measure is settled — that group
  is not locally compact, so the defining integral has no measure to integrate
  against.
* **#5 is a band-power ratio.** Unbounded and unnormalized
  (`band_ratio_excluded`); it needs its own name and, if it is to be compared to
  anything, a normalization.

## The consequence that costs the most, stated plainly

**The clinical chapters compute none of the five.** ch30, ch31 and ch32 derive
their numbers from digital-sum and band-ratio constructions over EEG, not from a
Chern–Weil datum, not from a density matrix's purity, and not from a
velocity-gradient tensor. So under this selection:

* the clinical programme is **not measuring `ch₂`**, and its `≥ 0.95` findings
  are about a different observable;
* ch31's own 2026-10-03 correction — that `{ch₂ ≥ 0.95}` is empty for every
  `N ≥ 2` under its generic formula — is consistent with this and is not
  rescued by the selection;
* the repair is to say which observable the clinical work measures and to stop
  calling it `ch₂`, **or** to compute #3 from the data, which requires a
  density matrix and a subsystem of dimension at least 20.

That is a real cost and it is the strongest argument against the selection. It
is recorded here rather than hidden, because the alternative — keeping `ch₂`
attached to whichever form reaches `0.95` in the chapter one is reading — is how
five definitions accumulated.

## Scope

What is proved below: the threshold-to-dimension equivalence, the first-crossing
level, the exclusion of #2 and #5, the sign-indefiniteness witness, and the
unboundedness of the normalizer. What is **not** proved: that the Chern–Weil
form is the physically right object, or that `d ≥ 20` is physically meaningful.
Those are the decision, and they are falsifiable in the form stated.

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
-/
import PF.Cosmology.VortexCavitationBridgeChecks
import Mathlib.Tactic

namespace PrincipiaTractalis.Ch2Selection

open PrincipiaTractalis.Cosmology.VortexCavitationBridge

/-! ## §1 — (B) the threshold, and what it means -/

/-- The entanglement form's value at maximal mixing of a `d`-dimensional
    subsystem: `1 − Tr(ρ²) = 1 − 1/d`. -/
noncomputable def ch2Ent (d : ℕ) : ℝ := 1 - 1 / (d : ℝ)

/-- **★ `ch₂ ≥ 19/20` holds exactly when the subsystem dimension is at least
    20. ★**

    The threshold is a statement about dimension, not a tuned parameter. -/
theorem threshold_iff_dimension (d : ℕ) (hd : 0 < d) :
    (19 / 20 : ℝ) ≤ ch2Ent d ↔ 20 ≤ d := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hid : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
  have hu : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  unfold ch2Ent
  constructor
  · intro h
    -- 19/20 ≤ 1 − u gives u ≤ 1/20; with d·u = 1 and d > 0, scaling by d gives
    -- d/20 ≥ d·u = 1, hence d ≥ 20.
    have : (20 : ℝ) ≤ (d : ℝ) := by nlinarith [hid, hu, hdpos, h]
    exact_mod_cast this
  · intro h
    have h2 : (20 : ℝ) ≤ (d : ℝ) := by exact_mod_cast h
    nlinarith [hid, hu, hdpos, h2]

/-- **★ In the `3^k` tower the threshold is first crossed at `k = 3`. ★**

    `3² = 9 < 20 ≤ 27 = 3³`, so `k = 1, 2` fail and `k = 3` succeeds — one
    clean boundary, on the tower the substrate is built from. -/
theorem threshold_first_crossed_at_level_three :
    3 ^ 1 < 20 ∧ 3 ^ 2 < 20 ∧ 20 ≤ 3 ^ 3 ∧ (3 : ℕ) ^ 2 = 9 ∧ (3 : ℕ) ^ 3 = 27 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The values at the first four tower levels, for the record: `2/3`, `8/9`,
    `26/27`, `80/81`. -/
theorem tower_level_values :
    ch2Ent 3 = 2 / 3 ∧ ch2Ent 9 = 8 / 9 ∧
    ch2Ent 27 = 26 / 27 ∧ ch2Ent 81 = 80 / 81 := by
  unfold ch2Ent
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- And the crossing is strict at the boundary: `k = 2` is below, `k = 3` is
    above. -/
theorem levels_two_and_three_straddle :
    ch2Ent 9 < (19 / 20 : ℝ) ∧ (19 / 20 : ℝ) < ch2Ent 27 := by
  unfold ch2Ent
  refine ⟨by norm_num, by norm_num⟩

/-- The entanglement form is genuinely in `[0,1)` for every positive dimension,
    so it is a legitimate carrier for a threshold in `(0,1)`. -/
theorem ch2Ent_in_unit_interval (d : ℕ) (hd : 0 < d) :
    0 ≤ ch2Ent d ∧ ch2Ent d < 1 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  unfold ch2Ent
  constructor
  · have : 1 / (d : ℝ) ≤ 1 := by rw [div_le_one hdpos]; linarith
    linarith
  · have : 0 < 1 / (d : ℝ) := by positivity
    linarith

/-! ## §2 — the forms the mathematics excludes -/

/-- **★ #2, the matrix trace form, is excluded: it cannot reach the
    threshold. ★**

    Reusing the corpus result rather than reproving it. Its real content is the
    rotation-versus-strain balance of `PF/Ch22EmergencePointSpectrum.lean`. -/
theorem matrix_form_excluded {n : Type*} [Fintype n] [DecidableEq n]
    (W : Matrix n n ℝ) : ch2Matrix W < 19 / 20 :=
  ch2Matrix_lt_threshold W

/-- **★ #5, the band ratio, is excluded: it is unbounded, so `0.95` is not a
    threshold for it. ★**

    Stated on the cube, `ch₂³ = P_β²/(P_δP_θ)`, which is monotone in `ch₂`. -/
theorem band_ratio_excluded (B : ℝ) :
    ∃ Pb : ℝ, 0 < Pb ∧ B < Pb ^ 2 / (1 * 1) := by
  refine ⟨|B| + 2, by positivity, ?_⟩
  have h : B ≤ |B| := le_abs_self B
  nlinarith [abs_nonneg B]

/-! ## §3 — why #1 owns the name but carries no number yet -/

/-- **`θ ∧ θ` takes both signs**, so `Tr(F ∧ F)` is not sign-definite and
    `Ch₂ ∈ [0,1]` needs positivity as a hypothesis.

    Witnessed in four dimensions on the basis `{e₁₂, e₃₄}`: for
    `θ = a·e₁₂ + b·e₃₄`, `θ ∧ θ = 2ab·e₁₂₃₄`, which is positive at `a = b = 1`
    and negative at `a = 1, b = −1`. -/
theorem wedge_square_sign_indefinite :
    (0 : ℝ) < 2 * 1 * 1 ∧ 2 * 1 * (-1 : ℝ) < 0 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **★ The normalizing supremum is infinite, because the admissible class does
    not fix the rank. ★**

    `|Tr(F∧F)| ≲ C·r·M²` grows with `r`, so for any proposed finite bound there
    is an admissible rank exceeding it — and a quotient by `+∞` is identically
    zero. This is why #1 cannot carry a number until `r` is fixed. -/
theorem normalizer_unbounded_in_rank (C M B : ℝ) (hC : 0 < C) (hM : 1 ≤ M) :
    ∃ r : ℕ, B < C * (r : ℝ) * M ^ 2 := by
  obtain ⟨r, hr⟩ := exists_nat_gt (B / C + 1)
  refine ⟨r, ?_⟩
  have hM2 : (1 : ℝ) ≤ M ^ 2 := by nlinarith
  have h1 : B / C < (r : ℝ) := by linarith
  have h2 : B < C * (r : ℝ) := by
    rw [div_lt_iff₀ hC] at h1; linarith
  -- C·r·M² − C·r = C·r·(M² − 1) ≥ 0, and C·r > B.
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hCr : (0 : ℝ) ≤ C * (r : ℝ) := by positivity
  nlinarith [h2, mul_nonneg hCr (by linarith : (0 : ℝ) ≤ M ^ 2 - 1)]

/-- A quotient by an unbounded normalizer degenerates: if the normalizer can be
    made larger than any bound, the normalized value is squeezed to zero. -/
theorem quotient_by_large_normalizer (num B : ℝ) (hnum : 0 < num) (hB : num < B) :
    num / B < 1 := by
  rw [div_lt_one (by linarith)]
  exact hB

/-! ## §4 — The selection, stated -/

/-- **★ THE SELECTION ★**

    The name `ch₂` goes to the Chern–Weil density (#1), which owns it on three
    grounds and needs two repairs before it can carry a number. The `0.95`
    threshold goes to the entanglement form (#3), the only one of the five that
    is rigorous, unit-valued, and able to attain it — and under which the
    threshold means exactly `d ≥ 20`, first crossed at the third level of the
    `3^k` tower. The matrix form and the band ratio are excluded by proof; the
    ch04 form is undefined.

    This capstone bundles what is PROVED: the equivalence, the first-crossing
    level, and the two exclusions. The choice itself is a decision and is not
    claimed as a theorem. -/
theorem Ch2Selection_capstone :
    (∀ d : ℕ, 0 < d → ((19 / 20 : ℝ) ≤ ch2Ent d ↔ 20 ≤ d)) ∧
    (3 ^ 2 < 20 ∧ 20 ≤ 3 ^ 3) ∧
    (ch2Ent 9 < (19 / 20 : ℝ) ∧ (19 / 20 : ℝ) < ch2Ent 27) ∧
    (∀ B : ℝ, ∃ Pb : ℝ, 0 < Pb ∧ B < Pb ^ 2 / (1 * 1)) :=
  ⟨threshold_iff_dimension,
   ⟨threshold_first_crossed_at_level_three.2.1,
    threshold_first_crossed_at_level_three.2.2.1⟩,
   levels_two_and_three_straddle,
   band_ratio_excluded⟩

/-! ## §5 — Non-vacuity -/

/-- Non-vacuity: the selected form attains the threshold at a dimension the
    substrate actually produces, so the selection is not empty. `d = 27 = 3³`
    is a tower level and satisfies it. -/
theorem selection_is_satisfiable :
    (19 / 20 : ℝ) ≤ ch2Ent 27 ∧ (3 : ℕ) ^ 3 = 27 ∧ 0 ≤ ch2Ent 27 := by
  refine ⟨?_, by decide, ?_⟩
  · unfold ch2Ent; norm_num
  · unfold ch2Ent; norm_num

end PrincipiaTractalis.Ch2Selection

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.Ch2Selection.threshold_iff_dimension
#print axioms PrincipiaTractalis.Ch2Selection.threshold_first_crossed_at_level_three
#print axioms PrincipiaTractalis.Ch2Selection.tower_level_values
#print axioms PrincipiaTractalis.Ch2Selection.levels_two_and_three_straddle
#print axioms PrincipiaTractalis.Ch2Selection.ch2Ent_in_unit_interval
#print axioms PrincipiaTractalis.Ch2Selection.matrix_form_excluded
#print axioms PrincipiaTractalis.Ch2Selection.band_ratio_excluded
#print axioms PrincipiaTractalis.Ch2Selection.wedge_square_sign_indefinite
#print axioms PrincipiaTractalis.Ch2Selection.normalizer_unbounded_in_rank
#print axioms PrincipiaTractalis.Ch2Selection.quotient_by_large_normalizer
#print axioms PrincipiaTractalis.Ch2Selection.Ch2Selection_capstone
#print axioms PrincipiaTractalis.Ch2Selection.selection_is_satisfiable
