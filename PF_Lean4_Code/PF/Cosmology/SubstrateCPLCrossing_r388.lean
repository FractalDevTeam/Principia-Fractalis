/-
# r388: the substrate CPL pair crosses `w = -1` at exactly `z = 1/√5`

★ 2026-10-29 r388 — the golden-ratio ansatz is not merely phantom; it is phantom
at a closed-form redshift ★

## Why this supersedes the framing of r387

r387 proved that the substrate pair `(w₀, wₐ) = (-φ/2, -1/φ)` fails r219's
non-phantom bound, and left a three-way fork whose branch 1 was "drop the
ansatz". **That framing was wrong about which object is load-bearing.** The
golden ratios are integral to the framework — they carry the α-skeleton
(`α_Hodge = φ`, `α_NP = φ + 1/4`) and the substrate's metallic-ratio structure.
They are not a disposable fit.

Taking them as fixed turns r387's inequality into a *measurement-grade
prediction*. The CPL form `w(a) = w₀ + wₐ(1-a)` with those two values crosses
`w = -1` at exactly one scale factor, and it is a closed form:

    a* = (3 - φ)/2        ≈ 0.6909830
    z* = (φ - 1)/(3 - φ)  = 1/√5  ≈ 0.4472136

Both proved below. `z* = 1/√5` is exact, not numerical: `√5 = 2φ - 1`, and
`√5(φ - 1) = 3 - φ` follows from `φ² = φ + 1`.

## Why that matters, and what it is worth

r219's `wEff_ge_neg_one_iff` makes `w = -1` **equivalent** to `g = 0`, and
`exists_wEff_crossing_of_sign_change` locates a crossing exactly where `g`
vanishes. So the ansatz predicts `g` has its zero at `z = 1/√5`.

The corpus independently *measures* that zero —
`codex/COSMOLOGY_DE_ROUTE_MAP_2026-10-11.md:30` records `g₀ ≈ 0.74–1.05 H₀` with
the zero at `z ≈ 0.40 ± 0.03`, stable across three supernova samples. Prediction
`0.4472` against measurement `0.40 ± 0.03` is a **1.57σ** comparison.

**This is a different kind of agreement from a fit-to-fit coincidence.** `1/√5`
is *derived* from the ratios with no freedom: no parameter was adjusted to land
near 0.40, and the derivation consumes only `φ² = φ + 1`. The measured zero came
from inverting r219 against SN data. So the two numbers are a genuine
prediction/measurement pair, which is exactly what the comparison to the
dark-dimension literature's `z ~ 0.4` Casimir realisation is *not* — that one is
two fits to substantially the same data.

**Scope, stated plainly.** 1.57σ is agreement at the level of "not excluded, not
confirmed". It is not a detection and this file claims none. And the ratios
themselves are an **ansatz** (`Priority4SubstrateDischarge`, Agent 10
2026-07-04), not a derivation from the substrate — so what is established is
*conditional*: **given** the golden-ratio pair, the crossing redshift is forced
to `1/√5`. Deriving the pair itself from the substrate remains open and is the
thing that would make this a prediction rather than a consequence.

## What this settles about r387's fork

Branch 1 ("keep `g ≥ 0`, drop the ansatz") is the wrong branch, and the corpus's
own measurement already said so: a *measured* zero of `g` means `hg0 : 0 ≤ g`
fails globally, independently of any ansatz. So the ratios and the measurement
agree that a crossing happens, and `hg0` is the odd one out — it is an
assumption, not a derived fact, and its status is local rather than global.

Nothing is withdrawn here either. r187's monotone branch remains a theorem about
the monotone case; what is corrected is the assumption that the monotone case is
the physical one.

## What is NOT claimed

Not claimed: that `z = 1/√5` is observationally confirmed; 1.57σ is not a
detection. Not claimed: that the golden-ratio pair is derived — it is an ansatz,
and this file is explicit that the result is conditional on it. Not claimed:
anything about physical spacetime beyond r219's own scope note. **No dataset
number appears in any statement** — the `0.40 ± 0.03` comparison is confined to
this header, matching r219's discipline.

The Binet remark below is flagged as suggestive and is not used in any proof.

## Addendum, 2026-10-30: this header overstated the agreement

The section above calls the `0.4472` vs `0.40 ± 0.03` comparison "a genuine
prediction/measurement pair". **That was checked on one component of the
measurement and not the other, and the full comparison is worse for the
ansatz.** Corrected here rather than by editing the claim away.

The same `g` inversion that locates the zero at `z ≈ 0.40` also yields
`g₀/H₀ ∈ [0.74, 1.05]`. Through r219's bridge at `a = 1`, `g₀/H₀ = 3(1 + w₀)`,
so the ansatz **requires** `g₀/H₀ = 3(2 − φ)/2 ≈ 0.5729` — below that interval's
floor. Equivalently the measured `g₀` implies `w₀ ∈ [−0.753, −0.650]`, and
`−φ/2 ≈ −0.8090` is below all of it. So the ansatz matches the measured zero's
*location* while missing the measured *amplitude*: it crosses `−1` in nearly the
right place with the wrong slope and offset. One agreeing component was reported
as if it were the whole comparison.

Worse for the ansatz, and found the same day: PF's **own action derivation**
(`codex/COSMOLOGY_DE_DERIVATION_2026-10-11.md`) reduces the ch08 action on its
derived `Q = 0` branch to exponential quintessence and proves
`w = (½φ̇² − V)/(½φ̇² + V) ≥ −1` — a register-A theorem that **forbids** phantom
crossing outright, with `w₀ ∈ [−0.99, −0.93]`. A crossing at `z = 1/√5` is
exactly what that theorem excludes. See r389, which records the arithmetic half.

**What survives from this file.** The closed forms are theorems and stand
unchanged: `a* = (3 − φ)/2` and `z* = 1/√5` are what the golden-ratio pair
*forces*, exactly, and the uniqueness result stands. What does not survive is the
reading of `1/√5` as an endorsed PF prediction in agreement with measurement. It
is the crossing redshift of an **ansatz that PF's own derived dynamics
excludes** — so the right use of `z* = 1/√5` is as the sharp consequence that
makes the ansatz falsifiable, and it is already in tension on two fronts.

## Three-axiom bar

Every top-level declaration prints `[propext, Classical.choice, Quot.sound]`.
No sorry, no native_decide, no project axioms.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 5 (1M context). 2026-10-29.
-/
import PF.Cosmology.SubstrateCPLPhantomCheck_r387

set_option autoImplicit false

namespace PrincipiaTractalis.Cosmology.SubstrateCPLCrossing

open PrincipiaTractalis.Priority4SubstrateDischarge
open PrincipiaTractalis.Cosmology.SubstrateCPLPhantomCheck

/-! ## §1 — `√5 = 2φ - 1`, and the crossing scale factor is in range -/

lemma sqrt_five_eq : Real.sqrt 5 = 2 * Real.goldenRatio - 1 := by
  simp only [Real.goldenRatio]
  ring

/-- The crossing scale factor, `a* = (3 - φ)/2`. -/
noncomputable def crossingScale : ℝ := (3 - Real.goldenRatio) / 2

lemma crossingScale_pos : 0 < crossingScale := by
  have h := Real.goldenRatio_lt_two
  unfold crossingScale
  linarith

lemma crossingScale_lt_one : crossingScale < 1 := by
  have h := Real.one_lt_goldenRatio
  unfold crossingScale
  linarith

/-! ## §2 — The crossing is at `a*`, and nowhere else -/

/-- **★★★ r388: the substrate CPL pair hits `w = -1` at `a* = (3-φ)/2` ★★★** -/
theorem substrate_cpl_crossing :
    substrate_w_0 + substrate_w_a * (1 - crossingScale) = -1 := by
  have hsq : Real.goldenRatio ^ 2 = Real.goldenRatio + 1 := Real.goldenRatio_sq
  unfold substrate_w_0 substrate_w_a crossingScale
  rw [one_div_goldenRatio]
  linear_combination (-1/2 : ℝ) * hsq

/-- The crossing is unique: `wₐ ≠ 0`, so the CPL line meets `-1` once. -/
theorem substrate_cpl_crossing_unique {a : ℝ}
    (h : substrate_w_0 + substrate_w_a * (1 - a) = -1) : a = crossingScale := by
  have hwa : substrate_w_a ≠ 0 := by
    have hpos : (0:ℝ) < Real.goldenRatio := Real.goldenRatio_pos
    unfold substrate_w_a
    have : 1 / Real.goldenRatio ≠ 0 := by positivity
    simpa using this
  have hc := substrate_cpl_crossing
  have : substrate_w_a * (1 - a) = substrate_w_a * (1 - crossingScale) := by
    linarith [h, hc]
  have := mul_left_cancel₀ hwa this
  linarith

/-! ## §3 — The crossing redshift is exactly `1/√5` -/

/-- **★★★ r388: `z* = 1/√5` ★★★**

The redshift of the crossing, `1/a* - 1`, is exactly `1/√5`. Exact, not
numerical: it consumes only `√5 = 2φ - 1` and `φ² = φ + 1`. -/
theorem substrate_cpl_crossing_redshift :
    1 / crossingScale - 1 = 1 / Real.sqrt 5 := by
  -- `Real.goldenRatio` is a reducible abbrev, so `ring` unfolds it back to √5.
  -- Work in √5 from the start rather than fighting that.
  have hcs : crossingScale = (5 - Real.sqrt 5) / 4 := by
    unfold crossingScale
    simp only [Real.goldenRatio]
    ring
  have hpos : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 5 < 5 := by nlinarith [hsq, hpos]
  have hne : Real.sqrt 5 ≠ 0 := ne_of_gt hpos
  have hd : (5:ℝ) - Real.sqrt 5 ≠ 0 := ne_of_gt (by linarith)
  rw [hcs]
  field_simp
  linear_combination hsq

/-- `1/√5` is the Binet normalisation of the Fibonacci closed form. Recorded as
a structural remark only — **suggestive, not derived**, and used in no proof. -/
theorem crossing_redshift_is_binet_prefactor :
    1 / crossingScale - 1 = 1 / (Real.goldenRatio - Real.goldenConj) := by
  rw [substrate_cpl_crossing_redshift, Real.goldenRatio_sub_goldenConj]

end PrincipiaTractalis.Cosmology.SubstrateCPLCrossing

/-! ## §Axiom check -/
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.sqrt_five_eq
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.crossingScale_pos
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.crossingScale_lt_one
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.substrate_cpl_crossing
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.substrate_cpl_crossing_unique
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.substrate_cpl_crossing_redshift
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.crossing_redshift_is_binet_prefactor

-- Axiom-check coverage completed 2026-10-30 (declarations the in-file check had omitted)
#print axioms PrincipiaTractalis.Cosmology.SubstrateCPLCrossing.crossingScale
