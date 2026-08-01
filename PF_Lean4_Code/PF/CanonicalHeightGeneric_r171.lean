/-
# PF.CanonicalHeightGeneric_r171

★★★ 2026-07-31 — THE CANONICAL HEIGHT, CURVE-INDEPENDENTLY ★★★

r147 built the canonical height for 389a1 and r156 rebuilt it for 5077a1.  The
two files differ only in constants.  Everything they prove needs **one** input:

> an abelian group `G`, a nonnegative `lognh : G → ℝ`, and a doubling window
> `|lognh (R+R) − 4·lognh R| ≤ log κ`.

No elliptic curve, no rationals, no naive height, no duplication map.  Given
that, the whole construction goes through:

  `hseq R n := lognh (2ⁿR)/4ⁿ` is Cauchy with geometric modulus `(log κ/4)·(1/4)ⁿ`
  ⟹ `ĥ(R) := lim hseq R` exists, and satisfies
      `ĥ ≥ 0`,  `ĥ(R+R) = 4ĥ(R)`,  `ĥ(2ⁿR) = 4ⁿĥ(R)`,
      `|ĥ(R) − lognh R| ≤ log κ / 3`,  `|ĥ(R) − hseq R n| ≤ log κ/(3·4ⁿ)`.

## What this replaces, and what it does not

It replaces the shared core of r147 and r156 — the Cauchy construction, the
doubling law, and both window forms.  Instantiating it for a new curve needs
only `lognh_dbl_window`, which for our curves is r145+r143 (resp. r146+r144)
through `Real.log`.

It does **not** replace the torsion characterisation (that needs Northcott for
ℚ and finiteness of the x-fibres, both genuinely curve-side), nor the
quasi-parallelogram bounds.

The existing r147 and r156 are left untouched: this file is additive, so nothing
already verified is put at risk.  New curves should use it.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PrincipiaTractalis.CanonicalHeightGeneric

open Filter Topology

variable {G : Type} [AddCommGroup G]

/-- The only input the construction needs. -/
structure HeightWindow (lognh : G → ℝ) (κ : ℝ) : Prop where
  nonneg : ∀ R, 0 ≤ lognh R
  one_le : (1 : ℝ) ≤ κ
  window : ∀ R, |lognh (R + R) - 4 * lognh R| ≤ Real.log κ

/-- The canonical-height approximant `log h(2ⁿR)/4ⁿ`. -/
noncomputable def hseq (lognh : G → ℝ) (R : G) (n : ℕ) : ℝ :=
  lognh (((2 : ℤ) ^ n) • R) / 4 ^ n

/-- The canonical height, as the limit of the approximants. -/
noncomputable def canheight (lognh : G → ℝ) (R : G) : ℝ :=
  limUnder atTop (hseq lognh R)

variable {lognh : G → ℝ} {κ : ℝ}

theorem log_kappa_nonneg (hw : HeightWindow lognh κ) : 0 ≤ Real.log κ :=
  Real.log_nonneg hw.one_le

theorem two_pow_succ_zsmul (R : G) (n : ℕ) :
    ((2 : ℤ) ^ (n + 1)) • R = ((2 : ℤ) ^ n) • R + ((2 : ℤ) ^ n) • R := by
  have h2 : ((2 : ℤ) ^ (n + 1)) = 2 ^ n + 2 ^ n := by ring
  rw [h2, add_zsmul]

theorem hseq_zero_eq (R : G) : hseq lognh R 0 = lognh R := by simp [hseq]

theorem hseq_nonneg (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    0 ≤ hseq lognh R n :=
  div_nonneg (hw.nonneg _) (by positivity)

/-- One-step estimate: `|hseq R (n+1) − hseq R n| ≤ log κ / 4ⁿ⁺¹`. -/
theorem hseq_step (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    |hseq lognh R (n + 1) - hseq lognh R n| ≤ Real.log κ / 4 ^ (n + 1) := by
  have key := hw.window (((2 : ℤ) ^ n) • R)
  rw [← two_pow_succ_zsmul R n] at key
  have h4pos : (0 : ℝ) < 4 ^ (n + 1) := by positivity
  have habs : ∀ L1 L0 : ℝ,
      L1 / 4 ^ (n + 1) - L0 / 4 ^ n = (L1 - 4 * L0) / 4 ^ (n + 1) := by
    intro L1 L0
    have h4 : ((4 : ℝ) ^ n) ≠ 0 := by positivity
    rw [pow_succ]; field_simp
  calc |hseq lognh R (n + 1) - hseq lognh R n|
      = |(lognh (((2 : ℤ) ^ (n + 1)) • R)
          - 4 * lognh (((2 : ℤ) ^ n) • R)) / 4 ^ (n + 1)| := by
        unfold hseq; rw [habs]
    _ = |lognh (((2 : ℤ) ^ (n + 1)) • R)
          - 4 * lognh (((2 : ℤ) ^ n) • R)| / 4 ^ (n + 1) := by
        rw [abs_div, abs_of_pos h4pos]
    _ ≤ Real.log κ / 4 ^ (n + 1) := by gcongr

theorem hseq_dist_step (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    dist (hseq lognh R n) (hseq lognh R (n + 1))
      ≤ Real.log κ / 4 * (1 / 4) ^ n := by
  rw [Real.dist_eq, abs_sub_comm]
  calc |hseq lognh R (n + 1) - hseq lognh R n|
      ≤ Real.log κ / 4 ^ (n + 1) := hseq_step hw R n
    _ = Real.log κ / 4 * (1 / 4) ^ n := by
        rw [div_pow, one_pow, div_mul_div_comm, mul_one, ← pow_succ']

theorem hseq_cauchySeq (hw : HeightWindow lognh κ) (R : G) :
    CauchySeq (hseq lognh R) :=
  cauchySeq_of_le_geometric (1 / 4) (Real.log κ / 4) (by norm_num)
    (hseq_dist_step hw R)

theorem tendsto_hseq (hw : HeightWindow lognh κ) (R : G) :
    Tendsto (hseq lognh R) atTop (𝓝 (canheight lognh R)) :=
  (hseq_cauchySeq hw R).tendsto_limUnder

theorem canheight_nonneg (hw : HeightWindow lognh κ) (R : G) :
    0 ≤ canheight lognh R :=
  ge_of_tendsto' (tendsto_hseq hw R) (hseq_nonneg hw R)

theorem hseq_add_self (R : G) (n : ℕ) :
    hseq lognh (R + R) n = 4 * hseq lognh R (n + 1) := by
  have hsm : ((2 : ℤ) ^ n) • (R + R) = ((2 : ℤ) ^ (n + 1)) • R := by
    rw [← two_zsmul, ← mul_zsmul, ← pow_succ]
  unfold hseq
  rw [hsm]
  generalize lognh (((2 : ℤ) ^ (n + 1)) • R) = L
  have h4 : ((4 : ℝ) ^ n) ≠ 0 := by positivity
  rw [pow_succ]; field_simp

/-- **The doubling law**: `ĥ(R+R) = 4·ĥ(R)`. -/
theorem canheight_dbl (hw : HeightWindow lognh κ) (R : G) :
    canheight lognh (R + R) = 4 * canheight lognh R := by
  have h1 : Tendsto (fun n : ℕ => hseq lognh R (n + 1)) atTop
      (𝓝 (canheight lognh R)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_hseq hw R)
  have h2 : Tendsto (hseq lognh (R + R)) atTop (𝓝 (4 * canheight lognh R)) := by
    have hmul := h1.const_mul (4 : ℝ)
    simpa only [← hseq_add_self] using hmul
  exact tendsto_nhds_unique (tendsto_hseq hw (R + R)) h2

/-- **The window**: `|ĥ(R) − lognh R| ≤ log κ / 3`. -/
theorem canheight_window (hw : HeightWindow lognh κ) (R : G) :
    |canheight lognh R - lognh R| ≤ Real.log κ / 3 := by
  have hd := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (Real.log κ / 4)
    (by norm_num) (hseq_dist_step hw R) (tendsto_hseq hw R)
  rw [Real.dist_eq, hseq_zero_eq] at hd
  have hconst : Real.log κ / 4 / (1 - 1 / 4) = Real.log κ / 3 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, div_div]; norm_num
  rw [hconst] at hd
  calc |canheight lognh R - lognh R| = |lognh R - canheight lognh R| :=
        abs_sub_comm _ _
    _ ≤ Real.log κ / 3 := hd

/-- Iterated doubling: `ĥ(2ⁿR) = 4ⁿ·ĥ(R)`. -/
theorem canheight_two_pow (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    canheight lognh (((2 : ℤ) ^ n) • R) = 4 ^ n * canheight lognh R := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [two_pow_succ_zsmul, canheight_dbl hw, ih, pow_succ]; ring

/-- **The shifted window**: `|ĥ(R) − hseq R n| ≤ log κ / (3·4ⁿ)`. -/
theorem canheight_window_shift (hw : HeightWindow lognh κ) (R : G) (n : ℕ) :
    |canheight lognh R - hseq lognh R n| ≤ Real.log κ / 3 / 4 ^ n := by
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have hwin := canheight_window hw (((2 : ℤ) ^ n) • R)
  rw [canheight_two_pow hw R n] at hwin
  have hkey : 4 ^ n * |canheight lognh R - hseq lognh R n| ≤ Real.log κ / 3 := by
    have e : (4 : ℝ) ^ n * (canheight lognh R - hseq lognh R n)
        = 4 ^ n * canheight lognh R - lognh (((2 : ℤ) ^ n) • R) := by
      simp only [hseq]; field_simp
    calc 4 ^ n * |canheight lognh R - hseq lognh R n|
        = |(4 : ℝ) ^ n * (canheight lognh R - hseq lognh R n)| := by
          rw [abs_mul, abs_of_pos h4]
      _ = |4 ^ n * canheight lognh R - lognh (((2 : ℤ) ^ n) • R)| := by rw [e]
      _ ≤ Real.log κ / 3 := hwin
  rw [le_div_iff₀ h4]
  calc |canheight lognh R - hseq lognh R n| * 4 ^ n
      = 4 ^ n * |canheight lognh R - hseq lognh R n| := by ring
    _ ≤ Real.log κ / 3 := hkey

end PrincipiaTractalis.CanonicalHeightGeneric

#print axioms PrincipiaTractalis.CanonicalHeightGeneric.hseq_cauchySeq
#print axioms PrincipiaTractalis.CanonicalHeightGeneric.canheight_dbl
#print axioms PrincipiaTractalis.CanonicalHeightGeneric.canheight_window
#print axioms PrincipiaTractalis.CanonicalHeightGeneric.canheight_two_pow
#print axioms PrincipiaTractalis.CanonicalHeightGeneric.canheight_window_shift
