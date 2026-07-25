/-
# PF.Analytic.XiThetaIntegral

★★★★★ 2026-07-25 — Hardy route milestone B3 (HARDY_SCOPING_2026-07-24 §3,
INTERVAL_SPIKE_2026-07-24): the EXPLICIT symmetric theta-integral
representation of the completed Riemann zeta, kernel-clean, on ALL of ℂ,
with its critical-line specialisation to a manifestly REAL integrand for
the witness function `Xi` of PF.Analytic.XiRealWitness.

## Goal

Route B needs to certify `Xi 14 < 0 < Xi 15` numerically.  For that the
abstract Mellin-transform definition of `Λ = completedRiemannZeta` must
be traded for a CONCRETE integral over `[1, ∞)` with exponentially
decaying integrand.  This file proves the classical Riemann 1859
symmetric representation, with

  `ω u = ∑' n : ℕ, exp (-π (n+1)² u)`   (the Jacobi theta tail),

as a chain of kernel-clean theorems:

  1. **`ω` and its bridge to mathlib's theta kernels** —
       `omega`, `hasSum_omega`, `evenKernel_zero_eq`
       (`evenKernel 0 u = 1 + 2 ω u`, via `hasSum_nat_cosKernel₀`);
     elementary facts for the later quadrature milestones:
       `omega_nonneg`, `omega_pos`, `omega_antitone`,
       `omega_le_geometric` (`ω u ≤ e^{-πu}/(1-e^{-πu})`, the same
       quality as mathlib's `norm_jacobiTheta_sub_one_le`),
       `continuousOn_omega`.

  2. **The Mellin split and theta inversion** — mathlib defines
     `Λ₀(s) = mellin f_modif (s/2) / 2` where `f_modif` is the
     piecewise-modified even theta kernel of the FE-pair machinery
     (`hurwitzEvenFEPair 0`, `WeakFEPair.f_modif`).  We split the Mellin
     integral at `u = 1` (`mellin_f_modif_split`) and fold the `(0,1)`
     piece onto `(1,∞)` by the substitution `u ↦ 1/u` together with the
     theta modular transformation `evenKernel_functional_equation`
     (`mellin_f_modif_inversion` — implemented via `mellin_comp_rpow`
     at exponent `-1`, so NO bespoke change-of-variables is needed).

  3. **★ The symmetric representation, valid for EVERY `s : ℂ` ★**
       `completedRiemannZeta₀_eq_theta_integral` :
         `Λ₀(s) = ∫_{u>1} (u^{s/2-1} + u^{(1-s)/2-1}) · ω u du`
       `completedRiemannZeta_eq_theta_integral` :
         `Λ(s) = -1/s - 1/(1-s) + ∫_{u>1} (u^{s/2-1} + u^{(1-s)/2-1}) · ω u du`
     No analytic continuation argument is needed: `f_modif` decays
     rapidly at BOTH ends, so the split Mellin integral converges for
     all `s` (`StrongFEPair.hasMellin`), and the identity is exact.

  4. **Critical-line specialisation** — at `s = ⟨1/2, t⟩` the two
     `cpow` exponents are complex conjugates (`critical_exponent_conj`)
     and the pole terms collapse to the real constant `-1/(1/4+t²)`
     (`pole_term_critical`), giving the manifestly real integrand
       `u^{s/2-1} + u^{(1-s)/2-1} = 2 u^{-3/4} cos((t/2) log u)`
     (`critical_integrand_eq`) and the B3 target formula
       **`Xi_eq_theta_integral`** :
         `Xi t = -1/(1/4+t²) + ∫_{u>1} 2 u^{-3/4} cos((t/2) log u) · ω u du`
     together with `integrableOn_Xi_theta_integrand` and the tail-bound
     workhorse `Xi_theta_integrand_abs_le`
     (`|integrand| ≤ 2 e^{-πu}/(1-e^{-π})` for `u ≥ 1`).

## Brick value

The single remaining RH bucket-1 atom is now reduced to certifying the
SIGN of an explicit real integral of an elementary integrand
(`exp`/`cos`/`rpow`/geometric series) — exactly the objects the vendored
interval engine evaluates (INTERVAL_SPIKE_2026-07-24 §API fit).  What
remains for Route B is pure quadrature engineering (B4/B5): a verified
composite rule on `[1, T]` plus the tail bound proved here.

## Axiom budget

Zero project axioms, zero sorries.  Theorems depend only on
`[propext, Classical.choice, Quot.sound]`.
-/

import PF.Analytic.XiRealWitness
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform

namespace PrincipiaTractalis.XiThetaIntegral

open Complex Set MeasureTheory HurwitzZeta
open PrincipiaTractalis.XiRealWitness
open scoped Real ComplexConjugate

/-! ## §1 — The Jacobi theta tail `ω` -/

/-- **`omega`** — the Jacobi theta tail `ω(u) = ∑_{n ≥ 1} e^{-π n² u}`,
    indexed here by `n : ℕ` as `n + 1`.  For `u > 0` this is the
    convergent positive series of Riemann 1859; for `u ≤ 0` the series
    diverges and the `tsum` junk value is `0`. -/
noncomputable def omega (u : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)

/-- The `ω` series is summable for `u > 0` (from mathlib's
    `hasSum_nat_cosKernel₀` at parameter `a = 0`). -/
theorem summable_omega {u : ℝ} (hu : 0 < u) :
    Summable fun n : ℕ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) := by
  have h := hasSum_nat_cosKernel₀ 0 hu
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one] at h
  exact (h.summable.div_const 2).congr fun n ↦ by ring

theorem hasSum_omega {u : ℝ} (hu : 0 < u) :
    HasSum (fun n : ℕ ↦ Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u)) (omega u) :=
  (summable_omega hu).hasSum

/-- Bridge to mathlib's cosine theta kernel: `cosKernel 0 u - 1 = 2 ω u`. -/
theorem cosKernel_zero_sub_one {u : ℝ} (hu : 0 < u) :
    cosKernel 0 u - 1 = 2 * omega u := by
  have h := hasSum_nat_cosKernel₀ 0 hu
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one, AddCircle.coe_zero] at h
  exact h.unique ((hasSum_omega hu).mul_left 2)

/-- **Bridge to mathlib's even theta kernel** — the object whose Mellin
    transform mathlib DEFINES `completedRiemannZeta` by:
    `evenKernel 0 u = θ(iu) = 1 + 2 ω u` for `u > 0`. -/
theorem evenKernel_zero_eq {u : ℝ} (hu : 0 < u) :
    evenKernel 0 u = 1 + 2 * omega u := by
  have h := cosKernel_zero_sub_one hu
  rw [evenKernel_eq_cosKernel_of_zero]
  linarith

/-- `ω ≥ 0` everywhere (including the junk region `u ≤ 0`). -/
theorem omega_nonneg (u : ℝ) : 0 ≤ omega u :=
  tsum_nonneg fun _ ↦ (Real.exp_pos _).le

/-- `ω > 0` on the positive axis. -/
theorem omega_pos {u : ℝ} (hu : 0 < u) : 0 < omega u :=
  lt_of_lt_of_le (Real.exp_pos _)
    ((summable_omega hu).le_tsum 0 fun _ _ ↦ (Real.exp_pos _).le)

/-- `ω` is decreasing on the positive axis. -/
theorem omega_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : omega v ≤ omega u := by
  refine (summable_omega (hu.trans_le huv)).tsum_le_tsum (fun n ↦ ?_) (summable_omega hu)
  refine Real.exp_le_exp.mpr ?_
  have hn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_nonneg.mpr huv)]

/-- **Geometric tail bound** for `ω` — the quantitative fact the
    quadrature milestone B4 truncates with (same quality as mathlib's
    `norm_jacobiTheta_sub_one_le`): `ω u ≤ e^{-πu} / (1 - e^{-πu})`. -/
theorem omega_le_geometric {u : ℝ} (hu : 0 < u) :
    omega u ≤ Real.exp (-π * u) / (1 - Real.exp (-π * u)) := by
  have hr0 : 0 < Real.exp (-π * u) := Real.exp_pos _
  have hr1 : Real.exp (-π * u) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hgeom : Summable fun n : ℕ ↦ Real.exp (-π * u) ^ n * Real.exp (-π * u) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_right _
  have hterm : ∀ n : ℕ,
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 * u) ≤ Real.exp (-π * u) ^ n * Real.exp (-π * u) := by
    intro n
    have hc : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h2 : Real.exp (-π * u) ^ n * Real.exp (-π * u)
        = Real.exp (((n : ℝ) + 1) * (-π * u)) := by
      rw [← pow_succ, ← Real.exp_nat_mul, Nat.cast_add_one]
    rw [h2]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg Real.pi_pos.le hu.le)]
  calc omega u ≤ ∑' n : ℕ, Real.exp (-π * u) ^ n * Real.exp (-π * u) :=
        (summable_omega hu).tsum_le_tsum hterm hgeom
    _ = (1 - Real.exp (-π * u))⁻¹ * Real.exp (-π * u) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hr0.le hr1]
    _ = Real.exp (-π * u) / (1 - Real.exp (-π * u)) := by rw [inv_mul_eq_div]

/-- `ω` is continuous on the positive axis (via mathlib's
    `continuousOn_cosKernel`). -/
theorem continuousOn_omega : ContinuousOn omega (Ioi 0) := by
  have h : ContinuousOn (fun u : ℝ ↦ (cosKernel 0 u - 1) / 2) (Ioi 0) :=
    ((continuousOn_cosKernel 0).sub continuousOn_const).div_const 2
  refine h.congr fun u hu ↦ ?_
  have h2 := cosKernel_zero_sub_one (mem_Ioi.mp hu)
  linarith

/-! ## §2 — Projections of mathlib's FE-pair `hurwitzEvenFEPair 0`

    `completedRiemannZeta₀ s` is BY DEFINITION
    `mellin (hurwitzEvenFEPair 0).f_modif (s/2) / 2`, where `f_modif`
    is the even theta kernel minus its constant term on `(1,∞)` and
    minus its `u^{-1/2}` blow-up on `(0,1)`.  We record the field
    values of the pair and evaluate `f_modif` piecewise. -/

theorem P_f_apply (x : ℝ) : (hurwitzEvenFEPair 0).f x = ((evenKernel 0 x : ℝ) : ℂ) := rfl

theorem P_k : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl

theorem P_ε : (hurwitzEvenFEPair 0).ε = 1 := rfl

theorem P_g₀ : (hurwitzEvenFEPair 0).g₀ = 1 := rfl

theorem P_f₀ : (hurwitzEvenFEPair 0).f₀ = 1 :=
  show (if (0 : UnitAddCircle) = 0 then (1 : ℂ) else 0) = 1 from if_pos rfl

/-- On `(1, ∞)` the modified kernel is `θ - 1`. -/
theorem f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    (hurwitzEvenFEPair 0).f_modif x = ((evenKernel 0 x : ℝ) : ℂ) - 1 := by
  simp only [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (notMem_Ioo_of_ge hx.le), add_zero, P_f_apply, P_f₀]

/-- On `(0, 1)` the modified kernel is `θ - u^{-1/2}`. -/
theorem f_modif_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (hurwitzEvenFEPair 0).f_modif x
      = ((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  simp only [WeakFEPair.f_modif, Pi.add_apply,
    indicator_of_notMem (notMem_Ioi.mpr hx.2.le), indicator_of_mem hx, zero_add,
    P_f_apply, P_ε, P_k, P_g₀, one_mul, smul_eq_mul, mul_one]

/-- At the joint `x = 1` the modified kernel vanishes. -/
theorem f_modif_one : (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
  simp [WeakFEPair.f_modif]

/-- **Integrability of the `(1,∞)` theta integrand for EVERY complex
    exponent** — extracted from the all-`s` convergence of the strong
    FE-pair's Mellin transform (`StrongFEPair.hasMellin`).  This is
    what makes the symmetric representation valid on ALL of ℂ with no
    analytic-continuation argument. -/
theorem integrableOn_cpow_smul_evenKernel_sub_one (w : ℂ) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ w • (((evenKernel 0 x : ℝ) : ℂ) - 1)) (Ioi 1) := by
  have h : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (w + 1 - 1) • (hurwitzEvenFEPair 0).f_modif x) (Ioi 0) :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (w + 1)).1
  refine (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [show w + 1 - 1 = w from by ring, f_modif_of_one_lt (mem_Ioi.mp hx)]

/-! ## §3 — Splitting the Mellin integral at `u = 1` -/

/-- **The Mellin split**: for every `σ : ℂ`,
    `mellin f_modif σ = ∫_{u>1} u^{σ-1}(θ(u)-1) du
                       + ∫_{0<u<1} u^{σ-1}(θ(u)-u^{-1/2}) du`. -/
theorem mellin_f_modif_split (σ : ℂ) :
    mellin (hurwitzEvenFEPair 0).f_modif σ
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (σ - 1) • (((evenKernel 0 x : ℝ) : ℂ) - 1))
        + ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (σ - 1) •
            (((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) := by
  have hconv : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (σ - 1) • (hurwitzEvenFEPair 0).f_modif x) (Ioi 0) :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin σ).1
  have h1 : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (σ - 1) • (((evenKernel 0 x : ℝ) : ℂ) - 1)) (Ioi 1) :=
    (hconv.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun
      (fun x hx ↦ by rw [f_modif_of_one_lt (mem_Ioi.mp hx)]) measurableSet_Ioi
  have h2 : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (σ - 1) •
        (((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) (Ioo 0 1) :=
    (hconv.mono_set Ioo_subset_Ioi_self).congr_fun
      (fun x hx ↦ by rw [f_modif_of_mem_Ioo hx]) measurableSet_Ioo
  have hi1 : Integrable
      ((Ioi (1 : ℝ)).indicator fun y : ℝ ↦
        (y : ℂ) ^ (σ - 1) • (((evenKernel 0 y : ℝ) : ℂ) - 1))
      (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Ioi).mpr h1).restrict
  have hi2 : Integrable
      ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
        (y : ℂ) ^ (σ - 1) • (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)))
      (volume.restrict (Ioi 0)) :=
    ((integrable_indicator_iff measurableSet_Ioo).mpr h2).restrict
  have key : EqOn (fun x : ℝ ↦ (x : ℂ) ^ (σ - 1) • (hurwitzEvenFEPair 0).f_modif x)
      (fun x : ℝ ↦
        (Ioi (1 : ℝ)).indicator
          (fun y : ℝ ↦ (y : ℂ) ^ (σ - 1) • (((evenKernel 0 y : ℝ) : ℂ) - 1)) x
        + (Ioo (0 : ℝ) 1).indicator
            (fun y : ℝ ↦ (y : ℂ) ^ (σ - 1) •
              (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) x)
      (Ioi 0) := by
    intro x (hx : 0 < x)
    rcases lt_trichotomy 1 x with hx1 | rfl | hx1
    · simp only [indicator_of_mem (mem_Ioi.mpr hx1),
        indicator_of_notMem (notMem_Ioo_of_ge hx1.le), add_zero, f_modif_of_one_lt hx1]
    · simp only [f_modif_one, smul_zero, indicator_of_notMem notMem_Ioi_self,
        indicator_of_notMem (notMem_Ioo_of_ge le_rfl), add_zero]
    · have hmem : x ∈ Ioo (0 : ℝ) 1 := ⟨hx, hx1⟩
      simp only [indicator_of_notMem (notMem_Ioi.mpr hx1.le), indicator_of_mem hmem,
        zero_add, f_modif_of_mem_Ioo hmem]
  simp only [mellin]
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_add hi1 hi2,
    setIntegral_indicator measurableSet_Ioi, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one), inter_eq_right.mpr Ioo_subset_Ioi_self]

/-! ## §4 — Theta inversion: folding `(0,1)` onto `(1,∞)` -/

/-- **Theta inversion**: the substitution `u ↦ 1/u` (via
    `mellin_comp_rpow` at exponent `-1`) together with the modular
    transformation `θ(1/u) = u^{1/2} θ(u)`
    (`evenKernel_functional_equation`) folds the `(0,1)` piece of the
    split onto `(1,∞)`:
    `∫_{0<u<1} u^{σ-1}(θ(u)-u^{-1/2}) du = ∫_{u>1} u^{-σ-1/2}(θ(u)-1) du`. -/
theorem mellin_f_modif_inversion (σ : ℂ) :
    (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (σ - 1) •
        (((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)))
      = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-σ - 1 / 2) • (((evenKernel 0 x : ℝ) : ℂ) - 1) := by
  have h1 : mellin ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
        (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) σ
      = ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (σ - 1) •
          (((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) := by
    simp only [mellin]
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := (Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
        (y : ℂ) ^ (σ - 1) •
          (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ?_]
    · rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self]
    · intro x _
      by_cases hmem : x ∈ Ioo (0 : ℝ) 1
      · simp only [indicator_of_mem hmem]
      · simp only [indicator_of_notMem hmem, smul_zero]
  have h2 := mellin_comp_rpow ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
    (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) (-σ) (-1)
  simp only [abs_neg, abs_one, inv_one, one_smul, Complex.ofReal_neg, Complex.ofReal_one,
    neg_div_neg_eq, div_one] at h2
  have h3 : mellin (fun t : ℝ ↦ ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
        (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) (t ^ (-1 : ℝ))) (-σ)
      = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-σ - 1 / 2) • (((evenKernel 0 x : ℝ) : ℂ) - 1) := by
    simp only [mellin]
    rw [setIntegral_congr_fun measurableSet_Ioi
      (g := (Ioi (1 : ℝ)).indicator fun y : ℝ ↦
        (y : ℂ) ^ (-σ - 1 / 2) • (((evenKernel 0 y : ℝ) : ℂ) - 1)) ?_]
    · rw [setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
    · intro t (ht : 0 < t)
      have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      simp only [Real.rpow_neg_one]
      rcases lt_or_ge 1 t with ht1 | ht1
      · -- `t > 1`: apply the theta modular transformation
        have hti : t⁻¹ ∈ Ioo (0 : ℝ) 1 := ⟨inv_pos.mpr (by positivity),
          inv_lt_one_of_one_lt₀ ht1⟩
        have hpow : (0 : ℝ) < t ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht _
        have hk : evenKernel 0 t⁻¹ = t ^ ((1 : ℝ) / 2) * evenKernel 0 t := by
          have hfe := evenKernel_functional_equation 0 t
          rw [← evenKernel_eq_cosKernel_of_zero, one_div] at hfe
          rw [hfe]
          field_simp
        have hp : (t⁻¹ : ℝ) ^ (-(1 / 2) : ℝ) = t ^ ((1 : ℝ) / 2) := by
          rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_neg]
        have hXX : (t : ℂ) ^ (-σ - 1) * (t : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)
            = (t : ℂ) ^ (-σ - 1 / 2) := by
          rw [← cpow_add _ _ htC]
          congr 1
          push_cast
          ring
        simp only [indicator_of_mem hti, indicator_of_mem (mem_Ioi.mpr ht1)]
        rw [hk, hp, Complex.ofReal_mul, Complex.ofReal_cpow ht.le]
        simp only [smul_eq_mul]
        calc (t : ℂ) ^ (-σ - 1) *
              ((t : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) * ((evenKernel 0 t : ℝ) : ℂ)
                - (t : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ))
            = ((t : ℂ) ^ (-σ - 1) * (t : ℂ) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)) *
              (((evenKernel 0 t : ℝ) : ℂ) - 1) := by ring
          _ = (t : ℂ) ^ (-σ - 1 / 2) * (((evenKernel 0 t : ℝ) : ℂ) - 1) := by rw [hXX]
      · -- `0 < t ≤ 1`: both sides vanish
        have hinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
        rw [indicator_of_notMem (fun hmem ↦ absurd hmem.2 (not_lt.mpr hinv)),
          indicator_of_notMem (notMem_Ioi.mpr ht1), smul_zero]
  calc (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (σ - 1) •
          (((evenKernel 0 x : ℝ) : ℂ) - ((x ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)))
      = mellin ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
          (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) σ := h1.symm
    _ = mellin (fun t : ℝ ↦ ((Ioo (0 : ℝ) 1).indicator fun y : ℝ ↦
          (((evenKernel 0 y : ℝ) : ℂ) - ((y ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) (t ^ (-1 : ℝ)))
          (-σ) := h2.symm
    _ = _ := h3

/-! ## §5 — ★ The symmetric theta-integral representation on ALL of ℂ ★ -/

/-- **★★★★★ RIEMANN'S SYMMETRIC REPRESENTATION (entire part) ★★★★★** —
    for EVERY `s : ℂ`:
    `Λ₀(s) = ∫_{u>1} (u^{s/2-1} + u^{(1-s)/2-1}) · ω(u) du`. -/
theorem completedRiemannZeta₀_eq_theta_integral (s : ℂ) :
    completedRiemannZeta₀ s
      = ∫ x in Ioi (1 : ℝ),
          ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * ((omega x : ℝ) : ℂ) := by
  have hL : completedRiemannZeta₀ s = mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := rfl
  have hint1 := integrableOn_cpow_smul_evenKernel_sub_one (s / 2 - 1)
  have hint2 := integrableOn_cpow_smul_evenKernel_sub_one (-(s / 2) - 1 / 2)
  rw [hL, mellin_f_modif_split (s / 2), mellin_f_modif_inversion (s / 2),
    ← integral_add hint1 hint2, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one (mem_Ioi.mp hx)
  rw [show ((1 : ℂ) - s) / 2 - 1 = -(s / 2) - 1 / 2 from by ring, evenKernel_zero_eq hx0]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- **★★★★★ RIEMANN'S SYMMETRIC REPRESENTATION ★★★★★** — for EVERY
    `s : ℂ` (poles included, under mathlib's `1/0 = 0` convention):
    `Λ(s) = -1/s - 1/(1-s) + ∫_{u>1} (u^{s/2-1} + u^{(1-s)/2-1}) · ω(u) du`. -/
theorem completedRiemannZeta_eq_theta_integral (s : ℂ) :
    completedRiemannZeta s
      = -(1 / s) - 1 / (1 - s)
        + ∫ x in Ioi (1 : ℝ),
            ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * ((omega x : ℝ) : ℂ) := by
  rw [completedRiemannZeta_eq, completedRiemannZeta₀_eq_theta_integral]
  ring

/-! ## §6 — Critical-line specialisation: the REAL integrand -/

/-- `conj` passes through `u ^ w` for a nonnegative real base `u` (off
    the branch cut). -/
theorem ofReal_cpow_conj {u : ℝ} (hu : 0 ≤ u) (w : ℂ) :
    (u : ℂ) ^ (conj w) = conj ((u : ℂ) ^ w) := by
  have harg : (u : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hu]
    exact Ne.symm Real.pi_ne_zero
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- On the critical line the two exponents of the symmetric integrand
    are complex conjugates: `(1-s)/2 - 1 = conj (s/2 - 1)` at
    `s = ⟨1/2, t⟩`. -/
theorem critical_exponent_conj (t : ℝ) :
    (1 - (⟨1 / 2, t⟩ : ℂ)) / 2 - 1 = conj ((⟨1 / 2, t⟩ : ℂ) / 2 - 1) := by
  rw [map_sub, map_div₀, map_one, map_ofNat, conj_critical_point]

/-- The real part of the critical-line power:
    `Re (u^{s/2-1}) = u^{-3/4} cos((t/2) log u)` at `s = ⟨1/2, t⟩`. -/
theorem cpow_critical_re {u : ℝ} (hu : 0 < u) (t : ℝ) :
    ((u : ℂ) ^ ((⟨1 / 2, t⟩ : ℂ) / 2 - 1)).re
      = u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hwre : ((⟨1 / 2, t⟩ : ℂ) / 2 - 1).re = -(3 / 4) := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    norm_num
  have hwim : ((⟨1 / 2, t⟩ : ℂ) / 2 - 1).im = t / 2 := by
    simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im]
    norm_num
  rw [cpow_def_of_ne_zero hu0, ← Complex.ofReal_log hu.le, Complex.exp_re,
    re_ofReal_mul, im_ofReal_mul, hwre, hwim, Real.rpow_def_of_pos hu,
    mul_comm (Real.log u) (t / 2)]

/-- **The critical-line integrand is manifestly REAL**:
    `u^{s/2-1} + u^{(1-s)/2-1} = 2 u^{-3/4} cos((t/2) log u)` at
    `s = ⟨1/2, t⟩`, for `u > 0`. -/
theorem critical_integrand_eq {u : ℝ} (hu : 0 < u) (t : ℝ) :
    (u : ℂ) ^ ((⟨1 / 2, t⟩ : ℂ) / 2 - 1) + (u : ℂ) ^ ((1 - (⟨1 / 2, t⟩ : ℂ)) / 2 - 1)
      = ((2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) : ℝ) : ℂ) := by
  rw [critical_exponent_conj, ofReal_cpow_conj hu.le, Complex.add_conj, cpow_critical_re hu]
  push_cast
  ring

/-- The pole terms collapse to the REAL constant `-1/(1/4 + t²)` on the
    critical line (since `1 - s = conj s` there). -/
theorem pole_term_critical (t : ℝ) :
    -(1 / (⟨1 / 2, t⟩ : ℂ)) - 1 / (1 - (⟨1 / 2, t⟩ : ℂ))
      = ((-(1 / (1 / 4 + t ^ 2)) : ℝ) : ℂ) := by
  have hs0 : (⟨1 / 2, t⟩ : ℂ) ≠ 0 := critical_point_ne_zero t
  have hcs0 : conj (⟨1 / 2, t⟩ : ℂ) ≠ 0 := by
    rw [starRingEnd_apply]
    exact star_ne_zero.mpr hs0
  have hc : (1 : ℂ) - (⟨1 / 2, t⟩ : ℂ) = conj (⟨1 / 2, t⟩ : ℂ) := (conj_critical_point t).symm
  have hns : (⟨1 / 2, t⟩ : ℂ) * conj (⟨1 / 2, t⟩ : ℂ) = ((1 / 4 + t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj]
    norm_cast
    rw [Complex.normSq_mk]
    ring
  have hadd : (⟨1 / 2, t⟩ : ℂ) + conj (⟨1 / 2, t⟩ : ℂ) = 1 := by
    rw [Complex.add_conj]
    norm_num
  have key : -(1 / (⟨1 / 2, t⟩ : ℂ)) - 1 / conj (⟨1 / 2, t⟩ : ℂ)
      = -(((⟨1 / 2, t⟩ : ℂ) + conj (⟨1 / 2, t⟩ : ℂ))
          / ((⟨1 / 2, t⟩ : ℂ) * conj (⟨1 / 2, t⟩ : ℂ))) := by
    field_simp
    ring
  have hden : ((1 / 4 + t ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  rw [hc, key, hadd, hns]
  push_cast
  ring

/-- **★★★★★ THE B3 TARGET FORMULA ★★★★★** — the real witness function
    of PF.Analytic.XiRealWitness as an explicit real integral:

    `Xi t = -1/(1/4 + t²) + ∫_{u>1} 2 u^{-3/4} cos((t/2) log u) · ω(u) du`.

    Everything on the right is elementary (`rpow`, `cos`, `log`, and
    the geometrically-dominated series `ω`) — exactly the objects the
    Route B interval engine certifies.  Milestones B4/B5 evaluate this
    at `t = 14, 15` to bracket the first on-line zeta zero. -/
theorem Xi_eq_theta_integral (t : ℝ) :
    Xi t = -(1 / (1 / 4 + t ^ 2))
      + ∫ u in Ioi (1 : ℝ), 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u := by
  have h := completedRiemannZeta_eq_theta_integral (⟨1 / 2, t⟩ : ℂ)
  rw [Xi_eq t, pole_term_critical t] at h
  have hInt : (∫ x in Ioi (1 : ℝ),
        ((x : ℂ) ^ ((⟨1 / 2, t⟩ : ℂ) / 2 - 1) + (x : ℂ) ^ ((1 - (⟨1 / 2, t⟩ : ℂ)) / 2 - 1))
          * ((omega x : ℝ) : ℂ))
      = ((∫ u in Ioi (1 : ℝ),
          2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    rw [critical_integrand_eq hu0 t, ← Complex.ofReal_mul]
  rw [hInt, ← Complex.ofReal_add] at h
  exact_mod_cast h

/-- The critical-line integrand is integrable on `(1, ∞)` — the
    convergence certificate the quadrature milestone splits into
    `[1, T]` + tail. -/
theorem integrableOn_Xi_theta_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ 2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u)
      (Ioi 1) := by
  have h1 := integrableOn_cpow_smul_evenKernel_sub_one ((⟨1 / 2, t⟩ : ℂ) / 2 - 1)
  have h2 := integrableOn_cpow_smul_evenKernel_sub_one ((1 - (⟨1 / 2, t⟩ : ℂ)) / 2 - 1)
  have hC : IntegrableOn
      (fun u : ℝ ↦
        ((2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u : ℝ) : ℂ))
      (Ioi 1) := by
    refine IntegrableOn.congr_fun ((h1.add h2).div_const 2) (fun u hu ↦ ?_) measurableSet_Ioi
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    simp only [Pi.add_apply]
    rw [show ((2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u : ℝ) : ℂ)
        = ((2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) : ℝ) : ℂ)
            * ((omega u : ℝ) : ℂ) from by push_cast; ring,
      ← critical_integrand_eq hu0 t, evenKernel_zero_eq hu0]
    simp only [smul_eq_mul]
    push_cast
    ring
  refine IntegrableOn.congr_fun hC.re (fun u _ ↦ ?_) measurableSet_Ioi
  simp only [RCLike.re_to_complex, Complex.ofReal_re]

/-- **Tail-bound workhorse for B4/B5**: on `[1, ∞)` the critical-line
    integrand is dominated by `2 e^{-πu} / (1 - e^{-π})`, uniformly in
    `t` — truncating the integral at `u = T` costs at most
    `(2/π) e^{-πT} / (1 - e^{-π})`. -/
theorem Xi_theta_integrand_abs_le {u : ℝ} (hu : 1 ≤ u) (t : ℝ) :
    |2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
      ≤ 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hω : 0 ≤ omega u := omega_nonneg u
  have hrp : 0 < u ^ (-(3 / 4) : ℝ) := Real.rpow_pos_of_pos hu0 _
  have hcos : |Real.cos (t / 2 * Real.log u)| ≤ 1 := Real.abs_cos_le_one _
  have hle1 : u ^ (-(3 / 4) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
  have hexp1 : Real.exp (-π * u) ≤ Real.exp (-π) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hd1 : 0 < 1 - Real.exp (-π) := by
    have : Real.exp (-π) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have hd2 : 0 < 1 - Real.exp (-π * u) := by
    have : Real.exp (-π * u) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    linarith
  have habs : |2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
      ≤ 2 * omega u := by
    have h₁ : |2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
        = 2 * u ^ (-(3 / 4) : ℝ) * |Real.cos (t / 2 * Real.log u)| * omega u := by
      rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hrp, abs_of_nonneg hω]
    rw [h₁]
    nlinarith [mul_nonneg hω (sub_nonneg.mpr hle1),
      mul_nonneg (mul_nonneg hrp.le hω) (sub_nonneg.mpr hcos),
      abs_nonneg (Real.cos (t / 2 * Real.log u))]
  calc |2 * u ^ (-(3 / 4) : ℝ) * Real.cos (t / 2 * Real.log u) * omega u|
      ≤ 2 * omega u := habs
    _ ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π * u))) := by
        have := omega_le_geometric hu0
        linarith
    _ ≤ 2 * (Real.exp (-π * u) / (1 - Real.exp (-π))) := by gcongr
    _ = 2 * Real.exp (-π * u) / (1 - Real.exp (-π)) := by ring

end PrincipiaTractalis.XiThetaIntegral

-- Axiom check. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.XiThetaIntegral.evenKernel_zero_eq
#print axioms PrincipiaTractalis.XiThetaIntegral.omega_nonneg
#print axioms PrincipiaTractalis.XiThetaIntegral.omega_pos
#print axioms PrincipiaTractalis.XiThetaIntegral.omega_antitone
#print axioms PrincipiaTractalis.XiThetaIntegral.omega_le_geometric
#print axioms PrincipiaTractalis.XiThetaIntegral.continuousOn_omega
#print axioms PrincipiaTractalis.XiThetaIntegral.integrableOn_cpow_smul_evenKernel_sub_one
#print axioms PrincipiaTractalis.XiThetaIntegral.mellin_f_modif_split
#print axioms PrincipiaTractalis.XiThetaIntegral.mellin_f_modif_inversion
#print axioms PrincipiaTractalis.XiThetaIntegral.completedRiemannZeta₀_eq_theta_integral
#print axioms PrincipiaTractalis.XiThetaIntegral.completedRiemannZeta_eq_theta_integral
#print axioms PrincipiaTractalis.XiThetaIntegral.critical_integrand_eq
#print axioms PrincipiaTractalis.XiThetaIntegral.pole_term_critical
#print axioms PrincipiaTractalis.XiThetaIntegral.Xi_eq_theta_integral
#print axioms PrincipiaTractalis.XiThetaIntegral.integrableOn_Xi_theta_integrand
#print axioms PrincipiaTractalis.XiThetaIntegral.Xi_theta_integrand_abs_le
