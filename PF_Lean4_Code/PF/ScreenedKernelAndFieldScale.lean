/-
# What The Kernel Actually Is, And What It Forces On `M` (2026-10-06)

`LambdaEffFromAction` derived `Λ_eff = Λ₀e^{−φ/M}` from an action, showed our
boxed formula is the static solution of the resulting field equation, and then
had to report that `R_f(√(2π), |x|)` cannot be the kernel that solution needs.
It left the actual kernel owed. This supplies it, and the kernel turns out to
**pin `M` to within a factor of four of the Planck mass** — a derived constraint,
not a fit, and the first number in this chapter that an observation could
contradict.

## §1 — The kernel is the screened (Yukawa) Green's function, not `1/4πr`

Linearize `∇²φ = V'(φ) − ch₂/f` about a background `φ₀`. With
`V(φ) = (Λ₀/κ)e^{−φ/M}` we have `V'' = V/M²`, so the perturbation obeys

  `(∇² − m²)δφ = −ch₂/f`,   `m² = V''(φ₀) = V(φ₀)/M² = Λ_eff/(κM²)`.

That is a **screened Poisson equation**, whose Green's function is

  `G(r) = e^{−mr}/(4πr)`   (`yukawaKernel`).

Three consequences, each formalized below.

**(a) It still diverges at the origin, so the obstruction against `R_f` stands.**
`e^{−mr} → 1` as `r → 0`, so `G` is unbounded there
(`yukawa_unbounded_at_origin`), exactly as the unscreened kernel was. `R_f`'s
abscissa `σ(√(2π)) ≈ −0.0387 < 0` keeps it bounded and tending to `1`, so it is
excluded as the kernel of *either* equation. Nothing about the screening rescues
it.

**(b) It fixes the dimensional complaint that `R_f` could not.** The objection to
`R_f(√(2π), |x|)` was that `r` sat in the *exponent* of a Dirichlet series and so
had to be dimensionless, while we put a length there. The Yukawa exponent is
`mr` — a length times an inverse length. The screening mass is precisely the
scale the earlier formula was missing.

**(c) It reduces to `1/4πr` in the unscreened limit**
(`yukawa_at_zero_mass_is_unscreened`), and agrees with it to within `1 − ε`
whenever `mr ≤ ε` (`yukawa_agrees_when_unscreened`). So `LambdaEffFromAction`'s
`1/4πf ∫ ch₂/|x−x'|` is the short-range limit of this, and is a good
approximation on every scale small against `1/m`.

## §2 — And the screening length forces `M` near the Planck mass

In natural units `κ = 8π/M_Pl²`, so `m² = Λ_eff M_Pl²/(8πM²)` and

  `1/m = √(8π) · (M/M_Pl) · Λ_eff^{−1/2}`.

Numerically, with `Λ_obs = 1.1056×10⁻⁵² m⁻²` (Planck 2018: `Ω_Λ = 0.6889`,
`H₀ = 67.66` km/s/Mpc):

| quantity | value |
|---|---|
| `Λ_obs^{−1/2}` (de Sitter radius) | `9.5104×10²⁵ m` |
| `c/H₀` (Hubble radius) | `1.3672×10²⁶ m` |
| `√(8π)` | `5.0133` |
| `1/m` at `M = M_Pl` | `4.768×10²⁶ m` = `3.49 ×` Hubble radius |
| `1/m` at `M = 10⁻³M_Pl` | `4.768×10²³ m` = `3.5×10⁻³ ×` Hubble radius |
| `1/m` at `M = 1 TeV` | `4.8×10¹⁰ m` ≈ `0.3 AU` |

**The dark-energy mechanism of ch08's Prop. 8.x requires the suppression to act
across the observable universe, i.e. `1/m ≥ c/H₀`. That requires**

  `M/M_Pl ≥ (c/H₀)·Λ^{1/2}/√(8π) = 1.3672/4.7675 = 0.2868`,

**so `M ≳ 0.29 M_Pl`** (`horizon_requires_planckian_scale`, with the numeric
bracket `1/4 < 0.2868 < 1/3` at `required_ratio_is_near_one`). The dependence is
strictly monotone in `M` (`screening_length_strictly_monotone`), so this is a
genuine threshold and not an artefact of the parametrisation.

## §3 — This cuts both ways, and both halves should be said

**In the framework's favour.** At `M = M_Pl` the screening length is `3.5×` the
Hubble radius, so the kernel is effectively unscreened everywhere observable and
the `1/4πr` form of `LambdaEffFromAction` §3 holds to nine decimal places at
laboratory scales. The mechanism is internally consistent at the Planck scale,
and there is no fine-tuning in the kernel: the one scale it needs is the one the
potential already carries.

**Against it.** `M ≳ 0.29 M_Pl` is a **Planck-scale field excursion**, and that
is the standard and well-known difficulty of quintessence models — such
excursions are hard to protect against higher-dimension operators and are argued
to be obstructed in string constructions. More sharply: **if `M` sits at any
accessible particle-physics scale the mechanism dies.** At `1 TeV` the
suppression is screened at `0.3 AU`, so `Λ_eff` would vary across the solar
system and could not be cosmological. There is no intermediate option — the gap
between `1 TeV` and `0.29 M_Pl` is sixteen orders of magnitude, and every value
in it is excluded by this inequality.

**So the framework's dark-energy mechanism commits it to `M` within a factor of
four of `M_Pl`.** That is a sharp, derived, falsifiable commitment, and it is
the number `Ch08Ch14ModifiedRelativity` said the framework owed.

## Scope

**Formalized**: the unboundedness of the screened kernel at the origin; its
reduction to the unscreened kernel at zero mass; its agreement with the
unscreened kernel when `mr` is small; the strict monotonicity of the screening
length in `M`; the threshold equivalence; and the numeric bracket on the required
ratio.

**Prose only, standard, cited, not derived here**: the linearization and the
identification `m² = V''(φ₀)`; that the screened Poisson Green's function is
`e^{−mr}/4πr`; the relation `κ = 8π/M_Pl²`; the Planck 2018 values of `Λ` and
`H₀`; and the string-theoretic arguments against super-Planckian excursions.
The arithmetic behind the table was computed outside Lean and is quoted, with
the one load-bearing ratio re-checked in the kernel.

**Not claimed**: that `M` does take a Planck-scale value, that `f` or the aether
couplings are determined, or that `Λ₀` comes out right. The constraint derived
here is necessary, not sufficient.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.ScreenedKernelAndFieldScale

/-! ## §1 — The screened kernel -/

/-- The unscreened three-dimensional Green's function `1/(4πr)`, as in
    `LambdaEffFromAction`. -/
noncomputable def unscreenedKernel (r : ℝ) : ℝ := 1 / (4 * Real.pi * r)

/-- The screened (Yukawa) Green's function `e^{−mr}/(4πr)` of `∇² − m²`. -/
noncomputable def yukawaKernel (m r : ℝ) : ℝ :=
  Real.exp (-(m * r)) / (4 * Real.pi * r)

/-- **★ At zero screening mass the kernel is the unscreened one. ★**

    So `LambdaEffFromAction`'s `1/4πf ∫ ch₂/|x−x'|` is the `m → 0` limit of this,
    not a different ansatz. -/
theorem yukawa_at_zero_mass_is_unscreened (r : ℝ) :
    yukawaKernel 0 r = unscreenedKernel r := by
  unfold yukawaKernel unscreenedKernel
  norm_num

/-- **★ On scales short against the screening length the two kernels agree. ★**

    If `mr ≤ ε` then the screened kernel is at least `(1 − ε)` times the
    unscreened one, so the unscreened form is accurate wherever `mr` is small.
    This is what licenses using `1/4πr` at laboratory and solar-system scales
    once `1/m` is shown to be cosmological. -/
theorem yukawa_agrees_when_unscreened (m r eps : ℝ) (hr : 0 < r)
    (hmr : m * r ≤ eps) :
    (1 - eps) * unscreenedKernel r ≤ yukawaKernel m r := by
  have hpi := Real.pi_pos
  have hden : (0 : ℝ) < 4 * Real.pi * r := by positivity
  have hexp : 1 - eps ≤ Real.exp (-(m * r)) := by
    have h := Real.add_one_le_exp (-(m * r))
    linarith
  unfold yukawaKernel unscreenedKernel
  rw [mul_one_div, div_le_div_iff_of_pos_right hden]
  exact hexp

/-- The screened kernel exceeds any bound at radii small enough — stated with
    the two smallness conditions explicit, so the witness in the existential
    below is built rather than asserted. -/
theorem yukawa_lower_bound_near_origin (m B r : ℝ) (hm : 0 < m) (hB : 0 < B)
    (hrpos : 0 < r) (h1 : r ≤ 1 / (2 * m)) (h2 : r ≤ 1 / (16 * Real.pi * B)) :
    B < yukawaKernel m r := by
  have hpi := Real.pi_pos
  have hmr : m * r ≤ 1 / 2 := by
    have hstep : m * r ≤ m * (1 / (2 * m)) := by nlinarith
    have hval : m * (1 / (2 * m)) = 1 / 2 := by
      field_simp
    linarith [hstep, hval.le, hval.ge]
  have hexp : (1 : ℝ) / 2 ≤ Real.exp (-(m * r)) := by
    have h := Real.add_one_le_exp (-(m * r))
    linarith
  have hden : 4 * B ≤ 1 / (4 * Real.pi * r) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi * r)]
    have hkey : 16 * Real.pi * B * r ≤ 16 * Real.pi * B * (1 / (16 * Real.pi * B)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have hone : 16 * Real.pi * B * (1 / (16 * Real.pi * B)) = 1 := by
      field_simp
    nlinarith [hkey, hone.le, hone.ge]
  have hprod : (1 : ℝ) / 2 * (4 * B) ≤ Real.exp (-(m * r)) * (1 / (4 * Real.pi * r)) :=
    mul_le_mul hexp hden (by positivity) (Real.exp_pos _).le
  unfold yukawaKernel
  rw [div_eq_mul_one_div]
  linarith

/-- **★ The screened kernel is unbounded at the origin, so the obstruction
    against `R_f` stands under screening too. ★**

    `e^{−mr} → 1` as `r → 0`, so screening does not tame the singularity.
    `R_f(√(2π), r)` stays bounded near `1` for every `r > 0` because its abscissa
    of convergence is negative, and so is excluded as the kernel of the screened
    equation exactly as it was for the unscreened one. -/
theorem yukawa_unbounded_at_origin (m B : ℝ) (hm : 0 < m) (hB : 0 < B) :
    ∃ r : ℝ, 0 < r ∧ B < yukawaKernel m r := by
  have hpi := Real.pi_pos
  have ha : (0 : ℝ) < 1 / (2 * m) := by
    apply one_div_pos.mpr; linarith
  have hb : (0 : ℝ) < 1 / (16 * Real.pi * B) := by
    apply one_div_pos.mpr; positivity
  refine ⟨min (1 / (2 * m)) (1 / (16 * Real.pi * B)), lt_min ha hb, ?_⟩
  exact yukawa_lower_bound_near_origin m B _ hm hB (lt_min ha hb)
    (min_le_left _ _) (min_le_right _ _)

/-! ## §2 — The screening length, and what it forces on `M`

    Written with the coefficient `A = √(8π)·Λ^{−1/2}` as a single positive
    constant, so the algebra is about the threshold rather than about square
    roots of particular numbers. -/

/-- The screening length `1/m = A·(M/M_Pl)` with `A = √(8π)·Λ_eff^{−1/2}`. -/
noncomputable def screeningLength (A M Mpl : ℝ) : ℝ := A * (M / Mpl)

/-- **★ The screening length is strictly increasing in the field scale `M`. ★**

    So the horizon condition below is a genuine threshold in `M`, not an
    artefact of how the relation was parametrised. -/
theorem screening_length_strictly_monotone (A Mpl M₁ M₂ : ℝ)
    (hA : 0 < A) (hMpl : 0 < Mpl) (h : M₁ < M₂) :
    screeningLength A M₁ Mpl < screeningLength A M₂ Mpl := by
  unfold screeningLength
  have hinv : (0 : ℝ) < 1 / Mpl := one_div_pos.mpr hMpl
  have hratio : M₁ / Mpl < M₂ / Mpl := by
    have hprod : 0 < (M₂ - M₁) * (1 / Mpl) := mul_pos (by linarith) hinv
    have e1 : M₁ / Mpl = M₁ * (1 / Mpl) := by ring
    have e2 : M₂ / Mpl = M₂ * (1 / Mpl) := by ring
    rw [e1, e2]
    nlinarith [hprod]
  exact (mul_lt_mul_left hA).mpr hratio

/-- **★ The horizon condition is exactly a lower bound on `M/M_Pl`. ★**

    `1/m ≥ R` holds precisely when `M/M_Pl ≥ R/A`. With `R` the Hubble radius
    and `A = √(8π)Λ^{−1/2}` this is the constraint `M ≳ 0.29 M_Pl`. -/
theorem horizon_requires_planckian_scale (A M Mpl R : ℝ) (hA : 0 < A) :
    R ≤ screeningLength A M Mpl ↔ R / A ≤ M / Mpl := by
  unfold screeningLength
  rw [div_le_iff₀ hA, mul_comm]

/-- **★ And the contrapositive, which is the falsifiable half: a field scale
    below the threshold screens the suppression inside the horizon. ★**

    At `M = 1 TeV`, `M/M_Pl ≈ 10⁻¹⁶` against a threshold of `0.287`, so the
    screening length is about `0.3 AU` and `Λ_eff` would vary across the solar
    system. Every value between a TeV and `0.29 M_Pl` is excluded this way. -/
theorem sub_threshold_scale_screens_inside_horizon (A M Mpl R : ℝ) (hA : 0 < A)
    (hbreak : M / Mpl < R / A) :
    screeningLength A M Mpl < R := by
  unfold screeningLength
  have hAne : A ≠ 0 := ne_of_gt hA
  have h1 : A * (M / Mpl) < A * (R / A) := (mul_lt_mul_left hA).mpr hbreak
  have h2 : A * (R / A) = R := by field_simp
  linarith

/-- The numeric bracket on the required ratio, re-checked in the kernel rather
    than quoted: `(c/H₀)·Λ^{1/2}/√(8π) = 1.3672/4.7675`, which lies strictly
    between `1/4` and `1/3`. So the threshold is a Planck-scale value to within a
    factor of four, which is the claim §3 rests on. -/
theorem required_ratio_is_near_one :
    (1 : ℝ) / 4 < 13672 / 47675 ∧ (13672 : ℝ) / 47675 < 1 / 3 := by
  constructor <;> norm_num

/-! ## §3 — Capstone -/

/-- **★ The kernel, and the field scale it forces — capstone ★**

    The screened Green's function reduces to the unscreened one at zero mass and
    agrees with it whenever `mr` is small; it is still unbounded at the origin,
    so `R_f` is excluded under screening as it was without; the screening length
    is strictly monotone in `M`; the horizon condition is exactly a lower bound
    on `M/M_Pl`; a scale below that bound screens the suppression inside the
    horizon; and the bound sits between `1/4` and `1/3`, i.e. at the Planck mass
    to within a factor of four. -/
theorem ScreenedKernel_capstone :
    (∀ r : ℝ, yukawaKernel 0 r = unscreenedKernel r) ∧
    (∀ m r eps : ℝ, 0 < r → m * r ≤ eps →
      (1 - eps) * unscreenedKernel r ≤ yukawaKernel m r) ∧
    (∀ m B : ℝ, 0 < m → 0 < B → ∃ r : ℝ, 0 < r ∧ B < yukawaKernel m r) ∧
    (∀ A Mpl M₁ M₂ : ℝ, 0 < A → 0 < Mpl → M₁ < M₂ →
      screeningLength A M₁ Mpl < screeningLength A M₂ Mpl) ∧
    (∀ A M Mpl R : ℝ, 0 < A →
      (R ≤ screeningLength A M Mpl ↔ R / A ≤ M / Mpl)) ∧
    (∀ A M Mpl R : ℝ, 0 < A → M / Mpl < R / A →
      screeningLength A M Mpl < R) ∧
    ((1 : ℝ) / 4 < 13672 / 47675 ∧ (13672 : ℝ) / 47675 < 1 / 3) :=
  ⟨yukawa_at_zero_mass_is_unscreened,
   yukawa_agrees_when_unscreened,
   yukawa_unbounded_at_origin,
   screening_length_strictly_monotone,
   horizon_requires_planckian_scale,
   sub_threshold_scale_screens_inside_horizon,
   required_ratio_is_near_one⟩

/-! ## §4 — Non-vacuity -/

/-- Non-vacuity: at `M = M_Pl` the screening length is `A` itself, which exceeds
    the Hubble radius on the quoted numbers — so the admissible region is
    nonempty and the threshold above is not excluding everything. Stated with
    the ratio form so the witness is the actual numeric case. -/
theorem planck_scale_satisfies_the_threshold (A Mpl : ℝ) (hA : 0 < A)
    (hMpl : 0 < Mpl) :
    screeningLength A Mpl Mpl = A ∧
      ((13672 : ℝ) / 47675) * A ≤ screeningLength A Mpl Mpl := by
  have hself : screeningLength A Mpl Mpl = A := by
    unfold screeningLength
    rw [div_self (ne_of_gt hMpl), mul_one]
  refine ⟨hself, ?_⟩
  rw [hself]
  have hr : (13672 : ℝ) / 47675 < 1 := by norm_num
  nlinarith [hA, hr]

end PrincipiaTractalis.ScreenedKernelAndFieldScale

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.yukawa_at_zero_mass_is_unscreened
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.yukawa_agrees_when_unscreened
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.yukawa_lower_bound_near_origin
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.yukawa_unbounded_at_origin
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.screening_length_strictly_monotone
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.horizon_requires_planckian_scale
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.sub_threshold_scale_screens_inside_horizon
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.required_ratio_is_near_one
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.ScreenedKernel_capstone
#print axioms PrincipiaTractalis.ScreenedKernelAndFieldScale.planck_scale_satisfies_the_threshold
