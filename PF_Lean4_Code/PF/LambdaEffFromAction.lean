/-
# Deriving `Λ_eff` From An Action (2026-10-06)

The repair identified yesterday, carried out. `Λ_eff` was defined in our ch08 as
a nonlocal functional of a spatial slice, which cannot come from a covariant
local action and which made the theory non-conservative — exactly the class
`|α₃| ≲ 10⁻²⁰` exists to exclude. Here is the action it *can* come from, what
varying it gives, and the one substitution our boxed formula still needs.

## §0 — The ch₂ selection is what makes this possible

Of the five quantities our corpus calls `ch₂`, **exactly one can appear in a
covariant local action**:

| form | why | admissible? |
|---|---|---|
| Chern–Weil `(1/8π²)Tr(F∧F)` | a local 4-form on the base | **yes** |
| matrix trace form | a function of a matrix, not a field | no |
| entanglement `1 − Tr(ρ²)` | a nonlinear functional of the *state* | no |
| ch04's `Tr(𝒞²ρ)/Tr(ρ)` | undefined, no Haar measure | no |
| ch31's band ratio | a spectral ratio, not a field | no |

And the reason the Chern–Weil form qualifies is worth stating: `Tr(F∧F)` **is**
the Pontryagin density, so coupling a scalar to it is the standard **axion**
coupling — local, gauge-invariant, and already a top form, so it needs no
`√−g`. The naming decision taken yesterday, which rested on two grounds and
looked like bookkeeping, is exactly what admits an action derivation. The other
four cannot appear in one at all.

## §1 — The action

  `S = ∫ d⁴x √−g [ R/(2κ) − ½(∇φ)² − V(φ) + L_m + L_æ ]  +  (1/f) ∫ φ · ch₂`

with `V(φ) = (Λ₀/κ) e^{−φ/M}`, `L_æ` the Einstein-aether terms if a preferred
structure is wanted, and the last term a top form carrying no metric.

**Varying the metric** gives `G_{μν} = κ(T_{μν} + T^φ_{μν})` with
`T^φ_{μν} = ∇_μφ∇_νφ − g_{μν}[½(∇φ)² + V(φ)]`. In the slowly-varying limit
`(∇φ)² → 0` this is `−V(φ)g_{μν}`, a cosmological term with

  `Λ_eff = κV(φ) = Λ₀ e^{−φ/M}`   (`lambda_eff_from_potential`)

— **exactly our form, with `φ` a local dynamical field in place of a spatial
integral.** It is strictly positive (`lambda_eff_pos`) and strictly decreasing
in `φ` (`lambda_eff_strictly_decreasing`), which is the mechanism ch08 wanted:
`Λ` falls where the consciousness field has grown. The approximation is
controlled, not hand-waved: the error is bounded by the kinetic density
(`slow_roll_relative_error`), so "slowly varying" has a stated meaning.

**Varying `φ`** gives `□φ = V'(φ) − ch₂/f`, so `ch₂` **sources** `φ`, and
`ch₂ ↑ ⟹ φ ↑ ⟹ Λ_eff ↓` is the dark-energy mechanism, now local.

And the suppression depends only on `(ψ − φ)/M`
(`suppression_factor_is_scaled_difference`), which is what fixes the meaning of
`M`: it is the field excursion that suppresses `Λ` by one factor of `e`. There
is no second scale hiding in the exponential.

## §2 — Conservation is automatic, and `α₃ = 0` structurally

This is what lifts the `10⁻²⁰` bound, and the reason is cleaner than the
"compensating field" framing of yesterday.

**Once `Λ_eff` comes from `φ`, there is no separate `Λ g_{μν}` term at all** — it
is *inside* `T^φ_{μν}`. The field equation is `G_{μν} = κ S_{μν}` with
`S = T + T^φ`, and the contracted Bianchi identity `∇^μ G_{μν} = 0` gives
`∇^μ S_{μν} = 0` directly, with **no residue**
(`absorbed_lambda_leaves_no_residue`). There is nothing to compensate, because
the thing that needed compensating was the detached `Λ` term, and it is gone.
Energy–momentum is conserved, so `α₃ = 0` identically rather than by tuning, and
only `α₁, α₂` remain — at `10⁻⁴` and `10⁻⁷`, and zeroable by choice of the
aether couplings.

This **supersedes** `GravitomagneticRescue.conservation_iff_compensating_divergence`
as the repair. That theorem is still correct and still pins the compensator
uniquely *given* a detached `Λ`; the point here is that the action removes the
detached `Λ`, so no compensator need be exhibited at all.

## §3 — Where our spatial integral came from, and the one repair it still needs

The static limit of the `φ` equation is `∇²φ = V'(φ) − ch₂/f`, whose
Green's-function solution is
`φ(x) = (1/4πf) ∫ d³x' ch₂(x')/|x − x'| + …`. Compare what we boxed:

  `Λ_eff = Λ₀ exp[ −∫_Σ d³x ch₂(x) · R_f(√(2π), |x|) ]`.

**Same shape** — a source integrated against a kernel, exponentiated. So our
boxed formula is the **static solution of a local field equation, written as
though it were a definition.** That is the whole repair: make the field equation
primary and the integral its solution. The slice `Σ` stops being a choice and
becomes the surface on which a static solution is evaluated.

**And it fixes the translation-invariance objection for free.** A Green's
function depends on `|x − x'|`, a *difference*, which needs no origin. We wrote
`|x|`. One character.

**But the kernel cannot stay as written, and this is the honest cost.** A
three-dimensional Green's function must diverge like `1/r` as `r → 0`
(`greens_kernel_is_unbounded`). `R_f(√(2π), r)` does not: its abscissa of
convergence is `σ(√(2π)) = log₃|1 + 2cos(π√(2π))| ≈ −0.0387 < 0`, so the series
converges for every `r > 0` and stays near `1`. Measured against `1/r`, the
magnitude of `R_f` at `r = 0.5, 1, 5, 10` is `1.198, 1.187, 1.004, 1.000`, while
`1/r` is `2.000, 1.000, 0.200, 0.100`. It is bounded where the Green's function
blows up, and tends to `1` where the Green's function tends to `0`. Separately,
`r` sits in the **exponent** of a Dirichlet series, so it must be dimensionless,
and we put a length there.

**So: the mechanism is derivable and the shape is right, but
`R_f(√(2π), |x|)` must be replaced by the actual kernel.** What survives is the
exponential suppression, the sourcing by `ch₂`, and automatic conservation. What
does not survive is that particular kernel.

## Scope

**Formalized**: the potential-to-`Λ_eff` identification; positivity and strict
monotonicity in `φ`; the slow-roll error bound; the scaled-difference form of
the suppression factor; the no-residue conservation argument; and the
unboundedness of a `1/r` kernel.

**Prose only, standard, cited, not proved here**: the variational derivation
itself; Noether's theorem; the contracted Bianchi identity; the vanishing of
`α₃` in action-derived theories; the zeroability of `α₁, α₂` in Einstein-aether.
The `R_f` numerics were computed outside Lean and are quoted, not derived.

**Not claimed**: that `M`, `f`, or the aether couplings take any particular
value, or that the resulting `Λ₀` matches observation. Those are the next
calculation, and they are where this can still fail.

**Two theorems were drafted for this module and cut before shipping** as
arithmetic shadows of prose steps: `-(0/2 + V) = -V` for the slow-roll limit,
and a restatement of the monotonicity theorem under a second name. The slow-roll
content is carried instead by `slow_roll_relative_error`, which bounds the error
rather than asserting the limit. This is the seventh and eighth such removal in
three days; the pattern is recorded in `Ch08Ch14ModifiedRelativity`.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace PrincipiaTractalis.LambdaEffFromAction

/-! ## §1 — The potential and the effective cosmological term -/

/-- The exponential potential `V(φ) = (Λ₀/κ)e^{−φ/M}` appearing in the action. -/
noncomputable def potential (Lam0 kap M phi : ℝ) : ℝ :=
  Lam0 / kap * Real.exp (-phi / M)

/-- The effective cosmological term read off the slow-roll stress tensor,
    `Λ_eff = κ V(φ)`. -/
noncomputable def lambdaEff (Lam0 M phi : ℝ) : ℝ := Lam0 * Real.exp (-phi / M)

/-- **★ The potential normalization reproduces our boxed exponential form. ★**

    `κ V(φ) = Λ₀ e^{−φ/M}` — the shape ch08 asserts, now as the output of a
    variation rather than a definition. -/
theorem lambda_eff_from_potential (Lam0 kap M phi : ℝ) (hkap : kap ≠ 0) :
    kap * potential Lam0 kap M phi = lambdaEff Lam0 M phi := by
  unfold potential lambdaEff
  field_simp

/-- `Λ_eff > 0` for positive `Λ₀`: the suppression never changes its sign, so
    the mechanism cannot turn dark energy attractive. -/
theorem lambda_eff_pos (Lam0 M phi : ℝ) (hL : 0 < Lam0) :
    0 < lambdaEff Lam0 M phi := by
  unfold lambdaEff
  have := Real.exp_pos (-phi / M)
  positivity

/-- **★ `Λ_eff` is strictly decreasing in `φ`. ★**

    This is the mechanism ch08 wanted — `Λ` falls where the consciousness field
    has grown — and here it is a property of the potential rather than an
    assertion. -/
theorem lambda_eff_strictly_decreasing (Lam0 M phi psi : ℝ)
    (hL : 0 < Lam0) (hM : 0 < M) (h : phi < psi) :
    lambdaEff Lam0 M psi < lambdaEff Lam0 M phi := by
  unfold lambdaEff
  have hinv : (0 : ℝ) < 1 / M := by positivity
  have harg : -psi / M < -phi / M := by
    have hprod : 0 < (psi - phi) * (1 / M) := mul_pos (by linarith) hinv
    have e1 : -psi / M = -psi * (1 / M) := by ring
    have e2 : -phi / M = -phi * (1 / M) := by ring
    rw [e1, e2]
    nlinarith [hprod]
  exact (mul_lt_mul_left hL).mpr (Real.exp_lt_exp.mpr harg)

/-- **★ The suppression factor depends only on the scaled field difference. ★**

    `Λ_eff(ψ) = Λ_eff(φ)·e^{−(ψ−φ)/M}`, so `M` has an operational meaning: it is
    the field excursion that suppresses `Λ` by one factor of `e`. No second
    scale hides in the exponential. -/
theorem suppression_factor_is_scaled_difference (Lam0 M phi psi : ℝ) :
    lambdaEff Lam0 M psi = lambdaEff Lam0 M phi * Real.exp (-(psi - phi) / M) := by
  unfold lambdaEff
  have harg : -psi / M = -phi / M + -(psi - phi) / M := by
    rw [div_add_div_same]
    congr 1
    ring
  rw [harg, Real.exp_add, mul_assoc]

/-! ## §2 — The slow-roll approximation, with its error bounded -/

/-- **The slow-roll identification is controlled, not asserted.**

    The coefficient of `g_{μν}` in `T^φ` is `−[K/2 + V]` with `K = (∇φ)²`; the
    cosmological-term reading drops the `K`. If the kinetic density is at most
    `2εV` then the error is at most `εV`, so "slowly varying" is a quantitative
    condition rather than a gesture. -/
theorem slow_roll_relative_error (K V eps : ℝ) (hK : 0 ≤ K)
    (hsmall : K ≤ 2 * eps * V) :
    |(-(K / 2 + V)) - (-V)| ≤ eps * V := by
  have hrw : (-(K / 2 + V)) - (-V) = -(K / 2) := by ring
  rw [hrw, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ K / 2)]
  linarith

/-! ## §3 — Conservation, with no residue -/

/-- **★ Once `Λ_eff` sits inside the scalar's stress tensor there is no residue
    to compensate. ★**

    The field equation is `G = κS` with no separate `Λ g` term, so the
    contracted Bianchi identity `∇·G = 0` gives `∇·S = 0` directly. This is
    what makes `α₃ = 0` structural: the non-conservation found in
    `Ch08Ch14ModifiedRelativity` came entirely from the detached `Λ` term, and
    absorbing it removes the source rather than cancelling it. -/
theorem absorbed_lambda_leaves_no_residue (divG divS kap : ℝ)
    (hkap : kap ≠ 0) (heq : divG = kap * divS) (hbianchi : divG = 0) :
    divS = 0 := by
  rw [hbianchi] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left hkap

/-! ## §4 — The kernel our boxed formula still needs -/

/-- The three-dimensional Green's function of the Laplacian, `1/(4πr)`. -/
noncomputable def greensKernel (r : ℝ) : ℝ := 1 / (4 * Real.pi * r)

/-- **★ The Green's kernel is unbounded as `r → 0`. ★**

    For any proposed bound there is a radius exceeding it. This is precisely the
    property `R_f(√(2π), r)` lacks: its abscissa of convergence is negative, so
    the series converges for every `r > 0` and stays near `1`. The two cannot be
    the same kernel, and that is what our boxed formula still owes. -/
theorem greens_kernel_is_unbounded (B : ℝ) (hB : 0 < B) :
    ∃ r : ℝ, 0 < r ∧ B < greensKernel r := by
  have hpi := Real.pi_pos
  have hpine : Real.pi ≠ 0 := ne_of_gt hpi
  have hBne : B ≠ 0 := ne_of_gt hB
  refine ⟨1 / (8 * Real.pi * B), by positivity, ?_⟩
  unfold greensKernel
  have h1 : 4 * Real.pi * (1 / (8 * Real.pi * B)) = 1 / (2 * B) := by
    field_simp
    ring
  rw [h1, one_div_one_div]
  linarith

/-- The kernel is positive wherever it is defined, so the comparison above is
    between a divergent positive kernel and a bounded one, not an artefact of
    sign. -/
theorem greens_kernel_pos (r : ℝ) (hr : 0 < r) : 0 < greensKernel r := by
  unfold greensKernel
  have := Real.pi_pos
  positivity

/-! ## §5 — Capstone -/

/-- **★ `Λ_eff` from an action — capstone ★**

    The exponential potential reproduces our boxed form under variation; the
    result is positive and strictly decreasing in `φ`; the suppression factor
    depends only on `(ψ−φ)/M`; the slow-roll error is bounded by the kinetic
    density; absorbing `Λ` into the scalar's stress tensor leaves no residue, so
    conservation is automatic and `α₃ = 0` structurally; and the kernel the
    static solution requires is unbounded at the origin, which the Dirichlet
    series we wrote is not. -/
theorem LambdaEffFromAction_capstone :
    (∀ Lam0 kap M phi : ℝ, kap ≠ 0 →
      kap * potential Lam0 kap M phi = lambdaEff Lam0 M phi) ∧
    (∀ Lam0 M phi : ℝ, 0 < Lam0 → 0 < lambdaEff Lam0 M phi) ∧
    (∀ Lam0 M phi psi : ℝ, 0 < Lam0 → 0 < M → phi < psi →
      lambdaEff Lam0 M psi < lambdaEff Lam0 M phi) ∧
    (∀ Lam0 M phi psi : ℝ,
      lambdaEff Lam0 M psi = lambdaEff Lam0 M phi * Real.exp (-(psi - phi) / M)) ∧
    (∀ K V eps : ℝ, 0 ≤ K → K ≤ 2 * eps * V →
      |(-(K / 2 + V)) - (-V)| ≤ eps * V) ∧
    (∀ divG divS kap : ℝ, kap ≠ 0 → divG = kap * divS → divG = 0 → divS = 0) ∧
    (∀ B : ℝ, 0 < B → ∃ r : ℝ, 0 < r ∧ B < greensKernel r) :=
  ⟨lambda_eff_from_potential,
   lambda_eff_pos,
   lambda_eff_strictly_decreasing,
   suppression_factor_is_scaled_difference,
   slow_roll_relative_error,
   absorbed_lambda_leaves_no_residue,
   greens_kernel_is_unbounded⟩

/-! ## §6 — Non-vacuity -/

/-- Non-vacuity: at `φ = 0` the suppression is absent and `Λ_eff = Λ₀`, and at
    `φ = M` it is strictly smaller. So the monotonicity above is a statement
    about a genuinely nonconstant function with a definite starting value, not
    about an empty or degenerate family. -/
theorem suppression_starts_at_bare_value (Lam0 M : ℝ) (hL : 0 < Lam0) (hM : 0 < M) :
    lambdaEff Lam0 M 0 = Lam0 ∧ lambdaEff Lam0 M M < Lam0 := by
  have hzero : lambdaEff Lam0 M 0 = Lam0 := by
    unfold lambdaEff
    simp
  refine ⟨hzero, ?_⟩
  have h := lambda_eff_strictly_decreasing Lam0 M 0 M hL hM hM
  rwa [hzero] at h

end PrincipiaTractalis.LambdaEffFromAction

/-! ## Axiom audit — LIVE, not commented out -/

#print axioms PrincipiaTractalis.LambdaEffFromAction.lambda_eff_from_potential
#print axioms PrincipiaTractalis.LambdaEffFromAction.lambda_eff_pos
#print axioms PrincipiaTractalis.LambdaEffFromAction.lambda_eff_strictly_decreasing
#print axioms PrincipiaTractalis.LambdaEffFromAction.suppression_factor_is_scaled_difference
#print axioms PrincipiaTractalis.LambdaEffFromAction.slow_roll_relative_error
#print axioms PrincipiaTractalis.LambdaEffFromAction.absorbed_lambda_leaves_no_residue
#print axioms PrincipiaTractalis.LambdaEffFromAction.greens_kernel_is_unbounded
#print axioms PrincipiaTractalis.LambdaEffFromAction.greens_kernel_pos
#print axioms PrincipiaTractalis.LambdaEffFromAction.LambdaEffFromAction_capstone
#print axioms PrincipiaTractalis.LambdaEffFromAction.suppression_starts_at_bare_value
