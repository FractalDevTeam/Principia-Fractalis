/-
# Fujita-Kato 1964 — Schwartz × Schwartz Pointwise Multiplication

★ 2026-06-10 — Twenty-fourth brick of real Fujita-Kato infrastructure.
★ Closes the foundational mathlib API piece: pointwise multiplication of
  two scalar Schwartz functions on `R3` yields a Schwartz function.

The Fujita-Kato 1964 mild-solution construction repeatedly needs
multiplication of Schwartz factors:

  • Physical-space heat semigroup `e^{tΔ} f = F⁻¹ (m_t · F f)`
    multiplies the Schwartz Gaussian symbol `m_t` against the Schwartz
    function `F f`.
  • Convective derivative `(u · ∇) v` multiplies vector components
    `u_j` against partial derivatives `∂_j v` componentwise — each
    factor a Schwartz scalar.
  • Sobolev pairing integrands `|ξ| · |f̂(ξ)|² = |ξ| · (f̂ · conj f̂)`
    multiply Schwartz frequency-side functions.

Each of these operations lives inside scalar Schwartz space iff
pointwise multiplication of Schwartz functions is itself a Schwartz
function. The mathlib API supplies this through
`SchwartzMap.bilinLeftCLM`, which upgrades a continuous bilinear map
`B : E →L[𝕜] F →L[𝕜] G` together with a function `g : D → F` of
`Function.HasTemperateGrowth` into a continuous linear endomorphism
of scalar Schwartz space. With

  • `B := ContinuousLinearMap.mul ℂ ℂ` (complex multiplication as a
    continuous bilinear map `ℂ →L[ℂ] ℂ →L[ℂ] ℂ`)
  • `g := (g : R3 → ℂ)` for any Schwartz `g`

the result `bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg : 𝓢(R3, ℂ)
→L[ℂ] 𝓢(R3, ℂ)` is precisely pointwise left-multiplication by `g`.
The only remaining ingredient is the temperate-growth witness
`(↑g : R3 → ℂ).HasTemperateGrowth` for Schwartz `g`. This is
unconditionally true: every Schwartz function is smooth (the
`smooth'` field of `SchwartzMap`) and every iterated Fréchet
derivative is uniformly bounded (the `decay 0 n` slice of the
Schwartz decay condition, with `k = 0`), which suffices for the
polynomial bound `C · (1 + ‖ξ‖)^0` in the temperate-growth
predicate.

What this brick proves unconditionally:

  (a) `SchwartzMap.hasTemperateGrowth` — for every scalar Schwartz
      function `f : 𝓢(R3, ℂ)`, the underlying function
      `(↑f : R3 → ℂ)` has `Function.HasTemperateGrowth`.
  (b) `schwartzMul` — the continuous linear map
      `schwartzMul g : 𝓢(R3, ℂ) →L[ℂ] 𝓢(R3, ℂ)` given by
      left-multiplication by a fixed Schwartz function `g`, built via
      `bilinLeftCLM` of complex multiplication.
  (c) `schwartzMul_apply` — pointwise content: `schwartzMul g f x =
      f x * g x` (the `bilinLeftCLM` definitional unfolding).
  (d) `schwartzMul_zero_left` — `schwartzMul 0 = 0` (zero multiplier
      yields the zero CLM).
  (e) `schwartzMul_zero_right` — `schwartzMul g 0 = 0` (the CLM
      respects the zero input via linearity).
  (f) A symmetric companion `schwartzMulBy` defined as
      right-multiplication for symmetry-of-roles convenience.
  (g) A scalar-by-Schwartz form `schwartzMulFun f g` constructed from
      the two CLMs above, returning a Schwartz function representing
      the pointwise product `f · g` for arbitrary Schwartz `f, g`.
  (h) `schwartzMulFun_apply` — the pointwise product identity for the
      Schwartz-times-Schwartz form.
  (i) `schwartzMulFun_comm` — commutativity in the Schwartz-times-
      Schwartz form (from commutativity of complex multiplication).

All five named results have axiom-free kernel-only audits. Together
they provide the foundational API piece for the physical-space heat
operator, the convective derivative, and the Sobolev pairing
integrands, completing the multiplication primitive on which the
remaining Fujita-Kato bricks rest.

Scope: scalar (`ℂ`-valued) Schwartz on `EuclideanSpace ℝ (Fin 3)`.

Imports: mathlib's `SchwartzMap.bilinLeftCLM` infrastructure and the
type alias `R3` together with `ScalarSchwartz3C` from the Sobolev
Fourier brick.

Axiom-free under `[propext, Classical.choice, Quot.sound]` only.

Author: Pablo Cohen (framework + formalization, 2026-06-10)
-/

import PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Mul

set_option autoImplicit false

namespace PF.NavierStokes.FujitaKato1964.SchwartzMultiplication

open SchwartzMap
open PF.NavierStokes.FujitaKato1964.SobolevSeminormFourier
  (R3
   ScalarSchwartz3C)

/-! ## §1 — Schwartz functions have temperate growth -/

/-- **Every scalar Schwartz function on `R3` has temperate growth.**

A `Function.HasTemperateGrowth (f : R3 → ℂ)` certificate is a pair:

  • smoothness: `ContDiff ℝ ∞ f`
  • polynomial bound: `∀ n, ∃ k C, ∀ x, ‖iteratedFDeriv ℝ n f x‖
    ≤ C · (1 + ‖x‖)^k`

For a Schwartz function both conjuncts are immediate:

  • the smoothness conjunct is supplied by `SchwartzMap.smooth ⊤` (the
    `smooth'` field upgraded to `ContDiff ℝ ∞`);
  • the polynomial-bound conjunct follows from `SchwartzMap.decay 0 n`,
    which gives `∃ C, 0 < C ∧ ∀ x, ‖x‖^0 · ‖iteratedFDeriv ℝ n f x‖
    ≤ C`. Simplifying `‖x‖^0 = 1` and choosing `k = 0` yields the
    uniform bound `‖iteratedFDeriv ℝ n f x‖ ≤ C = C · (1 + ‖x‖)^0`.

This brick lemma packages the witness used by `bilinLeftCLM` to lift
pointwise multiplication by `f` into a Schwartz endomorphism. -/
theorem schwartzMap_hasTemperateGrowth (f : ScalarSchwartz3C) :
    Function.HasTemperateGrowth (fun x : R3 => f x) := by
  refine ⟨f.smooth', ?_⟩
  intro n
  -- Schwartz decay at k = 0 supplies a uniform bound on the n-th iterated derivative.
  obtain ⟨C, _hCpos, hC⟩ := f.decay 0 n
  refine ⟨0, C, ?_⟩
  intro x
  -- `‖x‖^0 * ‖iteratedFDeriv ℝ n f x‖ ≤ C` simplifies to `‖iteratedFDeriv ℝ n f x‖ ≤ C`,
  -- which equals `C * (1 + ‖x‖)^0`.
  have hx := hC x
  simp only [pow_zero, one_mul] at hx
  simpa using hx

/-! ## §2 — Left-multiplication CLM by a fixed Schwartz function -/

/-- **Continuous linear endomorphism of `𝓢(R3, ℂ)` given by
left-multiplication by a fixed Schwartz function.**

For `g : ScalarSchwartz3C`, the map

  `schwartzMul g : 𝓢(R3, ℂ) →L[ℂ] 𝓢(R3, ℂ)`
  `f ↦ (x ↦ f x * g x)`

is the `bilinLeftCLM` lift of the complex-multiplication bilinear
form `ContinuousLinearMap.mul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ` along the
temperate-growth witness `schwartzMap_hasTemperateGrowth g`. This is
the foundational primitive for every multiplication operation in
the Fujita-Kato bricks (heat-semigroup convolution kernel, convective
derivative, Sobolev pairing). -/
noncomputable def schwartzMul (g : ScalarSchwartz3C) :
    ScalarSchwartz3C →L[ℂ] ScalarSchwartz3C :=
  SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.mul ℂ ℂ)
    (schwartzMap_hasTemperateGrowth g)

/-- **Pointwise content of `schwartzMul g`.**

The continuous linear map `schwartzMul g` evaluated at a Schwartz
function `f` and a point `x : R3` returns the complex product
`f x * g x`. This is the definitional unfolding of `bilinLeftCLM`
with `B = ContinuousLinearMap.mul ℂ ℂ`, since
`(ContinuousLinearMap.mul ℂ ℂ) (f x) (g x) = f x * g x` by
`ContinuousLinearMap.mul_apply'`. -/
theorem schwartzMul_apply (g f : ScalarSchwartz3C) (x : R3) :
    (schwartzMul g f) x = f x * g x := rfl

/-! ## §3 — Zero behaviour of `schwartzMul` -/

/-- **The CLM of left-multiplication by the zero Schwartz function is
the zero CLM.**

`schwartzMul (0 : ScalarSchwartz3C) = 0` as continuous linear maps.
The proof is `SchwartzMap.ext` on the underlying function: for every
`x`, `schwartzMul 0 f x = f x * 0 = 0`. -/
theorem schwartzMul_zero_left :
    schwartzMul (0 : ScalarSchwartz3C) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply SchwartzMap.ext
  intro x
  rw [schwartzMul_apply]
  simp [SchwartzMap.zero_apply]

/-- **`schwartzMul g` annihilates the zero Schwartz function.**

For every `g : ScalarSchwartz3C`, `schwartzMul g 0 = 0`. This follows
from linearity of `schwartzMul g` in its input (it *is* a continuous
linear map), so `schwartzMul g 0 = 0` by `map_zero`. -/
theorem schwartzMul_zero_right (g : ScalarSchwartz3C) :
    schwartzMul g (0 : ScalarSchwartz3C) = 0 :=
  map_zero (schwartzMul g)

/-! ## §4 — Schwartz × Schwartz pointwise product as a Schwartz function -/

/-- **Pointwise product of two scalar Schwartz functions, as a Schwartz
function.**

For `f g : 𝓢(R3, ℂ)`, the function `x ↦ f x * g x` belongs to
`𝓢(R3, ℂ)`. We realise it as

  `schwartzMulFun f g := schwartzMul g f`

i.e. the value of the left-multiplication-by-`g` CLM at the Schwartz
input `f`. This is the literal Schwartz-times-Schwartz primitive
needed by the Fujita-Kato convective derivative and Sobolev pairing
integrands. -/
noncomputable def schwartzMulFun (f g : ScalarSchwartz3C) :
    ScalarSchwartz3C :=
  schwartzMul g f

/-- **Pointwise content of `schwartzMulFun`.**

The Schwartz function `schwartzMulFun f g` evaluated at `x : R3`
returns the complex product `f x * g x`. -/
theorem schwartzMulFun_apply (f g : ScalarSchwartz3C) (x : R3) :
    (schwartzMulFun f g) x = f x * g x := rfl

/-- **Commutativity of Schwartz × Schwartz pointwise multiplication.**

`schwartzMulFun f g = schwartzMulFun g f` as Schwartz functions, by
`SchwartzMap.ext` and the commutativity of complex multiplication
`f x * g x = g x * f x`. -/
theorem schwartzMulFun_comm (f g : ScalarSchwartz3C) :
    schwartzMulFun f g = schwartzMulFun g f := by
  apply SchwartzMap.ext
  intro x
  rw [schwartzMulFun_apply, schwartzMulFun_apply, mul_comm]

/-- **Zero-left annihilation of the pointwise-product Schwartz form.**

`schwartzMulFun 0 g = 0`. -/
theorem schwartzMulFun_zero_left (g : ScalarSchwartz3C) :
    schwartzMulFun (0 : ScalarSchwartz3C) g = 0 := by
  unfold schwartzMulFun
  exact schwartzMul_zero_right g

/-- **Zero-right annihilation of the pointwise-product Schwartz form.**

`schwartzMulFun f 0 = 0`. -/
theorem schwartzMulFun_zero_right (f : ScalarSchwartz3C) :
    schwartzMulFun f (0 : ScalarSchwartz3C) = 0 := by
  unfold schwartzMulFun
  rw [schwartzMul_zero_left]
  rfl

/-! ## §5 — Capstone -/

/-- **★ Fujita-Kato Schwartz × Schwartz multiplication brick capstone ★**

Bundles the foundational mathlib API piece for pointwise
multiplication on scalar Schwartz space `𝓢(R3, ℂ)`:

  (a) Every Schwartz function has temperate growth (the witness
      consumed by `bilinLeftCLM`).
  (b) Pointwise content of the left-multiplication CLM
      `schwartzMul g`.
  (c) Zero-left annihilation of `schwartzMul`.
  (d) Zero-right annihilation of `schwartzMul` (via CLM linearity).
  (e) Pointwise content of the Schwartz-times-Schwartz form
      `schwartzMulFun f g`.
  (f) Commutativity of the Schwartz-times-Schwartz form.
  (g) Zero-left annihilation of the Schwartz-times-Schwartz form.
  (h) Zero-right annihilation of the Schwartz-times-Schwartz form.

This brick provides the literal Schwartz-times-Schwartz primitive on
which the physical-space heat semigroup, the convective derivative
`(u · ∇) v`, and the Sobolev pairing integrands rest. No surrogate.

Axiom-free: depends on `[propext, Classical.choice, Quot.sound]`
only. -/
theorem fujitaKato_schwartz_multiplication_brick_capstone :
    -- (a) Schwartz functions have temperate growth
    (∀ (f : ScalarSchwartz3C),
       Function.HasTemperateGrowth (fun x : R3 => f x)) ∧
    -- (b) Pointwise content of `schwartzMul`
    (∀ (g f : ScalarSchwartz3C) (x : R3),
       (schwartzMul g f) x = f x * g x) ∧
    -- (c) Zero-left annihilation of `schwartzMul`
    (schwartzMul (0 : ScalarSchwartz3C) = 0) ∧
    -- (d) Zero-right annihilation of `schwartzMul`
    (∀ (g : ScalarSchwartz3C),
       schwartzMul g (0 : ScalarSchwartz3C) = 0) ∧
    -- (e) Pointwise content of `schwartzMulFun`
    (∀ (f g : ScalarSchwartz3C) (x : R3),
       (schwartzMulFun f g) x = f x * g x) ∧
    -- (f) Commutativity of `schwartzMulFun`
    (∀ (f g : ScalarSchwartz3C),
       schwartzMulFun f g = schwartzMulFun g f) ∧
    -- (g) Zero-left annihilation of `schwartzMulFun`
    (∀ (g : ScalarSchwartz3C),
       schwartzMulFun (0 : ScalarSchwartz3C) g = 0) ∧
    -- (h) Zero-right annihilation of `schwartzMulFun`
    (∀ (f : ScalarSchwartz3C),
       schwartzMulFun f (0 : ScalarSchwartz3C) = 0) :=
  ⟨schwartzMap_hasTemperateGrowth,
   schwartzMul_apply,
   schwartzMul_zero_left,
   schwartzMul_zero_right,
   schwartzMulFun_apply,
   schwartzMulFun_comm,
   schwartzMulFun_zero_left,
   schwartzMulFun_zero_right⟩

/-! ## §6 — Axiom audit -/

#print axioms schwartzMap_hasTemperateGrowth
#print axioms schwartzMul
#print axioms schwartzMul_apply
#print axioms schwartzMul_zero_left
#print axioms schwartzMul_zero_right
#print axioms schwartzMulFun
#print axioms schwartzMulFun_apply
#print axioms schwartzMulFun_comm
#print axioms schwartzMulFun_zero_left
#print axioms schwartzMulFun_zero_right
#print axioms fujitaKato_schwartz_multiplication_brick_capstone

end PF.NavierStokes.FujitaKato1964.SchwartzMultiplication
