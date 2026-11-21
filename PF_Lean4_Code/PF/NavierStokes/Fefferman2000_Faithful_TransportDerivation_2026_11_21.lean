/-
# Completing the vorticity transport derivation

**Date**: 2026-11-21 (Legion).

`Fefferman2000_Faithful_Exchange_2026_11_21.lean` §4 itemised what the
transport equation's derivation still needed. This file works through
that list.

## §1 — The Laplacian is the sum of second partials

mathlib defines `InnerProductSpace.laplacian` as
`tensorIteratedFDerivTwo` applied to the canonical covariant tensor,
which is basis-free and right, but useless for a componentwise
calculation. Every coordinate argument about `Δ` needs

    `Δf x = ∑ᵢ ∂ᵢ∂ᵢ f x`

and mathlib supplies the pieces: `laplacian_eq_iteratedFDeriv_orthonormalBasis`
for an arbitrary orthonormal basis, `EuclideanSpace.basisFun` whose `i`-th
vector is `EuclideanSpace.single i 1`, and `iteratedFDeriv_two_apply` to
turn the order-2 iterated derivative into a nested `fderiv`. Composing
them gives the identification, for any target normed space.

This was named in the exchange file as "the clean missing lemma" blocking
`curl(Δu) = Δ(curl u)`, and it is reusable anywhere the corpus touches
the Laplacian.
-/

import PF.NavierStokes.Fefferman2000_Faithful_Exchange_2026_11_21

namespace PF.NavierStokes.FeffermanFaithful

/-- **The Laplacian is the sum of second partial derivatives.**

    `Δf x = ∑ᵢ D²f x eᵢ eᵢ`, with `eᵢ = EuclideanSpace.single i 1`.

    Bridges mathlib's basis-free `tensorIteratedFDerivTwo` definition to
    the coordinate form every componentwise argument needs. Stated for an
    arbitrary target space, so it serves both the scalar pressure and the
    vector velocity. -/
theorem laplacian_eq_sum_second_partials {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : V → F) (x : V) :
    InnerProductSpace.laplacian f x
      = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
        (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

/-- Componentwise form: the `k`-th coordinate of the Laplacian of a
    vector field is the sum of the second partials of its `k`-th
    coordinate. -/
theorem laplacian_apply_eq_sum (f : V → V) (x : V) (k : Fin 3) :
    (InnerProductSpace.laplacian f x) k
      = ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ))) k := by
  rw [laplacian_eq_sum_second_partials f x]
  rw [Finset.sum_apply]

/-! ## §2 — Third-order symmetry

mathlib has symmetry for the second derivative only: `IsSymmSndFDerivAt`,
and nothing above order 2. The Laplacian exchange needs order 3, because
`Δ` is two derivatives and `curl` adds one.

It is reachable from the order-2 result in two different ways, one for
each adjacent transposition of the three derivative slots. Writing
`D³f(a,b,c)` for `fderiv (fderiv (fderiv f)) x a b c` (outermost slot
first):

* **slots 1↔2** — apply order-2 symmetry to the *derivative map*
  `fderiv f`, which is `C²` when `f` is `C³`;
* **slots 2↔3** — the order-2 symmetry of `f` itself is an identity
  holding at every nearby point, so it can be *differentiated*; the two
  sides have equal derivatives, which is exactly the 2↔3 exchange.

Those two transpositions generate all six permutations, so the third
derivative is fully symmetric. The cyclic case is what the Laplacian
exchange uses. -/

section ThirdOrder

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Differentiating through evaluation of an operator-valued map at a
    fixed vector: `D(y ↦ g y v) = (eval at v) ∘ Dg`. -/
theorem fderiv_eval (g : V → (V →L[ℝ] W)) (x v : V) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => g y v) x
      = (ContinuousLinearMap.apply ℝ W v).comp (fderiv ℝ g x) :=
  ((ContinuousLinearMap.apply ℝ W v).hasFDerivAt.comp x hg.hasFDerivAt).fderiv

/-- Applied form of `fderiv_eval`. -/
theorem fderiv_eval_apply (g : V → (V →L[ℝ] W)) (x v a : V)
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => g y v) x a = (fderiv ℝ g x a) v := by
  rw [fderiv_eval g x v hg]; rfl

/-- An operator-valued map evaluated at a fixed vector stays
    differentiable. -/
theorem differentiableAt_eval (g : V → (V →L[ℝ] W)) (x v : V)
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun y => g y v) x :=
  ((ContinuousLinearMap.apply ℝ W v).hasFDerivAt.comp x hg.hasFDerivAt).differentiableAt

/-- For a `C³` function the second-derivative map is differentiable. -/
theorem differentiableAt_fderiv_fderiv (f : V → W) (x : V)
    (hf : ContDiffAt ℝ 3 f x) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) x := h2.fderiv_right (by norm_num)
  exact h1.differentiableAt (le_refl _)

/-- **Third derivative, slots 1↔2.** Order-2 symmetry applied to the
    derivative map `fderiv f`, which is `C²` because `f` is `C³`. -/
theorem third_deriv_swap_12 (f : V → W) (x : V) (hf : ContDiffAt ℝ 3 f x)
    (a b c : V) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b a c := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  rw [h2.isSymmSndFDerivAt (by simp) a b]

/-- The order-2 symmetry of a `C³` function holds at every nearby point,
    as an identity of functions of the base point — which is what makes
    it differentiable. -/
theorem sndDeriv_symm_eventually (f : V → W) (x : V) (hf : ContDiffAt ℝ 3 f x)
    (b c : V) :
    (fun y => fderiv ℝ (fderiv ℝ f) y b c) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fderiv ℝ f) y c b) := by
  have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 3 f y := hf.eventually (by norm_num)
  filter_upwards [hev] with y hy
  have h2 : ContDiffAt ℝ 2 f y := hy.of_le (by norm_num)
  exact h2.isSymmSndFDerivAt (by simp) b c

/-- **Third derivative, slots 2↔3.** Differentiate the order-2 symmetry
    of `f`: the two sides agree near `x`, hence have the same derivative
    there, and unwinding the evaluations turns that into the 2↔3
    exchange. -/
theorem third_deriv_swap_23 (f : V → W) (x : V) (hf : ContDiffAt ℝ 3 f x)
    (a b c : V) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a c b := by
  have hdF2 : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    differentiableAt_fderiv_fderiv f x hf
  have hgb : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ f) y b) x :=
    differentiableAt_eval _ x b hdF2
  have hgc : DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ f) y c) x :=
    differentiableAt_eval _ x c hdF2
  have hd : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y b c) x
      = fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y c b) x :=
    (sndDeriv_symm_eventually f x hf b c).fderiv_eq
  have hL : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y b c) x a
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c := by
    rw [fderiv_eval_apply (fun y => fderiv ℝ (fderiv ℝ f) y b) x c a hgb,
        fderiv_eval_apply (fderiv ℝ (fderiv ℝ f)) x b a hdF2]
  have hR : fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ f) y c b) x a
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a c b := by
    rw [fderiv_eval_apply (fun y => fderiv ℝ (fderiv ℝ f) y c) x b a hgc,
        fderiv_eval_apply (fderiv ℝ (fderiv ℝ f)) x c a hdF2]
  rw [← hL, ← hR, hd]

/-- **★ Third derivative, cyclic permutation**: `D³f(a,b,c) = D³f(b,c,a)`.

    The composition of the two adjacent transpositions. This is the form
    the Laplacian exchange needs: it moves the `curl` direction from the
    outermost slot to the innermost, past the two Laplacian slots. -/
theorem third_deriv_cycle (f : V → W) (x : V) (hf : ContDiffAt ℝ 3 f x)
    (a b c : V) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b c
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b c a := by
  rw [third_deriv_swap_12 f x hf a b c, third_deriv_swap_23 f x hf b a c]

/-- The case the Laplacian exchange uses: moving a direction past two
    equal directions. `D³f(a,b,b) = D³f(b,b,a)`. -/
theorem third_deriv_move_past_pair (f : V → W) (x : V) (hf : ContDiffAt ℝ 3 f x)
    (a b : V) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x a b b
      = fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x b b a :=
  third_deriv_cycle f x hf a b b

end ThirdOrder

#print axioms laplacian_eq_sum_second_partials
#print axioms laplacian_apply_eq_sum
#print axioms third_deriv_swap_12
#print axioms third_deriv_swap_23
#print axioms third_deriv_cycle
#print axioms third_deriv_move_past_pair

end PF.NavierStokes.FeffermanFaithful
