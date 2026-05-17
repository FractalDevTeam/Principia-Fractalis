/-
# Lipschitz Bounds for the Cantor IFS Contractions

The Cantor IFS contractions `f₁(x) = x/3` and `f₂(x) = (x+2)/3`
are both `(1/3)`-Lipschitz. Composition with a `LipschitzWith L`
function gives a `(L/3)`-Lipschitz function.

This is the analytic engine for the Banach contraction argument:
iterating the Hutchinson difference recursion against a Lipschitz
test function gives a geometric `(1/3)^n` rate, proving weak
convergence `cantorDiscMeasure n → μ_H`.

This file:
* Proves `cantorContraction1, cantorContraction2 : LipschitzWith (1/3)`.
* Proves composition `f ∘ cantorContraction_i : LipschitzWith (L · 1/3)`.

Stage L4+ — Lipschitz infrastructure for weak-* convergence.
-/

import PF.Analytic.Hutchinson

namespace PrincipiaTractalis.Analytic

open MeasureTheory NNReal

/-! ## Lipschitz constants of the two IFS contractions -/

/-- **`cantorContraction1` is `(1/3)`-Lipschitz**.

    `f₁(x) = x/3`, so `dist(f₁(x), f₁(y)) = |x − y|/3 = (1/3)·dist(x, y)`. -/
theorem cantorContraction1_lipschitz :
    LipschitzWith ((1 : ℝ≥0) / 3) cantorContraction1 := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  unfold cantorContraction1
  rw [Real.dist_eq, Real.dist_eq]
  have : x / 3 - y / 3 = (x - y) / 3 := by ring
  rw [this, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  -- want: |x - y| / 3 ≤ ↑(1/3) * |x - y|
  have hcoe : (((1 : ℝ≥0) / 3 : ℝ≥0) : ℝ) = 1/3 := by
    push_cast; norm_num
  rw [hcoe]
  ring_nf
  rfl

/-- **`cantorContraction2` is `(1/3)`-Lipschitz**.

    `f₂(x) = (x + 2)/3`, so `dist(f₂(x), f₂(y)) = |x − y|/3 = (1/3)·dist(x, y)`. -/
theorem cantorContraction2_lipschitz :
    LipschitzWith ((1 : ℝ≥0) / 3) cantorContraction2 := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  unfold cantorContraction2
  rw [Real.dist_eq, Real.dist_eq]
  have : (x + 2) / 3 - (y + 2) / 3 = (x - y) / 3 := by ring
  rw [this, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have hcoe : (((1 : ℝ≥0) / 3 : ℝ≥0) : ℝ) = 1/3 := by
    push_cast; norm_num
  rw [hcoe]
  ring_nf
  rfl

/-! ## Composition with Lipschitz functions -/

/-- **Composition Lipschitz bound (left contraction)**:

    If `f : ℝ → ℝ` is `LipschitzWith L`, then `f ∘ f₁` is
    `LipschitzWith (L · (1/3))`.

    This is the key bound for iterating the difference recursion:
    each level of Hutchinson iteration shrinks the effective
    Lipschitz constant of the test function by `1/3`. -/
theorem lipschitzWith_comp_cantorContraction1 {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    LipschitzWith (L * (1 / 3)) (fun x => f (cantorContraction1 x)) :=
  hf.comp cantorContraction1_lipschitz

/-- **Composition Lipschitz bound (right contraction)**:

    If `f : ℝ → ℝ` is `LipschitzWith L`, then `f ∘ f₂` is
    `LipschitzWith (L · (1/3))`. -/
theorem lipschitzWith_comp_cantorContraction2 {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) :
    LipschitzWith (L * (1 / 3)) (fun x => f (cantorContraction2 x)) :=
  hf.comp cantorContraction2_lipschitz

/-! ## ★ Iterated composition: the (1/3)ⁿ shrinkage ★ -/

/-- **Iterated composition along an `n`-step IFS word**: the function

      `g_{bs} := f ∘ f_{b_{n−1}} ∘ ⋯ ∘ f_{b_0}`

    (built by composing with one cell contraction per boolean in
    `bs`, head-first inside-out, matching the `cellMidpointOfBools`
    structure) is `LipschitzWith (L · (1/3)^n)`.

    This is the explicit shrinkage of the test function's Lipschitz
    constant under `n` iterations of the Hutchinson recursion. -/
noncomputable def iteratedIFSComp (f : ℝ → ℝ) : List Bool → (ℝ → ℝ)
  | [] => f
  | false :: bs => fun x => iteratedIFSComp f bs (cantorContraction1 x)
  | true :: bs => fun x => iteratedIFSComp f bs (cantorContraction2 x)

theorem iteratedIFSComp_nil (f : ℝ → ℝ) : iteratedIFSComp f [] = f := rfl

theorem iteratedIFSComp_false_cons (f : ℝ → ℝ) (bs : List Bool) :
    iteratedIFSComp f (false :: bs) =
    (fun x => iteratedIFSComp f bs (cantorContraction1 x)) := rfl

theorem iteratedIFSComp_true_cons (f : ℝ → ℝ) (bs : List Bool) :
    iteratedIFSComp f (true :: bs) =
    (fun x => iteratedIFSComp f bs (cantorContraction2 x)) := rfl

/-- **★ Iterated Lipschitz bound ★**:

    For `f : ℝ → ℝ` `LipschitzWith L` and any length-`n` boolean
    word `bs`, the iterated composition `iteratedIFSComp f bs` is
    `LipschitzWith (L · (1/3)^n)` — the test function's Lipschitz
    constant shrinks by `1/3` at every level. -/
theorem iteratedIFSComp_lipschitz {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (bs : List Bool) :
    LipschitzWith (L * (1/3)^bs.length) (iteratedIFSComp f bs) := by
  induction bs generalizing L with
  | nil =>
    simp [iteratedIFSComp]
    exact hf
  | cons b bs ih =>
    cases b
    · -- false :: bs
      rw [iteratedIFSComp_false_cons]
      have hcomp : LipschitzWith (L * (1/3)^bs.length * (1/3))
                                  (fun x => iteratedIFSComp f bs
                                              (cantorContraction1 x)) :=
        (ih hf).comp cantorContraction1_lipschitz
      have hpow : L * (1/3)^bs.length * (1/3) =
                  L * (1/3)^(false :: bs).length := by
        simp [List.length_cons, pow_succ]
        ring
      rw [hpow] at hcomp
      exact hcomp
    · -- true :: bs
      rw [iteratedIFSComp_true_cons]
      have hcomp : LipschitzWith (L * (1/3)^bs.length * (1/3))
                                  (fun x => iteratedIFSComp f bs
                                              (cantorContraction2 x)) :=
        (ih hf).comp cantorContraction2_lipschitz
      have hpow : L * (1/3)^bs.length * (1/3) =
                  L * (1/3)^(true :: bs).length := by
        simp [List.length_cons, pow_succ]
        ring
      rw [hpow] at hcomp
      exact hcomp

/-! ## Documentation: the Banach contraction argument

For a Lipschitz test function `f : ℝ → ℝ` with constant `L`, the
difference recursion `integral_difference_recursion` plus the
composition bounds above give:

  `|∫ f d(cantorDiscMeasure (n+1)) − ∫ f dμ|
    ≤ (1/2) · |∫ (f ∘ f₁) d(cantorDiscMeasure n) − ∫ (f ∘ f₁) dμ|
    + (1/2) · |∫ (f ∘ f₂) d(cantorDiscMeasure n) − ∫ (f ∘ f₂) dμ|`

Each integrand `f ∘ f_i` is Lipschitz with constant `L · (1/3)`.

Iterating `n` times, the test function's effective Lipschitz constant
is `L · (1/3)^n`, so the integral difference is bounded by
`L · (1/3)^n · (diam[0,1]) = L · (1/3)^n`.

For any bounded Lipschitz test function `f`, this gives the geometric
weak-convergence rate `cantorDiscMeasure n → μ_H` with rate `(1/3)^n`.

The full proof requires (a) `integral_difference_recursion` (already
in `Hutchinson.lean`), (b) the composition bounds above, (c) the
iteration argument (induction on `n`), and (d) the integration bound
`|∫ g dμ| ≤ ‖g‖_∞ for finite measure μ`. This file delivers (b);
(a) is already done; (c) and (d) are pending.

By the Bounded-Lipschitz characterisation of weak-* convergence
(Portmanteau / Kantorovich-Rubinstein duality), weak convergence on
the Lipschitz test functions extends to weak-* convergence of measures.

This gives the complete Banach-contraction-style argument for
`cantorDiscMeasure n → μ_H` weakly with geometric rate `(1/3)^n`.
-/

end PrincipiaTractalis.Analytic
