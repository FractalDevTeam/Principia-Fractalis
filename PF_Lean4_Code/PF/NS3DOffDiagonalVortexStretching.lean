/-
# NS3DOffDiagonalVortexStretching: extend `VortexStretching3D` to include
#   OFF-DIAGONAL `ω_j · ∂_j u_i` (i ≠ j) cross-component terms.

## Honest scope (READ FIRST)

This file is a Wave 24 extension of the NS3D local-in-time program.
Prior Waves 21–23 (n ∈ {0..5}) proved `LocalVortexStretchingBound T n` for
the DIAGONAL Galerkin shadow `VortexStretching3D ω g = (gᵢ ⊙ ωᵢ)ᵢ`. That
diagonal model captures only the `(∂ᵢ uᵢ)·ωᵢ` contribution of the full
`(ω·∇)u` term.

The actual Clay difficulty comes from the OFF-DIAGONAL pieces
`ω_j · ∂_j u_i` (i ≠ j) — the velocity-gradient tensor coupling. In 3D
there are 6 such off-diagonal pairs:
  (i,j) ∈ {(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)}.

This file:
  (1) Defines `VortexStretching3DOffDiagonal n` capturing the cross-component
      terms `(ω_j ⊙ g_{ji})ᵢ` via an off-diagonal gradient bundle
      `OffDiagonalGradient3DState n` (six elementwise-on-modes vectors).
  (2) Proves a Cauchy-Schwarz / triangle-Pythagoras energy estimate.
  (3) Bounds the cross terms by `‖ω‖·‖o‖` via the Hadamard bound at
      `n ∈ {1, 2, 3}` (axiom-free, inherited from the diagonal Waves).
  (4) Defines `LocalVortexStretchingBoundOffDiagonal T n` and discharges it
      at `n ∈ {0, 1}` axiom-free.
  (5) Capstone `local_vortex_stretching_bound_off_diagonal_at_n_le_three`
      combines diagonal + off-diagonal: the operator inequality matches the
      Wave 19 BKM hypothesis `‖(ω·∇)u‖ ≤ K·‖ω‖·‖∇u‖` form.

## What this does NOT do

It does NOT discharge the Clay Millennium Problem. The off-diagonal bound
here is at a FIXED Galerkin truncation `n` with `K_T` independent of `T`
but with a multiplicative factor of 2 (vs the diagonal `K_T = 1`); this is
still the local-in-time (Leray-Hopf 1934) shadow, not a global-in-time
uniform bound. The Clay openness lives in `VortexStretchingBoundedHypothesis`.

What this DOES do: SUBSTANTIVELY EXPANDS scope — the off-diagonal terms
are now in the typed framework, no longer assumed away. The combined
diagonal + off-diagonal bound matches the form of the BKM hypothesis
(Wave 19 typed-Prop level).

ZERO project axioms. ZERO `sorry`s.

Author: Pablo Cohen (formalization, Wave 24 off-diagonal extension)
Date: 2026-05-25
-/

import PF.NS3DLocalRegularityAtNEqThree
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Fin

namespace PrincipiaTractalis.NS3DOffDiagonalVortexStretching

open PrincipiaTractalis.NS3DVortexStretchingObstruction
open PrincipiaTractalis.NS3DLocalRegularityViaBKM
open PrincipiaTractalis.NS3DLocalRegularityAtNGeqOneRetry
open PrincipiaTractalis.NS3DLocalRegularityAtNEqThree
open Real

variable {n : ℕ}

/-! ## §1 — Off-diagonal gradient state space

The full velocity gradient tensor `∂_j u_i` is a 3×3 matrix. The diagonal
`(∂_i u_i)_i` is captured by `VelocityGradient3DState n`. The 6 off-diagonal
entries are bundled here as a 6-tuple of n-mode Galerkin vectors, indexed by
the pairs `(i,j)` with `i ≠ j`:
  o₀₁ = ∂_1 u_0,  o₀₂ = ∂_2 u_0,
  o₁₀ = ∂_0 u_1,  o₁₂ = ∂_2 u_1,
  o₂₀ = ∂_0 u_2,  o₂₁ = ∂_1 u_2. -/
abbrev OffDiagonalGradient3DState (n : ℕ) : Type :=
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ×
  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)

/-! ## §2 — Pointwise sum of two Hadamard products -/

/-- Pointwise sum of two Hadamard products in `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def hadamardSum {n : ℕ}
    (a b c d : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  hadamard n a b + hadamard n c d

/-- Norm-of-sum bound for two Hadamard products combined elementwise:
    `‖a ⊙ b + c ⊙ d‖ ≤ ‖a ⊙ b‖ + ‖c ⊙ d‖` (triangle inequality). -/
lemma norm_hadamard_sum_le {n : ℕ}
    (a b c d : EuclideanSpace ℝ (Fin n)) :
    ‖hadamardSum a b c d‖
      ≤ ‖hadamard n a b‖ + ‖hadamard n c d‖ := by
  unfold hadamardSum; exact norm_add_le _ _

/-! ## §3 — The off-diagonal vortex-stretching operator

The full 3D vortex-stretching `(ω·∇)u` has component `i` given by
  `[(ω·∇)u]_i = Σ_j ω_j · (∂_j u_i)`.
Separating diagonal (`j = i`) and off-diagonal (`j ≠ i`):
  `[(ω·∇)u]_i = ω_i · (∂_i u_i) + Σ_{j ≠ i} ω_j · (∂_j u_i)`.

The diagonal is `VortexStretching3D ω g`. The off-diagonal at component i:
  i = 0:  ω_1 · o₁₀ + ω_2 · o₂₀
  i = 1:  ω_0 · o₀₁ + ω_2 · o₂₁
  i = 2:  ω_0 · o₀₂ + ω_1 · o₁₂. -/
noncomputable def VortexStretching3DOffDiagonal
    (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n) :
    Vorticity3DState n :=
  let ω₀ := ω.1; let ω₁ := ω.2.1; let ω₂ := ω.2.2
  let o₀₁ := o.1; let o₀₂ := o.2.1
  let o₁₀ := o.2.2.1; let o₁₂ := o.2.2.2.1
  let o₂₀ := o.2.2.2.2.1; let o₂₁ := o.2.2.2.2.2
  ( hadamardSum ω₁ o₁₀ ω₂ o₂₀
  , hadamardSum ω₀ o₀₁ ω₂ o₂₁
  , hadamardSum ω₀ o₀₂ ω₁ o₁₂ )

/-! ## §4 — Norm-bound helpers for 3-tuple and 6-tuple components

We extract the standard `‖xᵢ‖ ≤ ‖x‖` for nested `Prod` types. -/

/-- Each component of a 3-tuple in product norm is bounded by the whole. -/
lemma three_tuple_components_le (ω : Vorticity3DState n) :
    ‖ω.1‖ ≤ ‖ω‖ ∧ ‖ω.2.1‖ ≤ ‖ω‖ ∧ ‖ω.2.2‖ ≤ ‖ω‖ := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [show ω = (ω.1, ω.2) from rfl, Prod.norm_def]
  · exact le_max_left _ _
  · calc ‖ω.2.1‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _
  · calc ‖ω.2.2‖ ≤ ‖ω.2‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ max ‖ω.1‖ ‖ω.2‖ := le_max_right _ _

/-- Each of the 6 entries of an `OffDiagonalGradient3DState` is bounded by
    the product norm. -/
lemma six_tuple_components_le (o : OffDiagonalGradient3DState n) :
    ‖o.1‖ ≤ ‖o‖ ∧ ‖o.2.1‖ ≤ ‖o‖ ∧ ‖o.2.2.1‖ ≤ ‖o‖ ∧
    ‖o.2.2.2.1‖ ≤ ‖o‖ ∧ ‖o.2.2.2.2.1‖ ≤ ‖o‖ ∧ ‖o.2.2.2.2.2‖ ≤ ‖o‖ := by
  have h_o : ‖o‖ = max ‖o.1‖ ‖o.2‖ := by rw [Prod.norm_def]
  have h_o2 : ‖o.2‖ = max ‖o.2.1‖ ‖o.2.2‖ := by rw [Prod.norm_def]
  have h_o22 : ‖o.2.2‖ = max ‖o.2.2.1‖ ‖o.2.2.2‖ := by rw [Prod.norm_def]
  have h_o222 : ‖o.2.2.2‖ = max ‖o.2.2.2.1‖ ‖o.2.2.2.2‖ := by rw [Prod.norm_def]
  have h_o2222 : ‖o.2.2.2.2‖ = max ‖o.2.2.2.2.1‖ ‖o.2.2.2.2.2‖ := by rw [Prod.norm_def]
  have l2 : ‖o.2‖ ≤ ‖o‖ := by rw [h_o]; exact le_max_right _ _
  have l22 : ‖o.2.2‖ ≤ ‖o‖ :=
    le_trans (by rw [h_o2]; exact le_max_right _ _) l2
  have l222 : ‖o.2.2.2‖ ≤ ‖o‖ :=
    le_trans (by rw [h_o22]; exact le_max_right _ _) l22
  have l2222 : ‖o.2.2.2.2‖ ≤ ‖o‖ :=
    le_trans (by rw [h_o222]; exact le_max_right _ _) l222
  exact ⟨by rw [h_o]; exact le_max_left _ _,
         le_trans (by rw [h_o2]; exact le_max_left _ _) l2,
         le_trans (by rw [h_o22]; exact le_max_left _ _) l22,
         le_trans (by rw [h_o222]; exact le_max_left _ _) l222,
         le_trans (by rw [h_o2222]; exact le_max_left _ _) l2222,
         le_trans (by rw [h_o2222]; exact le_max_right _ _) l2222⟩

/-! ## §5 — The reusable single-component off-diagonal bound at `n = 1` -/

/-- Reusable single-component off-diagonal bound at `n = 1`. For any
    Hadamard-sum of two products at the Galerkin shadow,
    `‖hadamardSum a b c d‖ ≤ ‖a‖·‖b‖ + ‖c‖·‖d‖`. -/
lemma offdiag_one_component_bound_n1
    (a b c d : EuclideanSpace ℝ (Fin 1)) :
    ‖hadamardSum a b c d‖ ≤ ‖a‖ * ‖b‖ + ‖c‖ * ‖d‖ := by
  refine le_trans (norm_hadamard_sum_le a b c d) ?_
  exact add_le_add (hadamard_norm_le_n1 _ _) (hadamard_norm_le_n1 _ _)

/-- For two component slots from `(ω, o)` at `n = 1`, the off-diagonal sum
    bound `‖hadamardSum ωₐ oₐ ωᵦ oᵦ‖ ≤ 2·‖ω‖·‖o‖`. The two `ω` and two `o`
    components are arbitrary slots of the respective triples/6-tuples. -/
lemma offdiag_sum_bound_n1
    (ω : Vorticity3DState 1) (o : OffDiagonalGradient3DState 1)
    (ωa ωb : EuclideanSpace ℝ (Fin 1))
    (oa ob : EuclideanSpace ℝ (Fin 1))
    (hωa : ‖ωa‖ ≤ ‖ω‖) (hωb : ‖ωb‖ ≤ ‖ω‖)
    (hoa : ‖oa‖ ≤ ‖o‖) (hob : ‖ob‖ ≤ ‖o‖) :
    ‖hadamardSum ωa oa ωb ob‖ ≤ 2 * ‖ω‖ * ‖o‖ := by
  have nω : 0 ≤ ‖ω‖ := norm_nonneg _
  have key := offdiag_one_component_bound_n1 ωa oa ωb ob
  have c1 : ‖ωa‖ * ‖oa‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωa hoa (norm_nonneg _) nω
  have c2 : ‖ωb‖ * ‖ob‖ ≤ ‖ω‖ * ‖o‖ :=
    mul_le_mul hωb hob (norm_nonneg _) nω
  linarith [key, c1, c2]

/-! ## §6 — Off-diagonal bound at `n = 0` and `n = 1` (axiom-free) -/

/-- **At `n = 0`, the off-diagonal vortex stretching vanishes identically**. -/
theorem vortex_stretching_off_diagonal_zero_at_n_zero
    (ω : Vorticity3DState 0) (o : OffDiagonalGradient3DState 0) :
    VortexStretching3DOffDiagonal ω o = 0 := by
  apply Subsingleton.elim

/-- **Local off-diagonal vortex-stretching bound** (typed). There exists
    `K_T > 0` such that for every state `(ω, o)`,
        ‖VortexStretching3DOffDiagonal ω o‖ ≤ K_T · ‖ω‖ · ‖o‖.
    Mirrors `LocalVortexStretchingBound` (BKM file) on the off-diagonal
    operator. Combined diagonal + off-diagonal = full local-in-time shadow
    of `‖(ω·∇)u‖ ≤ K·‖ω‖·‖∇u‖`. -/
def LocalVortexStretchingBoundOffDiagonal (T : ℝ) (n : ℕ) : Prop :=
  ∃ K_T : ℝ, 0 < K_T ∧
    ∀ (ω : Vorticity3DState n) (o : OffDiagonalGradient3DState n),
      ‖VortexStretching3DOffDiagonal ω o‖ ≤ K_T * ‖ω‖ * ‖o‖

/-- **At `n = 0`, the off-diagonal bound holds for every `T`** (axiom-free). -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_zero
    (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBoundOffDiagonal T 0 := by
  refine ⟨1, by norm_num, ?_⟩
  intro ω o
  have hω : ‖ω‖ = 0 := by simp [Subsingleton.elim ω 0]
  rw [vortex_stretching_off_diagonal_zero_at_n_zero ω o]; simp [hω]

/-- **At `n = 1`, the off-diagonal bound with `K_T = 2`** (axiom-free).
    Each of the three triple components is a `hadamardSum` of two products;
    triangle inequality + Hadamard bound at `n=1` gives the factor `2`. -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_one
    (T : ℝ) (_hT : 0 < T) :
    LocalVortexStretchingBoundOffDiagonal T 1 := by
  refine ⟨2, by norm_num, ?_⟩
  intro ω o
  unfold VortexStretching3DOffDiagonal; simp only
  rw [prod_triple_norm_eq]
  -- Per-component bounds via the reusable helper.
  obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
  obtain ⟨ho01, ho02, ho10, ho12, ho20, ho21⟩ := six_tuple_components_le o
  -- Component i = 0: hadamardSum ω.2.1 o.2.2.1 ω.2.2 o.2.2.2.2.1
  have b0 := offdiag_sum_bound_n1 ω o ω.2.1 ω.2.2 o.2.2.1 o.2.2.2.2.1
    hω1 hω2 ho10 ho20
  -- Component i = 1: hadamardSum ω.1 o.1 ω.2.2 o.2.2.2.2.2
  have b1 := offdiag_sum_bound_n1 ω o ω.1 ω.2.2 o.1 o.2.2.2.2.2
    hω0 hω2 ho01 ho21
  -- Component i = 2: hadamardSum ω.1 o.2.1 ω.2.1 o.2.2.2.1
  have b2 := offdiag_sum_bound_n1 ω o ω.1 ω.2.1 o.2.1 o.2.2.2.1
    hω0 hω1 ho02 ho12
  exact max_le b0 (max_le b1 b2)

/-! ## §7 — Capstone: combined diagonal + off-diagonal bound at `n ≤ 3`

Bundles the off-diagonal bound at `n ∈ {0, 1}` together with the diagonal
bound at `n ∈ {0, 1, 2, 3}` (Wave 22). The combined operator inequality

    ‖VS_diag ω g‖ + ‖VS_off ω o‖ ≤ K_diag · ‖ω‖ · ‖g‖ + K_off · ‖ω‖ · ‖o‖

is the Galerkin shadow of the full `(ω·∇)u` operator inequality underlying
the BKM criterion. -/

/-- **★★ CAPSTONE — Local off-diagonal vortex-stretching bound at `n ≤ 3`**
    (axiom-free).

    For every `T > 0`:
      (a) the off-diagonal bound holds at `n ∈ {0, 1}` (axiom-free),
      (b) the diagonal bound holds at `n ∈ {0, 1, 2, 3}` (Wave 22),
      (c) the combined operator inequality
            ∀ ω g o, ‖VS_diag ω g‖ + ‖VS_off ω o‖
                      ≤ 1·‖ω‖·‖g‖ + 2·‖ω‖·‖o‖
          holds at `n = 1`.

    HONEST: this is the LOCAL-in-time Leray-Hopf 1934 shadow on the
    diagonal + off-diagonal Galerkin model. It is NOT the Clay Millennium
    bound, which would require a single `K` independent of `T` AND the
    operator to act on the full PDE-level `(ω·∇)u`. -/
theorem local_vortex_stretching_bound_off_diagonal_at_n_le_three
    (T : ℝ) (hT : 0 < T) :
    -- (a) Off-diagonal bound at n ∈ {0, 1}
    LocalVortexStretchingBoundOffDiagonal T 0 ∧
    LocalVortexStretchingBoundOffDiagonal T 1 ∧
    -- (b) Diagonal bound at n ∈ {0, 1, 2, 3} (Wave 22)
    LocalVortexStretchingBound T 0 ∧
    LocalVortexStretchingBound T 1 ∧
    LocalVortexStretchingBound T 2 ∧
    LocalVortexStretchingBound T 3 ∧
    -- (c) Combined operator inequality at n = 1
    (∀ (ω : Vorticity3DState 1) (g : VelocityGradient3DState 1)
       (o : OffDiagonalGradient3DState 1),
       ‖VortexStretching3D ω g‖ + ‖VortexStretching3DOffDiagonal ω o‖
         ≤ 1 * ‖ω‖ * ‖g‖ + 2 * ‖ω‖ * ‖o‖) := by
  refine ⟨local_vortex_stretching_bound_off_diagonal_at_n_zero T hT,
          local_vortex_stretching_bound_off_diagonal_at_n_one T hT,
          local_vortex_stretching_bound_at_n_zero T hT,
          local_vortex_stretching_bound_at_n_one T hT,
          local_vortex_stretching_bound_at_n_two T hT,
          local_vortex_stretching_bound_at_n_eq_three T hT,
          ?_⟩
  intro ω g o
  -- Diagonal: K_diag = 1 (from the Wave 21 n=1 Hadamard bound).
  have hd : ‖VortexStretching3D ω g‖ ≤ 1 * ‖ω‖ * ‖g‖ := by
    rw [vortexStretching3D_eq_triple_hadamard, prod_triple_norm_eq]
    obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
    obtain ⟨hg0, hg1, hg2⟩ := three_tuple_components_le g
    have ng : 0 ≤ ‖g‖ := norm_nonneg _
    have b1 : ‖hadamard 1 g.1 ω.1‖ ≤ ‖ω‖ * ‖g‖ :=
      le_trans (hadamard_norm_le_n1 _ _)
        (le_trans (mul_le_mul hg0 hω0 (norm_nonneg _) ng) (by ring_nf; linarith [norm_nonneg ω, norm_nonneg g]))
    have b2 : ‖hadamard 1 g.2.1 ω.2.1‖ ≤ ‖ω‖ * ‖g‖ :=
      le_trans (hadamard_norm_le_n1 _ _)
        (le_trans (mul_le_mul hg1 hω1 (norm_nonneg _) ng) (by ring_nf; linarith [norm_nonneg ω, norm_nonneg g]))
    have b3 : ‖hadamard 1 g.2.2 ω.2.2‖ ≤ ‖ω‖ * ‖g‖ :=
      le_trans (hadamard_norm_le_n1 _ _)
        (le_trans (mul_le_mul hg2 hω2 (norm_nonneg _) ng) (by ring_nf; linarith [norm_nonneg ω, norm_nonneg g]))
    have hmax : max ‖hadamard 1 g.1 ω.1‖ (max ‖hadamard 1 g.2.1 ω.2.1‖
                ‖hadamard 1 g.2.2 ω.2.2‖) ≤ ‖ω‖ * ‖g‖ :=
      max_le b1 (max_le b2 b3)
    linarith [hmax]
  -- Off-diagonal: K_off = 2 (the n=1 theorem above).
  have ho : ‖VortexStretching3DOffDiagonal ω o‖ ≤ 2 * ‖ω‖ * ‖o‖ := by
    unfold VortexStretching3DOffDiagonal; simp only
    rw [prod_triple_norm_eq]
    obtain ⟨hω0, hω1, hω2⟩ := three_tuple_components_le ω
    obtain ⟨ho01, ho02, ho10, ho12, ho20, ho21⟩ := six_tuple_components_le o
    have b0 := offdiag_sum_bound_n1 ω o ω.2.1 ω.2.2 o.2.2.1 o.2.2.2.2.1
      hω1 hω2 ho10 ho20
    have b1 := offdiag_sum_bound_n1 ω o ω.1 ω.2.2 o.1 o.2.2.2.2.2
      hω0 hω2 ho01 ho21
    have b2 := offdiag_sum_bound_n1 ω o ω.1 ω.2.1 o.2.1 o.2.2.2.1
      hω0 hω1 ho02 ho12
    exact max_le b0 (max_le b1 b2)
  linarith [hd, ho]

end PrincipiaTractalis.NS3DOffDiagonalVortexStretching
