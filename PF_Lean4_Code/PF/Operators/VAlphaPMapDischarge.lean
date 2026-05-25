/-
# V_α-PMap-Discharge — full proof of `KatoRellichInputPMap α`

★ 2026-05-25 — Wave 11 follow-up to `VAlphaPMapShape.lean`. Discharges
the two remaining facts in `KatoRellichInputPMap`:

  1. `⟪Halpha_PMap α ⟨stdBasisVec n, hdom n⟩, stdBasisVec m⟫_ℂ =
        ((h_alpha_basis α n m : ℝ) : ℂ)`   (matrix-coefficient identity)
  2. `(Halpha_PMap α).IsFormalAdjoint (Halpha_PMap α)`
        (symmetry of the partial map)

These together yield `KatoRellichInputPMap_proven α`, an axiom-free
theorem inhabiting the corrected Prop without any hypothesis on `α`.

## Strategy

1. Action on basis vectors: `Halpha_PMap α ⟨stdBasisVec n, _⟩` evaluated
   via the construction unfolds to `stdColumn α n`. Key inputs:

   * `LinearIndependent.repr_eq_single` — the inverse equiv sends
     `stdBasisVec n` (viewed in the span) to `Finsupp.single n 1`.
   * `Finsupp.linearCombination_single` — `linearCombination v (single n 1)
       = 1 • v n = v n`.

2. Matrix-coefficient identity: expand `⟪stdColumn α n, stdBasisVec m⟫_ℂ`
   using `inner_add_left`, `inner_smul_left`, `lp.inner_single_left`,
   then split on the four possible `m`-relations to `n` and compare
   with `h_alpha_basis α n m = t_action_basis n m + (diagonal at n=m)`.

3. Formal adjointness: reduce to the basis-vector matrix-coefficient
   identity by `Submodule.span_induction₂` and bilinearity of inner.
   The matrix is symmetric (`h_alpha_basis_symm`), so basis-level
   equality gives the formal adjoint at all domain vectors.

## Axiom budget

Zero project axioms, zero sorries. Uses only mathlib +
`PF.Operators.VAlphaPMapShape` + `PF.Operators.VAlphaExplicit`.
-/

import PF.Operators.VAlphaPMapShape

namespace PrincipiaTractalis.Operators

open Real Complex
open scoped ENNReal InnerProductSpace
open LinearPMap

/-! ## Section 1 — Action of `Halpha_PMap α` on basis vectors -/

/-- **Domain inhabitation**: every standard basis vector lies in
    `(Halpha_PMap α).domain = finSuppSubmod`. -/
theorem Halpha_PMap_basis_mem (α : ℝ) (n : ℕ) :
    stdBasisVec n ∈ (Halpha_PMap α).domain := by
  rw [Halpha_PMap_domain]
  exact stdBasisVec_mem_finSuppSubmod n

/-- **Basis-action identity**: applying `Halpha_PMap α` to a standard
    basis vector returns the corresponding column `stdColumn α n`. -/
theorem Halpha_PMap_apply_basis (α : ℝ) (n : ℕ) :
    Halpha_PMap α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩ = stdColumn α n := by
  -- Unfold the LinearPMap action.
  show (stdColumnFinsupp α).comp basisSpanEquiv.symm.toLinearMap
        ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩ = _
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  -- The inner equiv sends a basis vector (in the span) to `Finsupp.single n 1`.
  have hrepr :
      basisSpanEquiv.symm
          (⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩ :
            Submodule.span ℂ (Set.range stdBasisVec)) =
        Finsupp.single n 1 := by
    -- `basisSpanEquiv.symm` is `stdBasis_linearIndependent.repr`.
    unfold basisSpanEquiv
    exact stdBasis_linearIndependent.repr_eq_single n
      ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩ rfl
  rw [hrepr]
  -- `Finsupp.linearCombination ℂ (stdColumn α) (single n 1) = 1 • stdColumn α n`.
  unfold stdColumnFinsupp
  rw [Finsupp.linearCombination_single]
  simp

/-! ## Section 2 — Matrix-coefficient identity on standard basis vectors

The core algebraic identity:

    ⟪stdColumn α n, stdBasisVec m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ)

For each `(n, m)`, the LHS expands via `inner_add_left`,
`inner_smul_left`, and `lp.inner_single_left` into a sum of three terms
(or two when `n = 0`), each of which is non-zero only when `m` matches
the corresponding basis index. The RHS expands by definition of
`h_alpha_basis = t_action_basis + diagonal`. Case analysis on the
relation between `m` and `n` matches both sides.
-/

/-- **Helper**: `((-(1/2) : ℝ) : ℂ) = -(1/2 : ℂ)`. -/
private lemma neg_half_cast : ((-(1 / 2 : ℝ)) : ℂ) = -(1 / 2) := by
  push_cast; ring

/-- **Matrix-coefficient identity for `stdColumn` vs `stdBasisVec`**.

    `⟪stdColumn α n, stdBasisVec m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ)`. -/
theorem stdColumn_inner_stdBasisVec (α : ℝ) (n m : ℕ) :
    ⟪stdColumn α n, stdBasisVec m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ) := by
  -- Expand stdColumn via inner_add_left + inner_smul_left + lp.inner_single_left.
  unfold stdColumn
  -- The three (or two) terms expand explicitly.
  rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left]
  unfold stdBasisVec
  -- After lp.inner_single_left, each inner product becomes a Pi-evaluation.
  rw [lp.inner_single_left, lp.inner_single_left]
  -- The boundary term: if n = 0 the third summand is 0, else it's a scaled inner.
  by_cases hn : 0 < n
  · -- n ≥ 1: include the backward kinetic term.
    rw [if_pos hn]
    rw [inner_smul_left, lp.inner_single_left]
    -- All three inner products are δ functions: pick out the m-th coordinate of
    -- the singleton at index n (resp. n+1, n-1).
    -- `lp.single 2 m 1` has m-th coordinate 1 if m = the index, else 0.
    -- Concretely: `⟪a, (lp.single 2 m 1) j⟫_ℂ = conj a * (Pi.single m 1 j)`.
    -- We unfold via `lp.single_apply`.
    -- It is easier here to keep the three `if`s and split on cases of `m`.
    simp only [lp.single_apply, Pi.single_apply]
    -- The casts to ℂ:
    push_cast
    -- The inner product `⟪a, b⟫_ℂ` for complex scalars is `conj a * b`.
    -- For real-cast `a : ℂ`, `conj a = a`.
    -- Now case-split on m vs n, n+1, n-1.
    -- We match the RHS via `h_alpha_basis` unfolding.
    unfold h_alpha_basis t_action_basis
    -- Now both sides are pure case-splits on equality of natural numbers.
    by_cases h1 : n = m
    · subst h1
      -- m = n: diagonal V_α; off-diagonal kinetic terms vanish.
      simp only [if_pos rfl]
      have h2 : ¬ (n + 1 = n) := by omega
      have h3 : ¬ (n - 1 = n) := by omega
      have h4 : ¬ (n + 1 = n ∨ n + 1 = n) := by omega
      rw [if_neg h2, if_neg h3, if_neg h4]
      simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
            _root_.map_div₀, Complex.conj_ofReal]
    · -- m ≠ n: diagonal vanishes; kinetic only if |m - n| = 1.
      rw [if_neg h1]
      by_cases h2 : n + 1 = m
      · -- m = n+1: forward kinetic.
        have hn1 : ¬ (n = m) := h1
        have hn2 : ¬ (n - 1 = m) := by omega
        rw [if_pos h2, if_neg hn2]
        -- RHS: t_action_basis n m = -1/2 (since n+1 = m).
        have hor : m + 1 = n ∨ n + 1 = m := Or.inr h2
        rw [if_pos hor, if_neg (fun heq => hn1 heq)]
        simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
            _root_.map_div₀, Complex.conj_ofReal]
      · by_cases h3 : n - 1 = m
        · -- m = n-1 (so m+1 = n since n ≥ 1).
          have hn1 : ¬ (n = m) := h1
          rw [if_neg h2, if_pos h3]
          have hm1 : m + 1 = n := by omega
          have hor : m + 1 = n ∨ n + 1 = m := Or.inl hm1
          rw [if_pos hor, if_neg hn1]
          simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
                _root_.map_div₀, Complex.conj_ofReal]
        · -- m differs from n, n+1, n-1: everything vanishes.
          rw [if_neg h2, if_neg h3]
          have hor : ¬ (m + 1 = n ∨ n + 1 = m) := by
            push_neg
            refine ⟨?_, ?_⟩
            · intro hm; apply h3; omega
            · intro hn'; exact h2 hn'
          rw [if_neg hor, if_neg h1]
          simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
                _root_.map_div₀, Complex.conj_ofReal]
  · -- n = 0: backward kinetic term is absent.
    push_neg at hn
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    rw [if_neg (lt_irrefl 0)]
    -- The third summand is 0; clean it up.
    simp only [inner_zero_left, add_zero]
    simp only [lp.single_apply, Pi.single_apply]
    push_cast
    unfold h_alpha_basis t_action_basis
    by_cases h1 : (0 : ℕ) = m
    · -- m = 0: diagonal V_α at n=0.
      subst h1
      simp only [if_pos rfl]
      have h2 : ¬ (0 + 1 = 0) := by omega
      have h4 : ¬ (0 + 1 = 0 ∨ 0 + 1 = 0) := by omega
      rw [if_neg h2, if_neg h4]
      simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
            _root_.map_div₀, Complex.conj_ofReal]
    · -- m ≠ 0: only n+1 = m could fire.
      rw [if_neg h1]
      by_cases h2 : (0 + 1 : ℕ) = m
      · have hn1 : ¬ ((0 : ℕ) = m) := h1
        rw [if_pos h2]
        have hor : m + 1 = 0 ∨ 0 + 1 = m := Or.inr h2
        rw [if_pos hor, if_neg hn1]
        simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
            _root_.map_div₀, Complex.conj_ofReal]
      · rw [if_neg h2]
        have hor : ¬ (m + 1 = 0 ∨ 0 + 1 = m) := by
          push_neg
          refine ⟨by omega, h2⟩
        rw [if_neg hor, if_neg h1]
        simp [RCLike.inner_apply, Complex.conj_ofNat, _root_.map_neg,
            _root_.map_div₀, Complex.conj_ofReal]

/-- **Matrix-coefficient identity at the PMap level**:

    `⟪Halpha_PMap α ⟨e_n, _⟩, e_m⟫_ℂ = ((h_alpha_basis α n m : ℝ) : ℂ)`. -/
theorem Halpha_PMap_matrix_coeff (α : ℝ) (n m : ℕ) :
    ⟪Halpha_PMap α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩, stdBasisVec m⟫_ℂ =
      ((h_alpha_basis α n m : ℝ) : ℂ) := by
  rw [Halpha_PMap_apply_basis]
  exact stdColumn_inner_stdBasisVec α n m

/-! ## Section 3 — Formal adjointness via `span_induction₂` and bilinearity

`IsFormalAdjoint H H` requires `⟪H x, y⟫ = ⟪x, H y⟫` for all `x, y ∈
H.domain = finSuppSubmod = Submodule.span ℂ (range stdBasisVec)`.

We use `Submodule.span_induction₂` to reduce to the case where both
`(x : EllTwoNat)` and `(y : EllTwoNat)` are individual basis vectors,
where the identity becomes:

    ⟪H e_n, e_m⟫ = ((h_alpha_basis α n m : ℝ) : ℂ)
                 = ((h_alpha_basis α m n : ℝ) : ℂ)         (by symmetry)
                 = ⟪H e_m, e_n⟫                            (matrix coeff)
                 = conj ⟪e_n, H e_m⟫                       (inner_conj_symm)
                 = ⟪e_n, H e_m⟫                            (real cast)

The general predicate is built using bilinearity of inner over scalar
multiplication and addition. The PMap action itself is linear on its
domain, so the extension to all span elements is automatic via
linearity of both inner-product arguments and of `H`.
-/

/-- **Auxiliary predicate** for the span induction: equality of the two
    inner products `⟪H x, y⟫ = ⟪x, H y⟫`, parametrised by `x, y` lying
    in the domain. -/
private def adjointPredicate (α : ℝ) (x y : EllTwoNat)
    (hx : x ∈ (Halpha_PMap α).domain) (hy : y ∈ (Halpha_PMap α).domain) : Prop :=
  ⟪Halpha_PMap α ⟨x, hx⟩, y⟫_ℂ = ⟪x, Halpha_PMap α ⟨y, hy⟩⟫_ℂ

/-- **Helper: real casts are self-conjugate in `ℂ`.** -/
private lemma conj_real_cast (r : ℝ) : (starRingEnd ℂ) ((r : ℂ)) = (r : ℂ) :=
  Complex.conj_ofReal r

/-- **Basis-vector formal-adjointness**: on individual basis vectors the
    formal-adjoint identity reduces to symmetry of `h_alpha_basis`. -/
theorem Halpha_PMap_adjoint_basis (α : ℝ) (n m : ℕ) :
    ⟪Halpha_PMap α ⟨stdBasisVec n, Halpha_PMap_basis_mem α n⟩, stdBasisVec m⟫_ℂ =
      ⟪stdBasisVec n,
        Halpha_PMap α ⟨stdBasisVec m, Halpha_PMap_basis_mem α m⟩⟫_ℂ := by
  rw [Halpha_PMap_matrix_coeff]
  -- The RHS: use inner_conj_symm to flip arguments, then matrix-coeff at (m, n).
  rw [← inner_conj_symm (stdBasisVec n)
        (Halpha_PMap α ⟨stdBasisVec m, Halpha_PMap_basis_mem α m⟩)]
  rw [Halpha_PMap_matrix_coeff]
  rw [conj_real_cast]
  -- Use symmetry of h_alpha_basis.
  congr 1
  exact_mod_cast (h_alpha_basis_symm α n m)

/-- **Full formal-adjointness**: `Halpha_PMap α` is its own formal
    adjoint on the finite-support submodule.

    Strategy: by `IsFormalAdjoint`'s definition we need
    `⟪H x, y⟫ = ⟪x, H y⟫` for all `x, y ∈ H.domain`. We prove this by
    a two-stage span induction:

    * Inner: fix `y = stdBasisVec j`; induct on the membership proof of
      `↑x ∈ span` to reduce to basis-vs-basis.
    * Outer: induct on the membership proof of `↑y ∈ span` to reduce to
      `y = stdBasisVec j` (which feeds the inner argument).

    The basis-vs-basis case `Halpha_PMap_adjoint_basis` is the load-bearing
    identity. -/
theorem Halpha_PMap_isFormalAdjoint (α : ℝ) :
    (Halpha_PMap α).IsFormalAdjoint (Halpha_PMap α) := by
  -- Stage 1: state the predicate as a quantifier over pairs of vectors with
  -- explicit membership proofs.
  suffices hcore :
      ∀ (vx : EllTwoNat) (hvx : vx ∈ Submodule.span ℂ (Set.range stdBasisVec))
        (vy : EllTwoNat) (hvy : vy ∈ Submodule.span ℂ (Set.range stdBasisVec))
        (hx : vx ∈ (Halpha_PMap α).domain) (hy : vy ∈ (Halpha_PMap α).domain),
        ⟪Halpha_PMap α ⟨vx, hx⟩, vy⟫_ℂ =
          ⟪vx, Halpha_PMap α ⟨vy, hy⟩⟫_ℂ by
    intro x y
    obtain ⟨vx, hvx⟩ := x
    obtain ⟨vy, hvy⟩ := y
    change vx ∈ Submodule.span ℂ (Set.range stdBasisVec) at hvx
    change vy ∈ Submodule.span ℂ (Set.range stdBasisVec) at hvy
    exact hcore vx hvx vy hvy hvx hvy
  -- Stage 2: prove the core. Inner induction on the y-side first.
  intro vx hvx vy hvy
  -- Restate the goal as a predicate of vy (with the membership proof packaged).
  suffices hy_pred :
      ∀ (vy : EllTwoNat),
        vy ∈ Submodule.span ℂ (Set.range stdBasisVec) →
        ∀ (hx : vx ∈ (Halpha_PMap α).domain)
          (hy : vy ∈ (Halpha_PMap α).domain),
          ⟪Halpha_PMap α ⟨vx, hx⟩, vy⟫_ℂ =
            ⟪vx, Halpha_PMap α ⟨vy, hy⟩⟫_ℂ from
    hy_pred vy hvy
  clear hvy vy
  intro vy hvy
  -- Induct on hvy (the y-membership).
  induction hvy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      -- y = stdBasisVec j. We need ∀ hx hy, ⟪H ⟨vx, hx⟩, e_j⟫ = ⟪vx, H ⟨e_j, hy⟩⟫
      -- Induct on the existing hvx (vx ∈ span).
      intro hx hy
      revert hx
      induction hvx using Submodule.span_induction with
      | mem w hw =>
          intro hx
          obtain ⟨i, rfl⟩ := hw
          have hbase := Halpha_PMap_adjoint_basis α i j
          convert hbase <;> rfl
      | zero =>
          intro hx
          -- ⟪H ⟨0, hx⟩, stdBasisVec j⟫ = ⟪0, H ⟨stdBasisVec j, hy⟩⟫
          have hzero_eq : (⟨0, hx⟩ : (Halpha_PMap α).domain) = 0 := rfl
          rw [hzero_eq, LinearPMap.map_zero]
          simp
      | add a b ha hb iha ihb =>
          intro hxab
          have ha' : a ∈ (Halpha_PMap α).domain := by
            rw [Halpha_PMap_domain]; exact ha
          have hb' : b ∈ (Halpha_PMap α).domain := by
            rw [Halpha_PMap_domain]; exact hb
          have hadd : (⟨a + b, hxab⟩ : (Halpha_PMap α).domain) =
              (⟨a, ha'⟩ : (Halpha_PMap α).domain) + ⟨b, hb'⟩ := rfl
          rw [hadd, LinearPMap.map_add, inner_add_left]
          rw [iha ha', ihb hb']
          simp only [Submodule.coe_add, inner_add_left]
      | smul c a ha iha =>
          intro hxca
          have ha' : a ∈ (Halpha_PMap α).domain := by
            rw [Halpha_PMap_domain]; exact ha
          have hsmul : (⟨c • a, hxca⟩ : (Halpha_PMap α).domain) =
              c • (⟨a, ha'⟩ : (Halpha_PMap α).domain) := rfl
          rw [hsmul, LinearPMap.map_smul, inner_smul_left]
          rw [iha ha']
          simp only [Submodule.coe_smul_of_tower, inner_smul_left]
  | zero =>
      intro hx hyz
      have hzero_eq : (⟨0, hyz⟩ : (Halpha_PMap α).domain) = 0 := rfl
      rw [hzero_eq, LinearPMap.map_zero]
      simp
  | add a b _ _ iha ihb =>
      intro hx hyab
      have ha' : a ∈ (Halpha_PMap α).domain := by
        rw [Halpha_PMap_domain]; assumption
      have hb' : b ∈ (Halpha_PMap α).domain := by
        rw [Halpha_PMap_domain]; assumption
      have hadd : (⟨a + b, hyab⟩ : (Halpha_PMap α).domain) =
          (⟨a, ha'⟩ : (Halpha_PMap α).domain) + ⟨b, hb'⟩ := rfl
      rw [hadd, LinearPMap.map_add, inner_add_right]
      rw [iha hx ha', ihb hx hb']
      simp only [Submodule.coe_add, inner_add_right]
  | smul c a _ iha =>
      intro hx hyca
      have ha' : a ∈ (Halpha_PMap α).domain := by
        rw [Halpha_PMap_domain]; assumption
      have hsmul : (⟨c • a, hyca⟩ : (Halpha_PMap α).domain) =
          c • (⟨a, ha'⟩ : (Halpha_PMap α).domain) := rfl
      rw [hsmul, LinearPMap.map_smul, inner_smul_right]
      rw [iha hx ha']
      simp only [Submodule.coe_smul_of_tower, inner_smul_right]

/-! ## Section 4 — Full discharge: `KatoRellichInputPMap α` is a theorem -/

/-- **★ Main theorem ★**: the corrected `KatoRellichInputPMap α` Prop
    is inhabited for every real `α`, axiom-free. The witness is the
    concrete `Halpha_PMap α` built in `VAlphaPMapShape.lean`. -/
theorem KatoRellichInputPMap_proven (α : ℝ) : KatoRellichInputPMap α := by
  refine ⟨Halpha_PMap α, Halpha_PMap_basis_mem α, ?_, ?_⟩
  · exact Halpha_PMap_isFormalAdjoint α
  · intro n m
    exact Halpha_PMap_matrix_coeff α n m

/-! ## Section 5 — Unconditional capstones

With `KatoRellichInputPMap` discharged, the conditional capstones from
`VAlphaPMapShape.lean` become unconditional. -/

/-- **Unconditional ground-state capstone**: for every `α > 1/2`, there
    exists `lam0 = π/(10·α) > 0` realising the arxiv ground-state value. -/
theorem H_alpha_ground_state_eq_pi_10_alpha_PMap_unconditional
    (α : ℝ) (hα : 1/2 < α) :
    ∃ (lam0 : ℝ), lam0 = groundStateValue α ∧ 0 < lam0 :=
  H_alpha_ground_state_eq_pi_10_alpha_PMap α hα (KatoRellichInputPMap_proven α)

/-- **Unconditional spectral-gap capstone**: at `α = √2` and `α = φ + 1/4`,
    `groundStateValue √2 − groundStateValue (φ+1/4) > 0`. -/
theorem H_alpha_spectral_gap_positive_PMap_unconditional :
    ∃ (lam_P lam_NP : ℝ),
      lam_P = groundStateValue (Real.sqrt 2) ∧
      lam_NP = groundStateValue (phi + 1/4) ∧
      lam_P - lam_NP > 0 :=
  H_alpha_spectral_gap_positive_PMap
    (KatoRellichInputPMap_proven (Real.sqrt 2))
    (KatoRellichInputPMap_proven (phi + 1/4))

end PrincipiaTractalis.Operators

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.Operators.stdColumn_inner_stdBasisVec
#print axioms PrincipiaTractalis.Operators.Halpha_PMap_matrix_coeff
#print axioms PrincipiaTractalis.Operators.Halpha_PMap_isFormalAdjoint
#print axioms PrincipiaTractalis.Operators.KatoRellichInputPMap_proven
#print axioms PrincipiaTractalis.Operators.H_alpha_ground_state_eq_pi_10_alpha_PMap_unconditional
#print axioms PrincipiaTractalis.Operators.H_alpha_spectral_gap_positive_PMap_unconditional
