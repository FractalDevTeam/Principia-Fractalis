/-
# NS3D_LerayProjector — concrete Leray projection onto the
   divergence-free subspace of Fourier-coefficient sequences

★ 2026-06-12 — fifth Type (F) advance on the NS Sobolev/Leray bridge
(Wave 51B residual gap). Builds the concrete Leray projector
`lerayProject : ((Fin 3 → ℤ) → (Fin 3 → ℂ)) → ((Fin 3 → ℤ) → (Fin 3 → ℂ))`
which orthogonally projects any Fourier-coefficient sequence onto the
divergence-free subspace by subtracting the `k`-parallel component
mode-by-mode.

## Concrete formula

For `k ∈ Fin 3 → ℤ` and an input sequence `c`:
  * if `k = 0`: `lerayProject c k := c k` (zero-mode pass-through,
    since `dotIntC3 0 a = 0` automatically)
  * if `k ≠ 0`: subtract the parallel projection along `k`:
    `lerayProject c k j := c k j - (dotIntC3 k (c k) / ‖k‖²_ℤ) · (k j : ℂ)`
    where `‖k‖²_ℤ := Σ_j ((k j : ℝ))² > 0`.

By construction, `dotIntC3 k (lerayProject c k) = 0` for every wave
vector `k`, so the result is in the divergence-free subspace.

## What this file delivers, axiom-free

  (1) **`kNormSqReal`** — `Σ_j ((k j : ℝ))²`, non-negative, and
      strictly positive iff `k ≠ 0`.

  (2) **`lerayProject`** — the explicit projector formula.

  (3) **`lerayProject_zero_mode`** — `lerayProject c 0 = c 0`.

  (4) **`lerayProject_div_free`** — the central identity:
      `∀ k, dotIntC3 k (lerayProject c k) = 0`.

  (5) **`lerayProjectToConcrete`** — the typed promotion of an
      arbitrary coefficient sequence to a `ConcreteDivFreeVelocityField`.

  (6) **`lerayProject_idempotent`** — `lerayProject (lerayProject c) = lerayProject c`
      (idempotence is automatic at the typed level since the second
      application acts on a sequence whose `dotIntC3 k` is already 0).

  (7) **Capstone** — the Leray projector exists, is divergence-free
      by construction, fixes already-div-free sequences (in particular
      preserves any `u.coeff` for `u : ConcreteDivFreeVelocityField`),
      and is idempotent.

ZERO project axioms; kernel-only `[propext, Classical.choice, Quot.sound]`.

Author: Pablo Cohen + Claude Opus 4.7. 2026-06-12.
-/

import PF.NS3D_ConcreteDivFreeHsInner

namespace PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

open PrincipiaTractalis.DivFreeFourierDensityOnTorus3Attempt

/-! ## §1 — Real-valued squared-norm of an integer wave vector -/

/-- **Squared norm of an integer wave vector**: `Σ_j ((k j : ℝ))²`. -/
noncomputable def kNormSqReal (k : Fin 3 → ℤ) : ℝ :=
  ∑ j : Fin 3, ((k j : ℝ))^2

theorem kNormSqReal_nonneg (k : Fin 3 → ℤ) : 0 ≤ kNormSqReal k := by
  unfold kNormSqReal
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **A wave vector with positive squared norm is non-zero**. -/
theorem kNormSqReal_pos_of_ne_zero
    {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < kNormSqReal k := by
  unfold kNormSqReal
  -- There exists j with k j ≠ 0
  have h_exists : ∃ j : Fin 3, k j ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    apply hk
    funext j
    exact h_all_zero j
  obtain ⟨j₀, hj₀⟩ := h_exists
  have h_term_pos : 0 < ((k j₀ : ℝ))^2 := by
    have h_ne : (k j₀ : ℝ) ≠ 0 := by
      exact_mod_cast hj₀
    positivity
  refine lt_of_lt_of_le h_term_pos ?_
  rw [show ((k j₀ : ℝ))^2 = (fun j => ((k j : ℝ))^2) j₀ from rfl]
  exact Finset.single_le_sum
    (f := fun j => ((k j : ℝ))^2)
    (s := Finset.univ)
    (fun j _ => sq_nonneg _)
    (Finset.mem_univ j₀)

theorem kNormSqReal_zero : kNormSqReal 0 = 0 := by
  unfold kNormSqReal
  simp

/-- **Cast of kNormSqReal as a complex coefficient**. -/
noncomputable def kNormSqC (k : Fin 3 → ℤ) : ℂ :=
  (kNormSqReal k : ℂ)

/-- **Key identity**: `Σ_j (k j : ℂ) * (k j : ℂ) = kNormSqC k`. -/
theorem sum_kj_sq_eq_kNormSqC (k : Fin 3 → ℤ) :
    ∑ j : Fin 3, (k j : ℂ) * (k j : ℂ) = kNormSqC k := by
  unfold kNormSqC kNormSqReal
  push_cast
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-! ## §2 — The Leray projector -/

/-- **The Leray projector**: orthogonally projects any Fourier-coefficient
    sequence onto the divergence-free subspace by subtracting the
    `k`-parallel component mode-by-mode.

    For `k = 0`: identity (zero mode unchanged).
    For `k ≠ 0`: `(P c)(k) := c(k) - (dotIntC3 k (c k) / ‖k‖²_ℤ) · k`. -/
noncomputable def lerayProject
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (Fin 3 → ℤ) → (Fin 3 → ℂ) := fun k =>
  if k = 0 then c k
  else fun j =>
    c k j - (dotIntC3 k (c k) / kNormSqC k) * (k j : ℂ)

theorem lerayProject_zero_mode
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProject c 0 = c 0 := by
  unfold lerayProject
  simp

theorem lerayProject_at_ne_zero
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) {k : Fin 3 → ℤ} (hk : k ≠ 0) (j : Fin 3) :
    lerayProject c k j
      = c k j - (dotIntC3 k (c k) / kNormSqC k) * (k j : ℂ) := by
  unfold lerayProject
  rw [if_neg hk]

/-! ## §3 — Divergence-free identity at every mode -/

/-- **Auxiliary: `dotIntC3` distributes over the pointwise subtraction**. -/
theorem dotIntC3_sub (k : Fin 3 → ℤ) (a b : Fin 3 → ℂ) :
    dotIntC3 k (a - b) = dotIntC3 k a - dotIntC3 k b := by
  have h_rw : a - b = a + (-b) := by ring
  rw [h_rw, dotIntC3_add, dotIntC3_neg]
  ring

/-- **The Leray-projected coefficient is divergence-free at every mode**. -/
theorem lerayProject_div_free
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) (k : Fin 3 → ℤ) :
    dotIntC3 k (lerayProject c k) = 0 := by
  by_cases hk : k = 0
  · -- k = 0: dotIntC3 0 a = 0 trivially
    rw [hk]
    unfold dotIntC3
    simp
  · -- k ≠ 0: explicit projection formula
    -- We need to show ∑ j, (k j : ℂ) * (c k j - α * (k j : ℂ)) = 0
    -- where α = dotIntC3 k (c k) / kNormSqC k.
    have h_norm_pos : 0 < kNormSqReal k := kNormSqReal_pos_of_ne_zero hk
    have h_norm_ne : kNormSqC k ≠ 0 := by
      unfold kNormSqC
      have : (kNormSqReal k : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt h_norm_pos
      exact this
    -- Compute dotIntC3 k (lerayProject c k) explicitly.
    have h_eq : lerayProject c k
        = (fun j => c k j - (dotIntC3 k (c k) / kNormSqC k) * (k j : ℂ)) := by
      funext j
      exact lerayProject_at_ne_zero c hk j
    rw [h_eq]
    -- Show the goal in pre-unfolded form.
    show ∑ j : Fin 3, (k j : ℂ)
          * (c k j - (dotIntC3 k (c k) / kNormSqC k) * (k j : ℂ)) = 0
    -- Distribute and split.
    have h_sum_split :
        ∑ j : Fin 3, (k j : ℂ)
          * (c k j - (dotIntC3 k (c k) / kNormSqC k) * (k j : ℂ))
        = (∑ j : Fin 3, (k j : ℂ) * c k j)
          - (dotIntC3 k (c k) / kNormSqC k)
            * (∑ j : Fin 3, (k j : ℂ) * (k j : ℂ)) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib (f := fun j => (k j : ℂ) * c k j)
          (g := fun j => (dotIntC3 k (c k) / kNormSqC k) * ((k j : ℂ) * (k j : ℂ)))]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [h_sum_split]
    have h_first : (∑ j : Fin 3, (k j : ℂ) * c k j) = dotIntC3 k (c k) := rfl
    rw [h_first, sum_kj_sq_eq_kNormSqC]
    field_simp
    ring

/-! ## §4 — Promotion to ConcreteDivFreeVelocityField -/

/-- **The Leray projector lifts any Fourier-coefficient sequence
    to a `ConcreteDivFreeVelocityField`**, since the projection
    is divergence-free at every mode by construction. -/
noncomputable def lerayProjectToConcrete
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) : ConcreteDivFreeVelocityField where
  coeff := lerayProject c
  div_free := lerayProject_div_free c

theorem lerayProjectToConcrete_coeff
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    (lerayProjectToConcrete c).coeff = lerayProject c := rfl

/-! ## §5 — Fixed-point property on already-div-free sequences -/

/-- **The Leray projector fixes a sequence whose `dotIntC3 k` is already
    zero at every mode**. -/
theorem lerayProject_fixes_div_free
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ))
    (h_div_free : ∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) :
    lerayProject c = c := by
  funext k
  by_cases hk : k = 0
  · rw [hk]; exact lerayProject_zero_mode c
  · funext j
    rw [lerayProject_at_ne_zero c hk j]
    rw [h_div_free k]
    simp

/-- **As a corollary, applied to a `ConcreteDivFreeVelocityField`,
    the Leray projector returns the same coefficient sequence**. -/
theorem lerayProject_fixes_concrete
    (u : ConcreteDivFreeVelocityField) :
    lerayProject u.coeff = u.coeff :=
  lerayProject_fixes_div_free u.coeff u.div_free

/-! ## §6 — Idempotence -/

/-- **The Leray projector is idempotent**:
    `lerayProject (lerayProject c) = lerayProject c`. -/
theorem lerayProject_idempotent
    (c : (Fin 3 → ℤ) → (Fin 3 → ℂ)) :
    lerayProject (lerayProject c) = lerayProject c :=
  lerayProject_fixes_div_free (lerayProject c) (lerayProject_div_free c)

/-! ## §7 — Capstone -/

/-- **★ LERAY PROJECTOR CAPSTONE ★** —
    `concrete_div_free_leray_projector_capstone`.

    The concrete Leray projector `lerayProject` orthogonally projects
    any Fourier-coefficient sequence onto the divergence-free subspace
    with the four defining properties:
      (L1) divergence-free at every mode by construction,
      (L2) fixes the zero mode (`k = 0` pass-through),
      (L3) fixes any already-divergence-free input (in particular every
           `u.coeff` for `u : ConcreteDivFreeVelocityField`),
      (L4) idempotent (`P² = P`).

    Combined with the vector-space, norm, and inner-product capstones,
    this completes the concrete Sobolev/Leray bridge structure on
    `ConcreteDivFreeVelocityField`. -/
theorem concrete_div_free_leray_projector_capstone :
    -- (L1) divergence-free at every mode
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), ∀ k : Fin 3 → ℤ,
      dotIntC3 k (lerayProject c k) = 0) ∧
    -- (L2) zero-mode pass-through
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ), lerayProject c 0 = c 0) ∧
    -- (L3) fixes already-div-free
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      (∀ k : Fin 3 → ℤ, dotIntC3 k (c k) = 0) → lerayProject c = c) ∧
    -- (L4) idempotence
    (∀ c : (Fin 3 → ℤ) → (Fin 3 → ℂ),
      lerayProject (lerayProject c) = lerayProject c) :=
  ⟨lerayProject_div_free,
   lerayProject_zero_mode,
   lerayProject_fixes_div_free,
   lerayProject_idempotent⟩

end PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField

#print axioms
  PrincipiaTractalis.NS3D_ConcreteDivFreeVelocityField.concrete_div_free_leray_projector_capstone
