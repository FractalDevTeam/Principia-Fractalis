/-
# Dilation Operator and Scale-Shift on cosineMode/sineMode

The natural operator-theoretic lift of the kernel self-similarity
(KernelSelfSimilarity.lean): the dilation operator `D_α : f ↦ f(·/α)`
on functions `ℝ → ℝ`. It is a linear, continuous isometry of `L²(ℝ)`
(scaled by `√α`) that acts on the cosineMode/sineMode basis by
shifting the scale index down by one:

  `D_α (cosineMode α (k+1)) = cosineMode α k`
  `D_α (sineMode α (k+1))   = sineMode α k`

This connects the **kernel-level** self-similarity equation
  `V_P(x, y) = cos(π·|x−y|) + (1/a)·V_P(αx, αy)`
to the **operator-level** functional equation relating
`H_P_at α a` and its dilation conjugate.

The conjectured eigenstructure follows: if `ψ_k` is an eigenfunction
of `H_P_at α a` at scale `k`, the dilation may relate it to
eigenfunctions at adjacent scales, providing the recursive
identification needed for the polylog formula.

Stage L4+ — Dilation operator (operator-theoretic depth).
-/

import PF.Analytic.PolylogSpectrum

namespace PrincipiaTractalis.Analytic

open Real

/-! ## Definition -/

/-- **Dilation operator**: `(D_α f)(x) := f(x / α)`.

    For `α > 0`, this is the operator-theoretic implementation of
    rescaling `x ↦ αx` (acting on functions by pullback). The scaling
    factor `1/α` ensures `D_α ∘ M_α = id` where `M_α x = αx`. -/
noncomputable def dilation (α : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (x / α)

/-! ## Basic linearity and continuity -/

/-- **Linearity (additivity)**: `D_α (f + g) = D_α f + D_α g`. -/
theorem dilation_add (α : ℝ) (f g : ℝ → ℝ) :
    dilation α (f + g) = dilation α f + dilation α g := by
  funext _; rfl

/-- **Linearity (scalar multiplication)**: `D_α (c·f) = c·D_α f`. -/
theorem dilation_smul (α c : ℝ) (f : ℝ → ℝ) :
    dilation α (c • f) = c • dilation α f := by
  funext _; rfl

/-- **Continuity preserved**: if `f` is continuous, so is `D_α f`. -/
theorem dilation_continuous (α : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (dilation α f) := by
  unfold dilation
  exact hf.comp (continuous_id'.div_const α)

/-- **Inverse property**: dilation by `α` composed with dilation by
    `α⁻¹` is the identity (for `α ≠ 0`). -/
theorem dilation_inv_dilation (α : ℝ) (hα : α ≠ 0) (f : ℝ → ℝ) :
    dilation α⁻¹ (dilation α f) = f := by
  funext x
  unfold dilation
  field_simp

/-! ## Preserved properties under dilation -/

/-- **Bounded functions stay bounded under dilation**: if `|f x| ≤ M`
    for all `x`, then `|(D_α f) x| ≤ M` for all `x`. (Same `M`; the
    dilation doesn't change the sup.) -/
theorem dilation_bounded (α : ℝ) (f : ℝ → ℝ) (M : ℝ) (hf : ∀ x, |f x| ≤ M) :
    ∀ x, |dilation α f x| ≤ M := by
  intro x
  unfold dilation
  exact hf (x / α)

/-- **Constants are fixed**: `D_α (constant c) = (constant c)`. -/
theorem dilation_const (α c : ℝ) :
    dilation α (fun _ => c) = fun _ => c := by
  funext _; rfl

/-- **Zero is fixed**: `D_α 0 = 0`. -/
theorem dilation_zero (α : ℝ) :
    dilation α (0 : ℝ → ℝ) = 0 := by
  funext _; unfold dilation; rfl

/-! ## Bijectivity (group inverse) -/

/-- **The other direction of inverse**: `D_α (D_α⁻¹ f) = f`.

    Together with `dilation_inv_dilation` (`D_α⁻¹ (D_α f) = f` from
    earlier), this gives bidirectional invertibility. -/
theorem dilation_dilation_inv (α : ℝ) (hα : α ≠ 0) (f : ℝ → ℝ) :
    dilation α (dilation α⁻¹ f) = f := by
  funext x
  unfold dilation
  field_simp

/-- **Bijectivity**: `dilation α : (ℝ → ℝ) → (ℝ → ℝ)` is a bijection
    for `α ≠ 0`. Inverse is `dilation α⁻¹`. -/
theorem dilation_bijective (α : ℝ) (hα : α ≠ 0) :
    Function.Bijective (dilation α : (ℝ → ℝ) → (ℝ → ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro f g h
    calc f = dilation α⁻¹ (dilation α f) := (dilation_inv_dilation α hα f).symm
      _ = dilation α⁻¹ (dilation α g) := by rw [h]
      _ = g := dilation_inv_dilation α hα g
  · intro g
    use dilation α⁻¹ g
    exact dilation_dilation_inv α hα g

/-! ## Group structure: composition and powers -/

/-- **Composition**: `D_α ∘ D_β = D_(αβ)`.

    The dilation operators form an abelian group under composition,
    parametrised by `ℝ \ {0}` (with `D_1 = id` and `D_α⁻¹` as
    inverse). -/
theorem dilation_comp (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) (f : ℝ → ℝ) :
    dilation α (dilation β f) = dilation (α * β) f := by
  funext x
  unfold dilation
  congr 1
  field_simp

/-- **Identity**: `D_1 = id`. -/
theorem dilation_one (f : ℝ → ℝ) : dilation 1 f = f := by
  funext _; unfold dilation; simp

/-- **Iteration**: `(D_α)^j = D_(α^j)`.

    By induction on `j`, using `dilation_comp` at each step. Provides
    the natural-number power structure of the dilation group. -/
theorem dilation_iter (α : ℝ) (hα : α ≠ 0) (j : ℕ) (f : ℝ → ℝ) :
    (dilation α)^[j] f = dilation (α^j) f := by
  induction j with
  | zero => simp [dilation_one]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [show dilation α (dilation (α^j) f) = dilation (α * α^j) f from
        dilation_comp α (α^j) hα (pow_ne_zero j hα) f]
    rw [show α * α^j = α^(j+1) from by ring]

/-! ## Scale shift on cosineMode/sineMode (the structural identity) -/

/-- **★ Scale shift on cosineMode ★**:

      `D_α (cosineMode α (k+1)) (x) = cosineMode α k (x)`

    for any `α ≠ 0`, `k : ℕ`, `x : ℝ`. The dilation operator shifts
    the cosineMode scale index DOWN by one. Direct from
    `cos(π · α^(k+1) · (x/α)) = cos(π · α^k · x)`. -/
theorem dilation_cosineMode_succ (α : ℝ) (hα : α ≠ 0) (k : ℕ) (x : ℝ) :
    dilation α (cosineMode α (k + 1)) x = cosineMode α k x := by
  unfold dilation cosineMode
  congr 1
  field_simp
  ring

/-- **★ Scale shift on sineMode ★** (parallel to cosineMode):

      `D_α (sineMode α (k+1)) (x) = sineMode α k (x)`. -/
theorem dilation_sineMode_succ (α : ℝ) (hα : α ≠ 0) (k : ℕ) (x : ℝ) :
    dilation α (sineMode α (k + 1)) x = sineMode α k x := by
  unfold dilation sineMode
  congr 1
  field_simp
  ring

/-- **Functional-equality version** for cosineMode: `D_α ∘ cosineMode α (k+1)
    = cosineMode α k`. Useful for substituting in operator expressions. -/
theorem dilation_cosineMode_succ_fun (α : ℝ) (hα : α ≠ 0) (k : ℕ) :
    dilation α (cosineMode α (k + 1)) = cosineMode α k :=
  funext (fun x => dilation_cosineMode_succ α hα k x)

/-- **Functional-equality version** for sineMode. -/
theorem dilation_sineMode_succ_fun (α : ℝ) (hα : α ≠ 0) (k : ℕ) :
    dilation α (sineMode α (k + 1)) = sineMode α k :=
  funext (fun x => dilation_sineMode_succ α hα k x)

/-! ## j-fold scale shift -/

/-- **j-fold scale shift on cosineMode**:

      `(D_α)^[j] (cosineMode α (k + j)) = cosineMode α k`

    Iterating the single-step shift `j` times lowers the scale by
    exactly `j`. Direct from `dilation_iter` + the explicit `α^k`
    factorisation `cos(π · α^(k+j) · x/α^j) = cos(π · α^k · x)`. -/
theorem dilation_iter_cosineMode (α : ℝ) (hα : α ≠ 0) (k j : ℕ) :
    (dilation α)^[j] (cosineMode α (k + j)) = cosineMode α k := by
  rw [dilation_iter α hα j]
  funext x
  unfold dilation cosineMode
  congr 1
  rw [pow_add]
  field_simp

/-- **j-fold scale shift on sineMode** (parallel). -/
theorem dilation_iter_sineMode (α : ℝ) (hα : α ≠ 0) (k j : ℕ) :
    (dilation α)^[j] (sineMode α (k + j)) = sineMode α k := by
  rw [dilation_iter α hα j]
  funext x
  unfold dilation sineMode
  congr 1
  rw [pow_add]
  field_simp

/-! ## j-fold inverse-dilation: raise scale by j -/

/-- **j-fold inverse-dilation on cosineMode raises scale by j**:

      `(D_α⁻¹)^[j] (cosineMode α k) = cosineMode α (k + j)`

    The mirror of `dilation_iter_cosineMode`. -/
theorem dilation_inv_iter_cosineMode (α : ℝ) (hα : α ≠ 0) (k j : ℕ) :
    (dilation α⁻¹)^[j] (cosineMode α k) = cosineMode α (k + j) := by
  have h_inv : α⁻¹ ≠ 0 := inv_ne_zero hα
  rw [dilation_iter α⁻¹ h_inv j]
  funext x
  unfold dilation cosineMode
  congr 1
  rw [pow_add]
  rw [inv_pow]
  field_simp

/-- **j-fold inverse-dilation on sineMode raises scale by j** (parallel). -/
theorem dilation_inv_iter_sineMode (α : ℝ) (hα : α ≠ 0) (k j : ℕ) :
    (dilation α⁻¹)^[j] (sineMode α k) = sineMode α (k + j) := by
  have h_inv : α⁻¹ ≠ 0 := inv_ne_zero hα
  rw [dilation_iter α⁻¹ h_inv j]
  funext x
  unfold dilation sineMode
  congr 1
  rw [pow_add]
  rw [inv_pow]
  field_simp

/-! ## Inverse-dilation shift (raise the scale index) -/

/-- **Inverse-dilation scale shift on cosineMode**:

      `D_(α⁻¹) (cosineMode α k) (x) = cosineMode α (k+1) (x)`

    Substituting `x ↦ x · α` raises the scale index. Direct from
    `cos(π · α^k · (x · α)) = cos(π · α^(k+1) · x)`. -/
theorem dilation_inv_cosineMode (α : ℝ) (hα : α ≠ 0) (k : ℕ) (x : ℝ) :
    dilation α⁻¹ (cosineMode α k) x = cosineMode α (k + 1) x := by
  unfold dilation cosineMode
  congr 1
  field_simp
  ring

/-- **Inverse-dilation scale shift on sineMode**. -/
theorem dilation_inv_sineMode (α : ℝ) (hα : α ≠ 0) (k : ℕ) (x : ℝ) :
    dilation α⁻¹ (sineMode α k) x = sineMode α (k + 1) x := by
  unfold dilation sineMode
  congr 1
  field_simp
  ring

/-! ## Documentation: connection to operator self-similarity

The kernel self-similarity (`KernelSelfSimilarity.lean`):

  `V_P(x, y) = cos(π·|x−y|) + (1/a)·V_P(αx, αy)`

translates to an operator equation. Acting on `f` and using the
substitution `y' = αy` (valid on `ℝ` but with boundary subtleties on
`[0, 1]`):

  `(H_P f)(x) = (K_cos f)(x) + (1/(aα)) · (H_P (D_(α⁻¹) f))(αx)`

where `K_cos f := ∫ cos(π·|x−y|) f(y) dy` is the rank-2 cosine
kernel operator. Combined with the scale-shift identities
above:

  * `D_(α⁻¹) (cosineMode α k) = cosineMode α (k+1)` raises scale.
  * `D_α (cosineMode α (k+1)) = cosineMode α k` lowers scale.

So acting `H_P` on `cosineMode α k`:
  * The `K_cos` part involves `⟨cos(π·|·|), cosineMode α k⟩` inner products
    (computable via the matrix-entry catalog in `PolylogSpectrum.lean`).
  * The dilation part recurses to `cosineMode α (k+1)` evaluated at `αx`.

The recursion `(H_P · cosineMode α k)(x) ↔ (H_P · cosineMode α (k+1))(αx)`
connects eigenvalues at adjacent scales — the precise content of the
conjectured eigenvalue recursion `λ_(k+1) ↔ λ_k / a` underlying the
polylog formula `λ_k = a^(-k) Re[Li₁(e^{iπα^k})]`.

The boundary subtlety on `[0, 1]` (integration domain changes under
`y' = αy`) is the technical obstacle preventing a direct closed-form
proof; the manuscript's fractal-self-similar domain construction
resolves it on the appropriate Cantor-set domain. -/

end PrincipiaTractalis.Analytic
