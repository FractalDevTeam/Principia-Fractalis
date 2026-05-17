/-
# Kernel Self-Similarity Equation

The structural heart of the manuscript's Ch 21 argument for the polylog
eigenvalue conjecture: the fractal kernel `V_P(x, y) = Σ aⁿ cos(παⁿd)`
satisfies a **self-similarity functional equation** under the scaling
`(x, y) ↦ (αx, αy)`.

## Main result

For `K = ℝ`, `a > 1`, `α ≥ 0`:

  ```
  V_P(x, y) = cos(π·|x−y|) + (1/a) · V_P(αx, αy)
  ```

Equivalently:

  ```
  V_P(αx, αy) = a · V_P(x, y) − a · cos(π·|x−y|)
  ```

## Significance

This is the structural identity that drives the conjectured polylog
formula `λ_k = (1/aᵏ) · Re[Li₁(e^{iπαᵏ})]`:

* It tells us that the kernel restricted to scale-`(αx, αy)` differs
  from the kernel at `(x, y)` by exactly the n=0 cosine term, modulo
  the `1/a` weight.
* At the operator level (formalized in `OperatorSelfSimilarity.lean` —
  a follow-on), this yields a functional equation relating
  `(H_P f)(x)` to `(H_P D_α f)(αx)`, where `D_α` is the dilation
  operator. Substituting candidate eigenfunctions `ψ_k(x) = cos(παᵏx)`
  into this functional equation produces a *recursion* on the
  eigenvalues `λ_k`, with the n=0 cosine inner product as the
  inhomogeneous term.
* That inner-product term, evaluated via the closed forms in
  `PolylogSpectrum.lean`, is conjecturally what generates the
  `Re[Li₁(e^{iπαᵏ})]` polylogarithm structure.

## What this file delivers

* `fractalKernelTerm_scale` — per-term scaling: each summand at scale
  `(αx, αy)` equals `a` times the next summand at `(x, y)`.
* `fractalKernelReal_self_similarity` — the full self-similarity
  equation, proven from per-term identity + tsum index shift.
* `fractalKernel_self_similarity` — complex-valued version.

All theorems use only Lean standard foundation; **zero project axioms**.

Stage L4+ — Kernel self-similarity (structural lever for the polylog
spectrum conjecture).
-/

import PF.IntegralKernel.FractalKernel

namespace PrincipiaTractalis.IntegralKernel

open MeasureTheory Real

/-! ## Per-term self-similarity -/

/-- **Per-term scaling identity** (on `K = ℝ`): the `n`-th summand of
    `fractalKernelTerm α a` at the scaled point `(αx, αy)` equals `a`
    times the `(n+1)`-th summand at `(x, y)`.

    This is the algebraic seed of the full self-similarity equation:
    the scaling `(x, y) ↦ (αx, αy)` shifts the summation index by one
    and absorbs a factor of `a` from the exponential weight. -/
theorem fractalKernelTerm_scale
    (α a : ℝ) (ha : a ≠ 0) (hα : 0 ≤ α) (x y : ℝ) (n : ℕ) :
    fractalKernelTerm α a ((α * x, α * y) : ℝ × ℝ) n =
    a * fractalKernelTerm α a ((x, y) : ℝ × ℝ) (n + 1) := by
  unfold fractalKernelTerm
  have hd : dist (α * x) (α * y) = α * dist x y := by
    simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hα]
  show a ^ (-(n : ℤ)) * Real.cos (Real.pi * α^n * dist (α * x) (α * y)) =
       a * (a ^ (-((n + 1 : ℕ) : ℤ)) * Real.cos (Real.pi * α^(n+1) * dist x y))
  rw [hd]
  -- Argument-of-cos equality: π · αⁿ · (α · d) = π · α^(n+1) · d.
  have hcos_arg : Real.pi * α^n * (α * dist x y) = Real.pi * α^(n+1) * dist x y := by
    rw [show α^(n+1) = α^n * α from by ring]; ring
  rw [hcos_arg]
  -- Scalar prefactor: a^(-n) = a · a^(-(n+1)).
  have hscalar : a ^ (-(n : ℤ)) = a * a ^ (-((n + 1 : ℕ) : ℤ)) := by
    rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + (-1 : ℤ) by push_cast; ring]
    rw [zpow_add₀ ha, zpow_neg_one]
    field_simp
  rw [hscalar]
  ring

/-! ## The self-similarity equation -/

/-- **Kernel self-similarity equation** (the structural lever of
    manuscript Ch 21's polylog argument):

      `V_P(x, y) = cos(π·|x−y|) + (1/a) · V_P(αx, αy)`

    on `K = ℝ`, under `a > 1` and `α ≥ 0`.

    Proof: peel off the `n = 0` term of `V_P(x, y) = Σ aⁿ cos(παⁿd)`
    (which is `cos(π·d)`), then re-index the tail
    `Σ_{n≥1} aⁿ cos(παⁿd)` against the per-term identity above to
    recognise it as `(1/a) · V_P(αx, αy)`. -/
theorem fractalKernelReal_self_similarity
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x y : ℝ) :
    fractalKernelReal α a ((x, y) : ℝ × ℝ) =
    Real.cos (Real.pi * dist x y) +
    (1 / a) * fractalKernelReal α a ((α * x, α * y) : ℝ × ℝ) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hsum_xy : Summable (fractalKernelTerm α a ((x, y) : ℝ × ℝ)) :=
    summable_fractalKernelTerm α ha ((x, y) : ℝ × ℝ)
  have hsum_αxαy : Summable (fractalKernelTerm α a ((α * x, α * y) : ℝ × ℝ)) :=
    summable_fractalKernelTerm α ha ((α * x, α * y) : ℝ × ℝ)
  unfold fractalKernelReal
  rw [Summable.tsum_eq_zero_add hsum_xy]
  -- The n=0 term is cos(π · dist x y):
  have hn0 : fractalKernelTerm α a ((x, y) : ℝ × ℝ) 0 = Real.cos (Real.pi * dist x y) := by
    unfold fractalKernelTerm; simp
  rw [hn0]
  congr 1
  rw [show (fun n => fractalKernelTerm α a ((x, y) : ℝ × ℝ) (n + 1))
       = (fun n => (1/a) * fractalKernelTerm α a ((α * x, α * y) : ℝ × ℝ) n)
       from ?_]
  · exact hsum_αxαy.tsum_mul_left (1/a)
  · funext n
    have := fractalKernelTerm_scale α a ha_ne hα x y n
    rw [this]
    field_simp

/-- **Self-similarity, complex form**: same equation lifted to the
    `Complex`-valued `fractalKernel`. -/
theorem fractalKernel_self_similarity
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x y : ℝ) :
    fractalKernel α a ((x, y) : ℝ × ℝ) =
    ((Real.cos (Real.pi * dist x y) : ℝ) : ℂ) +
    ((1 / a : ℝ) : ℂ) * fractalKernel α a ((α * x, α * y) : ℝ × ℝ) := by
  unfold fractalKernel
  rw [fractalKernelReal_self_similarity α a ha hα x y]
  push_cast
  ring

/-! ## Rearranged forms -/

/-- **Self-similarity, rearranged for the scaled kernel value**:

      `V_P(αx, αy) = a · V_P(x, y) − a · cos(π·|x−y|)`. -/
theorem fractalKernelReal_self_similarity_scaled
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x y : ℝ) :
    fractalKernelReal α a ((α * x, α * y) : ℝ × ℝ) =
    a * fractalKernelReal α a ((x, y) : ℝ × ℝ) - a * Real.cos (Real.pi * dist x y) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have h := fractalKernelReal_self_similarity α a ha hα x y
  -- V_P(x,y) = cos(π·d) + (1/a) · V_P(αx, αy)
  -- ⟹ a · V_P(x,y) − a · cos(π·d) = V_P(αx, αy)
  field_simp at h
  linarith

/-! ## Iterated (k-fold) self-similarity -/

/-- **k-fold iterated self-similarity** (the explicit recursion structure):

      `V_P(x, y) = Σ_{j=0}^{k-1} a^(-j) · cos(π · αʲ · |x−y|)
                + a^(-k) · V_P(αᵏx, αᵏy)`

    Direct proof by induction on `k`, using the single-step
    `fractalKernelReal_self_similarity` at each step to peel off the
    next summand and rescale the residual.

    This is the structural identity that drives the conjectured
    polylog formula: each application of the self-similar rescaling
    produces one term of the series, and the residual is the entire
    series at scale `(αᵏx, αᵏy)` weighted by `a^(-k)`. The conjectured
    eigenvalues `λ_k = a^(-k) · Re[Li₁(e^{iπαᵏ})]` are conjecturally
    the eigenvalues that organize this `a^(-k)` residual structure
    against the `cosineMode α k` eigenvector candidates from
    `PolylogSpectrum.lean`. -/
theorem fractalKernelReal_iterated_self_similarity
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (x y : ℝ) (k : ℕ) :
    fractalKernelReal α a ((x, y) : ℝ × ℝ) =
    (Finset.range k).sum
      (fun j => a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x y)) +
    a^(-(k : ℤ)) * fractalKernelReal α a ((α^k * x, α^k * y) : ℝ × ℝ) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [ih]
    have hα_n_nn : 0 ≤ α^n := pow_nonneg hα n
    have hself := fractalKernelReal_self_similarity α a ha hα (α^n * x) (α^n * y)
    have hd_eq : dist (α^n * x) (α^n * y) = α^n * dist x y := by
      simp [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hα_n_nn]
    rw [hd_eq] at hself
    have hαsucc_x : α * (α^n * x) = α^(n+1) * x := by ring
    have hαsucc_y : α * (α^n * y) = α^(n+1) * y := by ring
    rw [hαsucc_x, hαsucc_y] at hself
    have hcos_assoc :
        Real.cos (Real.pi * (α^n * dist x y)) = Real.cos (Real.pi * α^n * dist x y) := by
      congr 1; ring
    rw [hcos_assoc] at hself
    rw [Finset.sum_range_succ, hself]
    have ha_pos : 0 < a := lt_trans zero_lt_one ha
    have ha_ne : a ≠ 0 := ne_of_gt ha_pos
    have hpow : a^(-(n : ℤ)) * (1/a) = a^(-((n+1 : ℕ) : ℤ)) := by
      rw [show -((n + 1 : ℕ) : ℤ) = -(n : ℤ) + (-1 : ℤ) by push_cast; ring]
      rw [zpow_add₀ ha_ne, zpow_neg_one]
      ring
    set V := fractalKernelReal α a ((α^(n+1) * x, α^(n+1) * y) : ℝ × ℝ)
    set C := Real.cos (Real.pi * α^n * dist x y)
    set S := (Finset.range n).sum
      (fun j => a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x y))
    rw [← hpow]
    ring

/-! ## Residual bound and partial-sum approximation -/

/-- **Residual bound**: the rescaled-tail term in the iterated identity is
    bounded above by `a^(-k) · a/(a−1)`.

    Direct from the uniform-bound `|V_P z| ≤ a/(a−1)` (provable for all
    `a > 1` and any `z` — already in `IntegralKernel.FractalKernel`)
    combined with the positivity of `a^(-k)`. -/
theorem fractalKernelReal_residual_bound
    (α a : ℝ) (ha : 1 < a) (k : ℕ) (x y : ℝ) :
    |a^(-(k : ℤ)) * fractalKernelReal α a ((α^k * x, α^k * y) : ℝ × ℝ)|
    ≤ a^(-(k : ℤ)) * (a / (a - 1)) := by
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have hzpow_pos : 0 < a^(-(k : ℤ)) := zpow_pos ha_pos _
  rw [abs_mul, abs_of_pos hzpow_pos]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hzpow_pos)
  exact abs_fractalKernelReal_le α ha ((α^k * x, α^k * y) : ℝ × ℝ)

/-- **Partial-sum approximation error** (the rigorous spectral
    approximation theorem):

      `|V_P(x, y) − Σ_{j=0}^{k-1} a^(-j) · cos(π · αʲ · |x−y|)|
        ≤ a^(-k) · a/(a−1)`.

    Since `a > 1`, the right-hand side decays as `O(a^(-k))` uniformly
    in `(x, y)`. The first `k` summands of the series approximate the
    full fractal kernel to within this uniform error.

    This is the rigorous foundation for finite-rank spectral
    approximations of `H_P_at α a` — truncate the kernel to the first
    `k` cosine terms, and the resulting operator approximates `H_P`
    in uniform operator norm with error `O(a^(-k))`. -/
theorem fractalKernelReal_partial_sum_error
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (k : ℕ) (x y : ℝ) :
    |fractalKernelReal α a ((x, y) : ℝ × ℝ)
      - (Finset.range k).sum
          (fun j => a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x y))|
    ≤ a^(-(k : ℤ)) * (a / (a - 1)) := by
  rw [fractalKernelReal_iterated_self_similarity α a ha hα x y k]
  rw [add_sub_cancel_left]
  exact fractalKernelReal_residual_bound α a ha k x y

/-! ## Truncated kernel — finite-rank approximation infrastructure -/

/-- **Truncated fractal kernel** — the first `k` cosine summands:

      `V_P^(k)(x, y) := Σ_{j=0}^{k-1} a^(-j) · cos(π · αʲ · |x−y|)`.

    By the Mercer rank-2-per-scale decomposition
    (`PF/Analytic/FourierCosineDecomposition`), this is a finite sum
    of rank-2 separable kernels (one rank-2 piece per scale `j`), so
    the induced operator on `L²([0,1])` is rank `≤ 2k`. -/
noncomputable def truncatedFractalKernelReal
    (α a : ℝ) (k : ℕ) (z : ℝ × ℝ) : ℝ :=
  (Finset.range k).sum
    (fun j => a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist z.1 z.2))

/-- **Truncation residual identity** (rearrangement of the iterated
    self-similarity):

      `V_P − V_P^(k) = a^(-k) · V_P(αᵏ·x, αᵏ·y)`.

    The residual is exactly the rescaled kernel value at scale `αᵏ`,
    weighted by `a^(-k)`. -/
theorem fractalKernelReal_sub_truncated_eq_residual
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (k : ℕ) (x y : ℝ) :
    fractalKernelReal α a ((x, y) : ℝ × ℝ)
      - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)
    = a^(-(k : ℤ)) *
      fractalKernelReal α a ((α^k * x, α^k * y) : ℝ × ℝ) := by
  rw [fractalKernelReal_iterated_self_similarity α a ha hα x y k]
  unfold truncatedFractalKernelReal
  simp

/-- **Uniform L∞ approximation bound**: the error `‖V_P − V_P^(k)‖_∞`
    is bounded above by `a^(-k) · a/(a−1)`.

    Combining the residual identity with the uniform kernel bound
    `|V_P z| ≤ a/(a−1)`. Decays as `O(a^(-k))` since `a > 1`. This
    is the spectral-approximation theorem: the finite-rank operator
    induced by `V_P^(k)` converges to `H_P_at α a` in operator norm
    with rate `O(a^(-k))`. -/
theorem abs_fractalKernelReal_sub_truncated_le
    (α a : ℝ) (ha : 1 < a) (hα : 0 ≤ α) (k : ℕ) (x y : ℝ) :
    |fractalKernelReal α a ((x, y) : ℝ × ℝ)
      - truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)|
    ≤ a^(-(k : ℤ)) * (a / (a - 1)) := by
  rw [fractalKernelReal_sub_truncated_eq_residual α a ha hα k x y]
  exact fractalKernelReal_residual_bound α a ha k x y

/-! ## Pointwise bound on the truncated kernel -/

/-- **Uniform pointwise bound on the truncated kernel**:

      `|V_P^(k)(x, y)| ≤ a / (a − 1)`

    independent of `k`. Direct from `|cos| ≤ 1` and the geometric sum
    `Σ_{j<∞} (1/a)ʲ = a/(a−1)` for `a > 1`.

    This is uniform in `k`, so it complements the `O(a^(-k))`
    approximation-error bound: the truncated kernels are uniformly
    bounded, and converge to the full kernel as `k → ∞`. The Banach-
    Steinhaus / Hilbert-Schmidt machinery then gives the operator-norm
    convergence `‖T_k − H_P‖_op → 0`. -/
theorem abs_truncatedFractalKernelReal_le
    (α a : ℝ) (ha : 1 < a) (k : ℕ) (x y : ℝ) :
    |truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)|
    ≤ (a / (a - 1)) := by
  unfold truncatedFractalKernelReal
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have h_lt_one : (1 / a : ℝ) < 1 := by
    rw [one_div]; exact inv_lt_one_of_one_lt₀ ha
  have h_nn : (0 : ℝ) ≤ 1 / a := by positivity
  calc |(Finset.range k).sum
          (fun j => a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x y))|
      ≤ (Finset.range k).sum
          (fun j => |a^(-(j : ℤ)) * Real.cos (Real.pi * α^j * dist x y)|) :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range k).sum (fun j => |a^(-(j : ℤ))| * 1) := by
            apply Finset.sum_le_sum
            intros j _
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact Real.abs_cos_le_one _
    _ = (Finset.range k).sum (fun j => ((1/a) : ℝ)^j) := by
            apply Finset.sum_congr rfl
            intros j _
            rw [mul_one]
            rw [abs_of_pos (zpow_pos ha_pos _)]
            rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    _ ≤ ∑' j, ((1/a) : ℝ)^j := Summable.sum_le_tsum _
            (fun j _ => by positivity)
            (summable_geometric_of_lt_one h_nn h_lt_one)
    _ = (1 - 1/a)⁻¹ := tsum_geometric_of_lt_one h_nn h_lt_one
    _ = a / (a - 1) := by field_simp

/-! ## Continuity of truncated-kernel sections -/

/-- **The map `y ↦ V_P^(k)(x, y)` is continuous** for any fixed `x : ℝ`.

    Direct from the finite-sum form: each summand is `a^(-j) ·
    cos(π · αʲ · dist x y)`, where `dist x y` is continuous in `y`,
    `cos` is continuous, and `a^(-j)` is a constant. Finite sum of
    continuous functions is continuous.

    Closes the interval-integrability hypothesis of
    `fullOperatorAction_sub_truncated_bound` for continuous `f`: the
    integrand `V_P^(k)(x, y) · f(y)` is then a product of two
    continuous functions on `[0, 1]`, hence interval-integrable. -/
theorem continuous_truncatedFractalKernelReal_snd
    (α a : ℝ) (k : ℕ) (x : ℝ) :
    Continuous (fun y : ℝ =>
      truncatedFractalKernelReal α a k ((x, y) : ℝ × ℝ)) := by
  unfold truncatedFractalKernelReal
  apply continuous_finset_sum
  intros j _
  apply Continuous.mul continuous_const
  apply Real.continuous_cos.comp
  apply Continuous.mul continuous_const
  exact continuous_const.dist continuous_id'

/-! ## Documentation: connection to the eigenvalue conjecture

The chain of identities above provides the **structural framework** the
manuscript's Ch 21 polylog spectrum conjecture inhabits:

1. **Self-similarity** (`fractalKernelReal_self_similarity`): each
   application of the rescaling `(x, y) → (αx, αy)` peels off one
   cosine term and weights the residual by `1/a`. This generates the
   `a^(-k)` weight in the conjectured `λ_k = a^(-k) · Re[Li₁(...)]`.

2. **Iterated form** (`fractalKernelReal_iterated_self_similarity`):
   the explicit k-fold expansion, written as a partial sum plus
   rescaled residual.

3. **Tail bound** (`fractalKernelReal_residual_bound`,
   `fractalKernelReal_partial_sum_error`): the rescaled residual is
   uniformly `O(a^(-k))`, so the partial sums approximate `V_P`
   uniformly with explicitly-controlled error.

The CONJECTURE goes further: it claims the precise eigenvalue
extracted from the k-th level of this iteration is `Re[Li₁(e^{iπαᵏ})]`,
the polylogarithm-on-the-physical-Riemann-sheet evaluation. THAT step
requires:

* Identifying the eigenvectors of `H_P_at α a` (likely linear
  combinations of the `cosineMode α k` modes from
  `FourierCosineDecomposition`, organized by scale).
* Computing the action of the iterated kernel on those eigenvectors
  using the matrix entries from `PolylogSpectrum.lean`.
* Recognizing the resulting series as the polylog `Li₁(e^{iπαᵏ})`
  on the appropriate Riemann sheet.

That is the open mathematical content of Problem 1 in
`OPEN_PROBLEMS.md`. The pieces above are the axiom-free infrastructure
for any future attack on it. -/

end PrincipiaTractalis.IntegralKernel
