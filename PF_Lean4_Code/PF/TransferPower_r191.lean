/-
# PF.TransferPower_r191

★★★ 2026-08-04 — TRACES OF POWERS: THE n-CYCLE LEFSCHETZ FORMULA ★★★

The n-th power of a transfer operator is ITSELF a weighted composition
system: its branches are the n-fold compositions Φ_α = φ_{kₙ} ∘ ⋯ ∘ φ_{k₁}
over words α = (k₁,…,kₙ), and its weights are the Birkhoff products
W_α(z) = Π_i w_{k_i}(φ_{k_{i-1}}⋯φ_{k₁} z).  This stone proves the
**closure of the r186/r188 hypothesis class under composition** — contraction
geometry, uniform bounds, holomorphy all propagate from the base system to
every word system — so the Lefschetz trace formula (r188c) applies verbatim
to L^n:

  `trace_pow_eq_residues` :
  Σ'_m A⁽ⁿ⁾[m,m]  =  Σ_{|α|=n}  W_α(x_α) / (1 − Φ_α'(x_α)),

the sum running over the K^n words, x_α the fixed point of Φ_α — i.e. the
**n-periodic points** of the underlying expanding map.  These are exactly
the periodic-orbit sums from which Fredholm determinants
det(1 ∓ L_s) = exp(−Σ_n Tr Lⁿ/n · (∓1)ⁿ⁺¹…) and hence the Selberg-zeta
factorization are built (Mayer 1991); the determinant assembly itself is NOT
formalized here — see scope note.

Key pieces:
* `listBranch` / `listWeight` — word compositions and Birkhoff weights;
* closure lemmas: `listBranch_cons_mem_tau` (compositions contract),
  `norm_listWeight_le` (‖W_α‖ ≤ W^n), `differentiableAt_listBranch/Weight`
  (holomorphy composes);
* `trace_pow_eq_residues` — the n-cycle trace formula;
* `deriv_listBranch_cons` — the chain-rule step for orbit multipliers;
* `gauss_square_trace` — non-vacuity witness: the squared golden branch,
  trace of L² for the K = 1 Gauss system = x⁴/(1−x⁴) = **(3√5−5)/10**.

Scope — NOT claimed: the operator identity A⁽ⁿ⁾ = Aⁿ (matrix power); the
word system's coefficient matrix is analyzed directly.  Equality with the
n-th matrix power is the operator-composition property — a separate stone
(needs coefficientwise composition of Cauchy expansions).  No determinants,
no zeta functions, no RH claims.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-08-04.
-/
import PF.MayerTrace_r190

set_option maxHeartbeats 1600000

namespace PrincipiaTractalis.HilbertSchmidtL2

open Complex Metric Real
open scoped Real

noncomputable section

variable {c : ℂ} {R R₁ τ W : ℝ} {K : ℕ} {w φ : Fin K → ℂ → ℂ}

/-! ### Word systems -/

/-- The branch of a word: `listBranch φ [k₁,…,kₙ] = φ_{kₙ} ∘ ⋯ ∘ φ_{k₁}`. -/
def listBranch (φ : Fin K → ℂ → ℂ) : List (Fin K) → ℂ → ℂ
  | [] => id
  | k :: l => fun z => listBranch φ l (φ k z)

/-- The Birkhoff weight of a word:
`listWeight w φ [k₁,…,kₙ] z = w_{k₁}(z)·w_{k₂}(φ_{k₁}z)⋯`. -/
def listWeight (w φ : Fin K → ℂ → ℂ) : List (Fin K) → ℂ → ℂ
  | [] => fun _ => 1
  | k :: l => fun z => w k z * listWeight w φ l (φ k z)

@[simp] theorem listBranch_nil (φ : Fin K → ℂ → ℂ) (z : ℂ) :
    listBranch φ [] z = z := rfl

@[simp] theorem listBranch_cons (φ : Fin K → ℂ → ℂ) (k : Fin K)
    (l : List (Fin K)) (z : ℂ) :
    listBranch φ (k :: l) z = listBranch φ l (φ k z) := rfl

@[simp] theorem listWeight_nil (w φ : Fin K → ℂ → ℂ) (z : ℂ) :
    listWeight w φ [] z = 1 := rfl

@[simp] theorem listWeight_cons (w φ : Fin K → ℂ → ℂ) (k : Fin K)
    (l : List (Fin K)) (z : ℂ) :
    listWeight w φ (k :: l) z = w k z * listWeight w φ l (φ k z) := rfl

/-! ### Closure of the hypothesis class under composition -/

/-- Word branches keep the big ball invariant. -/
theorem listBranch_mem_closedBall (hτR₁ : τ ≤ R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (l : List (Fin K)) :
    ∀ z ∈ Metric.closedBall c R₁, listBranch φ l z ∈ Metric.closedBall c R₁ := by
  induction l with
  | nil => intro z hz; simpa using hz
  | cons k l ih =>
    intro z hz
    exact ih _ (Metric.closedBall_subset_closedBall hτR₁ (hφ k z hz))

/-- Nonempty word branches contract into the small ball. -/
theorem listBranch_cons_mem_tau (hτR₁ : τ ≤ R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (l : List (Fin K)) (k : Fin K) :
    ∀ z ∈ Metric.closedBall c R₁,
      listBranch φ (k :: l) z ∈ Metric.closedBall c τ := by
  induction l generalizing k with
  | nil => intro z hz; exact hφ k z hz
  | cons k' l ih =>
    intro z hz
    exact ih k' _ (Metric.closedBall_subset_closedBall hτR₁ (hφ k z hz))

theorem listBranch_mem_tau_of_ne_nil (hτR₁ : τ ≤ R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    {l : List (Fin K)} (hl : l ≠ []) :
    ∀ z ∈ Metric.closedBall c R₁, listBranch φ l z ∈ Metric.closedBall c τ := by
  cases l with
  | nil => exact absurd rfl hl
  | cons k l => exact listBranch_cons_mem_tau hτR₁ hφ l k

/-- Birkhoff weights obey the product bound `‖W_α‖ ≤ W^{|α|}`. -/
theorem norm_listWeight_le (hτR₁ : τ ≤ R₁) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (l : List (Fin K)) :
    ∀ z ∈ Metric.closedBall c R₁, ‖listWeight w φ l z‖ ≤ W ^ l.length := by
  induction l with
  | nil => intro z _; simp
  | cons k l ih =>
    intro z hz
    have h2 := ih (φ k z)
      (Metric.closedBall_subset_closedBall hτR₁ (hφ k z hz))
    simp only [listWeight_cons, List.length_cons]
    calc ‖w k z * listWeight w φ l (φ k z)‖
        = ‖w k z‖ * ‖listWeight w φ l (φ k z)‖ := norm_mul _ _
      _ ≤ W * W ^ l.length :=
          mul_le_mul (hw k z hz) h2 (norm_nonneg _) hW
      _ = W ^ (l.length + 1) := by rw [pow_succ]; ring

/-- Holomorphy of word branches. -/
theorem differentiableAt_listBranch (hτR₁ : τ ≤ R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (l : List (Fin K)) :
    ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (listBranch φ l) z := by
  induction l with
  | nil => intro z _; exact differentiableAt_id
  | cons k l ih =>
    intro z hz
    exact (ih (φ k z)
      (Metric.closedBall_subset_closedBall hτR₁ (hφ k z hz))).comp z
      (hφd k z hz)

/-- Holomorphy of Birkhoff weights. -/
theorem differentiableAt_listWeight (hτR₁ : τ ≤ R₁)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    (l : List (Fin K)) :
    ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (listWeight w φ l) z := by
  induction l with
  | nil => intro z _; exact differentiableAt_const 1
  | cons k l ih =>
    intro z hz
    exact (hwd k z hz).mul ((ih (φ k z)
      (Metric.closedBall_subset_closedBall hτR₁ (hφ k z hz))).comp z
      (hφd k z hz))

/-- The chain-rule step for orbit multipliers:
`Φ_{k::l}'(z) = Φ_l'(φ_k z) · φ_k'(z)`. -/
theorem deriv_listBranch_cons (k : Fin K) (l : List (Fin K)) {z : ℂ}
    (hφz : DifferentiableAt ℂ (φ k) z)
    (hl : DifferentiableAt ℂ (listBranch φ l) (φ k z)) :
    deriv (listBranch φ (k :: l)) z
      = deriv (listBranch φ l) (φ k z) * deriv (φ k) z :=
  (hl.hasDerivAt.comp z hφz.hasDerivAt).deriv

/-- General `DiffContOnCl` builder (the r189 one was specialized to the
Mayer disc). -/
theorem diffContOnCl_of_differentiableAt (hR₁ : 0 < R₁) {f : ℂ → ℂ}
    (h : ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ f z) :
    DiffContOnCl ℂ f (Metric.ball c R₁) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball c hR₁.ne']
  exact fun z hz => (h z hz).differentiableWithinAt

/-! ### The n-th power system -/

/-- The branches of `L^n`: word compositions, indexed through
`(Fin n → Fin K) ≃ Fin (K^n)`. -/
def powerBranch (φ : Fin K → ℂ → ℂ) (n : ℕ) : Fin (K ^ n) → ℂ → ℂ :=
  fun i => listBranch φ (List.ofFn (finFunctionFinEquiv.symm i))

/-- The weights of `L^n`: Birkhoff products over words. -/
def powerWeight (w φ : Fin K → ℂ → ℂ) (n : ℕ) : Fin (K ^ n) → ℂ → ℂ :=
  fun i => listWeight w φ (List.ofFn (finFunctionFinEquiv.symm i))

/-! ### THE n-CYCLE TRACE FORMULA -/

/-- **Traces of powers**: the trace of the `n`-th iterate system is the sum
of fixed-point residues over all `K^n` words — the `n`-periodic points of
the underlying map:

`Σ'_m A⁽ⁿ⁾[m,m] = Σ_{|α|=n} W_α(x_α)/(1 − Φ_α'(x_α))`. -/
theorem trace_pow_eq_residues (hR : 0 < R) (hRR : R < R₁)
    (hτ0 : 0 ≤ τ) (hτR : τ < R) (hW : 0 ≤ W)
    (hw : ∀ k, ∀ z ∈ Metric.closedBall c R₁, ‖w k z‖ ≤ W)
    (hφ : ∀ k, ∀ z ∈ Metric.closedBall c R₁, φ k z ∈ Metric.closedBall c τ)
    (hwd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (w k) z)
    (hφd : ∀ k, ∀ z ∈ Metric.closedBall c R₁, DifferentiableAt ℂ (φ k) z)
    {n : ℕ} (hn : 0 < n)
    {x : Fin (K ^ n) → ℂ} (hx : ∀ i, x i ∈ Metric.ball c R₁)
    {g : Fin (K ^ n) → ℂ → ℂ}
    (hfactor : ∀ i, ∀ z ∈ Metric.closedBall c R₁,
      z - powerBranch φ n i z = (z - x i) * g i z)
    (hgd : ∀ i, DiffContOnCl ℂ (g i) (Metric.ball c R₁))
    (hg0 : ∀ i, ∀ z ∈ Metric.closedBall c R₁, g i z ≠ 0) :
    (∑' m : ℕ, transferMatrix c R R₁ (K ^ n)
        (powerWeight w φ n) (powerBranch φ n) m m)
      = ∑ i : Fin (K ^ n), powerWeight w φ n i (x i)
          / (1 - deriv (powerBranch φ n i) (x i)) := by
  have hR₁ : (0 : ℝ) < R₁ := hR.trans hRR
  have hτR₁ : τ ≤ R₁ := le_of_lt (hτR.trans hRR)
  have hword_ne : ∀ i : Fin (K ^ n),
      (List.ofFn (finFunctionFinEquiv.symm i) : List (Fin K)) ≠ [] :=
    fun i => List.ne_nil_of_length_pos (by rw [List.length_ofFn]; exact hn)
  apply trace_eq_residues hR hRR hτ0 hτR (pow_nonneg hW n)
  · -- uniform bound W^n on the sphere
    intro i z hz
    have h := norm_listWeight_le hτR₁ hW hw hφ
      (List.ofFn (finFunctionFinEquiv.symm i)) z
      (Metric.sphere_subset_closedBall hz)
    rwa [List.length_ofFn] at h
  · -- contraction of word branches
    intro i z hz
    exact listBranch_mem_tau_of_ne_nil hτR₁ hφ (hword_ne i) z
      (Metric.sphere_subset_closedBall hz)
  · exact hx
  · exact hfactor
  · -- holomorphy of Birkhoff weights
    intro i
    exact diffContOnCl_of_differentiableAt hR₁ fun z hz =>
      differentiableAt_listWeight hτR₁ hφ hwd hφd _ z hz
  · -- holomorphy of word branches
    intro i
    exact diffContOnCl_of_differentiableAt hR₁ fun z hz =>
      differentiableAt_listBranch hτR₁ hφ hφd _ z hz
  · exact hgd
  · exact hg0

/-! ### Non-vacuity witness: the squared golden branch -/

/-- `gaussBranch` fixes its fixed point (noble reciprocity, applied). -/
theorem gaussBranch_fix {a : ℝ} (ha : 1 ≤ a) :
    gaussBranch a ((gaussFix a : ℝ) : ℂ) = ((gaussFix a : ℝ) : ℂ) := by
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  show (((gaussFix a : ℝ) : ℂ) + (a : ℂ))⁻¹ = _
  rw [gaussFix_add_eq_inv ha, inv_inv]

theorem gaussWeight_fix {a : ℝ} (ha : 1 ≤ a) :
    gaussWeight a ((gaussFix a : ℝ) : ℂ) = ((gaussFix a : ℝ) : ℂ) ^ 2 := by
  show ((((gaussFix a : ℝ) : ℂ) + (a : ℂ))⁻¹) ^ 2 = _
  rw [gaussFix_add_eq_inv ha, inv_inv]

/-- `HasDerivAt` form of the r190 branch-derivative identity. -/
theorem hasDerivAt_gaussBranch_fix {a : ℝ} (ha : 1 ≤ a) :
    HasDerivAt (gaussBranch a) (-((gaussFix a : ℝ) : ℂ) ^ 2)
      ((gaussFix a : ℝ) : ℂ) := by
  have hx0 : 0 < gaussFix a := gaussFix_pos (by linarith)
  have hxC : ((gaussFix a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx0
  have hsum := gaussFix_add_eq_inv ha
  have hne : ((gaussFix a : ℝ) : ℂ) + (a : ℂ) ≠ 0 := by
    rw [hsum]; exact inv_ne_zero hxC
  have h1 : HasDerivAt (fun z : ℂ => z + (a : ℂ)) 1 ((gaussFix a : ℝ) : ℂ) :=
    (hasDerivAt_id _).add_const _
  have hd : HasDerivAt (fun z : ℂ => (z + (a : ℂ))⁻¹)
      (-1 / (((gaussFix a : ℝ) : ℂ) + (a : ℂ)) ^ 2) ((gaussFix a : ℝ) : ℂ) :=
    h1.inv hne
  have hval : -1 / (((gaussFix a : ℝ) : ℂ) + (a : ℂ)) ^ 2
      = -((gaussFix a : ℝ) : ℂ) ^ 2 := by
    rw [hsum, inv_pow, div_inv_eq_mul, neg_one_mul]
  exact hval ▸ hd

/-- The closed-ball version of the r189 contraction (same proof; the sphere
hypothesis was never needed). -/
theorem gaussBranch_mem_closedBall {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    gaussBranch a z ∈ Metric.closedBall (1 : ℂ) 1 := by
  have hne := denom_ne_zero ha hz
  have hre := re_ge_of_mem hz
  have hkey : ‖z + (a : ℂ) - 1‖ ≤ ‖z + (a : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    apply Real.sqrt_le_sqrt
    rw [Complex.normSq_apply, Complex.normSq_apply]
    have h1 : (z + (a : ℂ) - 1).re = z.re + a - 1 := by simp
    have h2 : (z + (a : ℂ) - 1).im = z.im := by simp
    have h3 : (z + (a : ℂ)).re = z.re + a := by simp
    have h4 : (z + (a : ℂ)).im = z.im := by simp
    rw [h1, h2, h3, h4]
    nlinarith [hre, ha]
  rw [Metric.mem_closedBall, dist_eq_norm, gaussBranch]
  have hrw : (z + (a : ℂ))⁻¹ - 1 = -((z + (a : ℂ) - 1) * (z + (a : ℂ))⁻¹) := by
    have h : (z + (a : ℂ) - 1) * (z + (a : ℂ))⁻¹ = 1 - (z + (a : ℂ))⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hne, one_mul]
    rw [h]; ring
  rw [hrw, norm_neg, norm_mul, norm_inv]
  have hden : (0 : ℝ) < ‖z + (a : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) (denom_norm_ge ha hz)
  calc ‖z + (a : ℂ) - 1‖ * ‖z + (a : ℂ)‖⁻¹
      ≤ ‖z + (a : ℂ)‖ * ‖z + (a : ℂ)‖⁻¹ :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hden)

theorem gaussWeight_norm_le_closedBall {a : ℝ} (ha : 1 ≤ a) {z : ℂ}
    (hz : z ∈ Metric.closedBall (1 : ℂ) (3 / 2)) :
    ‖gaussWeight a z‖ ≤ 4 := by
  have hd := denom_norm_ge ha hz
  rw [gaussWeight, norm_pow, norm_inv]
  have h2 : ‖z + (a : ℂ)‖⁻¹ ≤ 2 := by
    rw [← one_div]
    calc 1 / ‖z + (a : ℂ)‖ ≤ 1 / (1 / 2 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hd
      _ = 2 := by norm_num
  calc ‖z + (a : ℂ)‖⁻¹ ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ (by positivity) h2 2
    _ = 4 := by norm_num

/-- **The golden square** — non-vacuity witness for `trace_pow_eq_residues`:
the trace of `L²` for the single golden Gauss branch is
`x⁴/(1−x⁴) = (3√5−5)/10` where `x = 1/φ`. -/
theorem gauss_square_trace :
    (∑' m : ℕ, transferMatrix 1 (5 / 4) (3 / 2) (1 ^ 2)
        (powerWeight (fun _ : Fin 1 => gaussWeight 1)
          (fun _ : Fin 1 => gaussBranch 1) 2)
        (powerBranch (fun _ : Fin 1 => gaussBranch 1) 2) m m)
      = (((3 * Real.sqrt 5 - 5) / 10 : ℝ) : ℂ) := by
  have ha : (1 : ℝ) ≤ 1 := le_refl 1
  have hx0 : 0 < gaussFix 1 := gaussFix_pos (by norm_num)
  -- every word over Fin 1 is [0, 0]
  have hword : ∀ i : Fin (1 ^ 2),
      (List.ofFn (finFunctionFinEquiv.symm i) : List (Fin 1)) = [0, 0] := by
    intro i
    have hf : (finFunctionFinEquiv.symm i : Fin 2 → Fin 1) = fun _ => 0 :=
      Subsingleton.elim _ _
    rw [hf]
    decide
  -- casts: (1 : ℝ) and (2 : ℝ) into ℂ
  have hone : ((1 : ℝ) : ℂ) = 1 := Complex.ofReal_one
  have hid : ((gaussFix 1 : ℝ) : ℂ) ^ 2 + ((gaussFix 1 : ℝ) : ℂ) = 1 := by
    have h := gaussFix_identityC 1
    rwa [hone, one_mul] at h
  -- denominator nonvanishing on the disc
  have h1ne : ∀ z ∈ Metric.closedBall (1 : ℂ) (3 / 2), z + 1 ≠ 0 :=
    fun z hz => by
      have h := denom_ne_zero (a := 1) (by norm_num) hz
      rwa [hone] at h
  have h2ne : ∀ z ∈ Metric.closedBall (1 : ℂ) (3 / 2), z + 2 ≠ 0 :=
    fun z hz => by
      have h := denom_ne_zero (a := 2) (by norm_num) hz
      rwa [show ((2 : ℝ) : ℂ) = 2 by norm_num] at h
  -- the residue data
  set xC : ℂ := ((gaussFix 1 : ℝ) : ℂ) with hxCdef
  have hmain := trace_pow_eq_residues (c := 1) (R := 5 / 4) (R₁ := 3 / 2)
    (τ := 1) (W := 4)
    (w := fun _ : Fin 1 => gaussWeight 1) (φ := fun _ : Fin 1 => gaussBranch 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ z hz => gaussWeight_norm_le_closedBall ha hz)
    (fun _ z hz => gaussBranch_mem_closedBall ha hz)
    (fun _ z hz => (differentiableAt_denom_inv ha hz).pow 2)
    (fun _ z hz => differentiableAt_denom_inv ha hz)
    (n := 2) (by norm_num)
    (x := fun _ => xC) (fun _ => gaussFix_mem_ball ha)
    (g := fun _ => fun z => (z + 1 + xC) * (z + 2)⁻¹)
    (fun i z hz => by
      -- z − φ²(z) = (z − x)·(z + 1 + x)/(z + 2)
      have hb : powerBranch (fun _ : Fin 1 => gaussBranch 1) 2 i z
          = gaussBranch 1 (gaussBranch 1 z) := by
        show listBranch _ (List.ofFn (finFunctionFinEquiv.symm i)) z = _
        rw [hword i]
        simp only [listBranch_cons, listBranch_nil]
      rw [hb]
      have h1 := h1ne z hz
      have h2 := h2ne z hz
      have hφz : gaussBranch 1 z = (z + 1)⁻¹ := by
        show (z + ((1 : ℝ) : ℂ))⁻¹ = _
        rw [hone]
      have hφφ : gaussBranch 1 (gaussBranch 1 z) = (z + 1) * (z + 2)⁻¹ := by
        rw [hφz]
        show ((z + 1)⁻¹ + ((1 : ℝ) : ℂ))⁻¹ = _
        rw [hone,
          show (z + 1)⁻¹ + 1 = (z + 2) * (z + 1)⁻¹ from by field_simp; ring,
          mul_inv, inv_inv]
        ring
      rw [hφφ]
      field_simp
      linear_combination hid)
    (fun i => diffContOnCl_of_differentiableAt (by norm_num) fun z hz =>
      ((differentiableAt_id.add_const _).add_const _).mul
        ((differentiableAt_id.add_const _).inv (h2ne z hz)))
    (fun i z hz => by
      apply mul_ne_zero _ (inv_ne_zero (h2ne z hz))
      intro h0
      have hre := re_ge_of_mem hz
      have hsum : (z + 1 + xC).re = z.re + 1 + gaussFix 1 := by
        simp [hxCdef]
      rw [h0, Complex.zero_re] at hsum
      linarith [hsum.symm.le])
  rw [hmain]
  -- evaluate the single word residue
  have hsum1 : (∑ i : Fin (1 ^ 2),
      powerWeight (fun _ : Fin 1 => gaussWeight 1)
        (fun _ : Fin 1 => gaussBranch 1) 2 i xC
        / (1 - deriv (powerBranch (fun _ : Fin 1 => gaussBranch 1) 2 i) xC))
      = powerWeight (fun _ : Fin 1 => gaussWeight 1)
          (fun _ : Fin 1 => gaussBranch 1) 2 0 xC
          / (1 - deriv (powerBranch (fun _ : Fin 1 => gaussBranch 1) 2 0) xC) :=
    Fin.sum_univ_one _
  rw [hsum1]
  -- weight at the fixed point: x²·(x²·1)
  have hWval : powerWeight (fun _ : Fin 1 => gaussWeight 1)
      (fun _ : Fin 1 => gaussBranch 1) 2 0 xC
      = xC ^ 2 * (xC ^ 2 * 1) := by
    show listWeight _ _ (List.ofFn (finFunctionFinEquiv.symm 0)) xC = _
    rw [hword 0]
    simp only [listWeight_cons, listWeight_nil]
    rw [gaussWeight_fix ha, gaussBranch_fix ha, gaussWeight_fix ha]
  -- multiplier at the fixed point: (−x²)·(−x²)
  have hBfun : powerBranch (fun _ : Fin 1 => gaussBranch 1) 2 0
      = fun z => gaussBranch 1 (gaussBranch 1 z) := by
    funext z
    show listBranch _ (List.ofFn (finFunctionFinEquiv.symm 0)) z = _
    rw [hword 0]
    simp only [listBranch_cons, listBranch_nil]
  have hΦ : HasDerivAt (fun z => gaussBranch 1 (gaussBranch 1 z))
      (-xC ^ 2 * -xC ^ 2) xC := by
    have hbase := hasDerivAt_gaussBranch_fix ha
    have houter : HasDerivAt (gaussBranch 1) (-xC ^ 2) (gaussBranch 1 xC) := by
      rw [gaussBranch_fix ha]
      exact hbase
    exact houter.comp xC hbase
  rw [hWval, hBfun, hΦ.deriv]
  -- golden arithmetic: x⁴/(1 − x⁴) = (3√5−5)/10
  have hfix : gaussFix 1 = (Real.sqrt 5 - 1) / 2 := by
    unfold gaussFix
    norm_num
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hxlt : (Real.sqrt 5 - 1) / 2 < 1 := by
    nlinarith [h5, Real.sqrt_nonneg 5]
  have hx0' : (0 : ℝ) ≤ (Real.sqrt 5 - 1) / 2 := by
    nlinarith [h5, Real.sqrt_nonneg 5]
  have hreal : ((Real.sqrt 5 - 1) / 2) ^ 4 / (1 - ((Real.sqrt 5 - 1) / 2) ^ 4)
      = (3 * Real.sqrt 5 - 5) / 10 := by
    have hden : (0 : ℝ) < 1 - ((Real.sqrt 5 - 1) / 2) ^ 4 := by
      have := pow_lt_one₀ hx0' hxlt (n := 4) (by norm_num)
      linarith
    rw [div_eq_div_iff hden.ne' (by norm_num : (10 : ℝ) ≠ 0)]
    linear_combination ((3 * Real.sqrt 5 ^ 3 - 7 * Real.sqrt 5 ^ 2
      + 13 * Real.sqrt 5 - 17) / 16) * h5
  have hstep : xC ^ 2 * (xC ^ 2 * 1) / (1 - -xC ^ 2 * -xC ^ 2)
      = xC ^ 4 / (1 - xC ^ 4) := by ring
  rw [hstep, hxCdef, hfix]
  exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal

end

end PrincipiaTractalis.HilbertSchmidtL2

#print axioms PrincipiaTractalis.HilbertSchmidtL2.trace_pow_eq_residues
#print axioms PrincipiaTractalis.HilbertSchmidtL2.deriv_listBranch_cons
#print axioms PrincipiaTractalis.HilbertSchmidtL2.gauss_square_trace
