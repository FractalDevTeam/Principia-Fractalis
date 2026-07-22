/-
# r106: Substrate UHF COMPLETION-TIER simplicity — the M3.3 rung

★ 2026-07-22 r106 — Milestone M3.3 of the Glimm-simplicity program:
the COMPLETION tier of the substrate UHF trace faithfulness route
(continuing r103/r104/r105) ★

## The framework-first content

r103 reduced completion-tier faithfulness of τ_UHF to a single honest
hypothesis: algebraic simplicity of the substrate UHF C*-algebra
completion `T∞ = TimelessFieldCompletion` (Glimm 1960). r104 built the
finite-dimensional discrete-Weyl averaging engine; r105 fired it at the
algebraic (direct-limit) tier, proving `TimelessFieldRing` is a simple
ring. r106 lifts the averaging engine INTO THE COMPLETION and proves,
UNCONDITIONALLY, the actual analytic heart of Glimm's argument: a
concrete averaging operator on `T∞` that is trace-detecting, ideal-
preserving, and a contraction, together with the Neumann-series
"units force ⊤" mechanism. What remains is a single, sharp, honestly
stated hypothesis — one that is now consumed by fully kernel-verified
analytic machinery rather than assumed raw.

**PRIORITY 1 — the reachable analytic infrastructure (all UNCONDITIONAL):**

  * `unit_mem_forces_top` — a unit inside a two-sided ideal forces the
    ideal to be ⊤ (multiply by the inverse; `TwoSidedIdeal.one_mem_iff`).
  * `oneSub_mem_forces_top` — Neumann membership: if `c • (1 - t) ∈ I`
    with `c ≠ 0` and `‖t‖ < 1`, then `I = ⊤`
    (`isUnit_one_sub_of_norm_lt_one` from complete-normed-ring geometric
    series + the scalar unit `algebraMap ℂ T∞ c`).
  * `levelToCompletion k : M_{3^k}(ℂ) →+* T∞` — the level-k
    *-embedding `A ↦ ↑⟦⟨k, A⟩⟧` into the completion, with the separate
    identities `levelToCompletion_star`, `levelToCompletion_smul`,
    `levelToCompletion_norm`, and `levelToCompletion_mem_unitary`.
  * `avgK k x := (1/(3^k)²) • Σ_{a,b} u_{a,b} · x · (u_{a,b})⋆`, the
    completion-level unitary averaging operator over the images
    `u_{a,b}` of the r104 Weyl unitaries `C^a S^b`. Properties:
      - `avgK_mem` : `x ∈ I → avgK k x ∈ I` (finite sum of
        u·x·u⋆, each in a two-sided ideal).
      - `avgK_sub` + `avgK_contraction` : `‖avgK k z‖ ≤ ‖z‖`
        (each conjugation by a unitary is isometric — `norm_*_unitary_*`
        C*-lemmas — the average is a contraction).
      - `avgK_on_level` : `avgK k (ι_k A) = τ_UHF(ι_k A) • 1`, the
        r104 matrix averaging identity transported through the
        *-ring-hom `ι_k` + trace coherence (`UHF_trace_coe`,
        `substrate_pre_trace_of_level`).
      - **`avgK_approx`** : for every `x` and `ε > 0` there is a level
        `k` with `‖avgK k x − τ_UHF(x) • 1‖ < ε` — approximation +
        contraction + 1-Lipschitz trace: this is the completion-tier
        averaging identity.

**PRIORITY 2 — the completion-tier engine (UNCONDITIONAL):**

  * **`ideal_trace_ne_zero_forces_top`** : if a two-sided ideal `I`
    contains some `x` with `τ_UHF(x) ≠ 0`, then `I = ⊤`. Proof (no
    circularity — no trace lower bound on `x⋆x` is ever used): average
    `x` into `I` (`avgK_mem`); by `avgK_approx` the average `w` is
    within `ε = ‖τ_UHF(x)‖` of `τ_UHF(x) • 1`; rescale by
    `τ_UHF(x)⁻¹` (ideals absorb ℂ-smul) to land `1 − t ∈ I` with
    `‖t‖ < 1`; `oneSub_mem_forces_top` gives `I = ⊤`.

  This is the genuine analytic content of Glimm's completion-tier
  simplicity theorem, fully kernel-verified.

**The remaining honest gap (M3.3 residual).** The non-circular spectral
step "from a nonzero ideal produce an element of nonzero trace" is the
one place mathlib cannot currently supply: it classically needs the
continuous functional calculus applied to a spectral INDICATOR
(spectral projection) plus a hereditary-subalgebra / corner
invertibility argument, and mathlib presently has `cfc` but no
`spectralProjection` and no corner/hereditary-subalgebra API. We
therefore isolate exactly that step as the named hypothesis

    `SubstrateCompletionTraceDetectsIdeals :=
       ∀ I : TwoSidedIdeal T∞, I ≠ ⊥ → ∃ x, x ∈ I ∧ UHF_trace x ≠ 0`

and prove RIGOROUSLY, via the r106 averaging engine, that it forces
full simplicity `∀ I, I = ⊥ ∨ I = ⊤`, and hence (composing with r103)
completion-tier faithfulness of `τ_UHF`. This is a strictly sharper and
more standard hypothesis than r103's raw simplicity: everything between
the trace-detection witness and faithfulness is now discharged by
kernel-verified analysis (averaging + Neumann + density).

Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
axioms. Zero sorries.

Stage 2026-07-22 r106 — the substrate completion-tier unitary averaging
engine and the reduction of completion simplicity/faithfulness to
trace-detection of ideals.
-/

import PF.SubstrateUHFTraceNullIdeal
import PF.SubstrateDirectLimitSimplicity
import PF.SubstrateUHFPreTraceDirectLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace SubstrateCompletionSimplicity

open scoped Matrix.Norms.L2Operator
open scoped ComplexOrder
open Matrix
open SubstrateMatrixUnitaryAveraging
open SubstrateDirectLimit
open SubstrateTimelessFieldCompletion
open SubstrateTimelessFieldNorm
open SubstrateUHFBoundedTrace
open SubstrateUHFPreTraceDirectLimit
open SubstrateUHFTraceCauchySchwarz
open SubstrateUHFTraceNullIdeal
open SubstrateUHFTraceIsStarPreserving
open SubstrateUHFTraceIsFaithful
open SubstrateDirectLimitSimplicity

/-! ## §1 — Neumann membership: units and `1 - t` force `⊤`

    (`NeZero (3 ^ k)` is inferred automatically by mathlib throughout.) -/

/-- **r106.a: a unit inside a two-sided ideal forces `⊤`.**

    If `w ∈ I` and `w` is a unit, then `1 = w⁻¹ · w ∈ I`, so `I = ⊤`
    by `TwoSidedIdeal.one_mem_iff`. -/
theorem unit_mem_forces_top (I : TwoSidedIdeal TimelessFieldCompletion)
    (w : TimelessFieldCompletion) (hw : w ∈ I) (hu : IsUnit w) : I = ⊤ := by
  obtain ⟨u, rfl⟩ := hu
  have h1 : (↑u⁻¹ : TimelessFieldCompletion) * (u : TimelessFieldCompletion) ∈ I :=
    I.mul_mem_left _ _ hw
  rw [Units.inv_mul] at h1
  exact I.one_mem_iff.mp h1

/-- **★★★ r106.b: NEUMANN MEMBERSHIP — `c • (1 - t) ∈ I` with `c ≠ 0`
    and `‖t‖ < 1` forces `I = ⊤` ★★★**

    `1 - t` is a unit by the complete-normed-ring geometric series
    (`isUnit_one_sub_of_norm_lt_one`); `algebraMap ℂ T∞ c` is a unit
    since `c ≠ 0`; their product `c • (1 - t)` is a unit lying in `I`,
    so `unit_mem_forces_top` applies. -/
theorem oneSub_mem_forces_top (I : TwoSidedIdeal TimelessFieldCompletion)
    (c : ℂ) (t : TimelessFieldCompletion) (hc : c ≠ 0) (ht : ‖t‖ < 1)
    (hmem : c • (1 - t) ∈ I) : I = ⊤ := by
  have hu : IsUnit (c • (1 - t)) := by
    rw [Algebra.smul_def]
    exact (IsUnit.map (algebraMap ℂ TimelessFieldCompletion) hc.isUnit).mul
      (isUnit_one_sub_of_norm_lt_one ht)
  exact unit_mem_forces_top I (c • (1 - t)) hmem hu

/-! ## §2 — The level-k *-embedding into the completion -/

/-- **r106.c: the level-k embedding `M_{3^k}(ℂ) →+* T∞`**, the
    composition `A ↦ ↑⟦⟨k, A⟩⟧` of the substrate level embedding with
    the completion coercion, bundled as a ring homomorphism. -/
noncomputable def levelToCompletion (k : ℕ) :
    Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ →+* TimelessFieldCompletion where
  toFun A := ((substrateLevelToTimelessField k A : TimelessFieldRing) : TimelessFieldCompletion)
  map_one' := by
    show ((substrateLevelToTimelessField k (1 : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
          : TimelessFieldRing) : TimelessFieldCompletion) = 1
    simp only [substrateLevelToTimelessField]
    rw [substrate_quotient_one_same_level k]
    exact UniformSpace.Completion.coe_one _
  map_mul' A B := by
    show ((substrateLevelToTimelessField k (A * B) : TimelessFieldRing) : TimelessFieldCompletion)
        = ((substrateLevelToTimelessField k A : TimelessFieldRing) : TimelessFieldCompletion)
          * ((substrateLevelToTimelessField k B : TimelessFieldRing) : TimelessFieldCompletion)
    simp only [substrateLevelToTimelessField]
    rw [← substrate_quotient_mul_same_level k A B, UniformSpace.Completion.coe_mul]
  map_zero' := by
    show ((substrateLevelToTimelessField k (0 : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
          : TimelessFieldRing) : TimelessFieldCompletion) = 0
    simp only [substrateLevelToTimelessField]
    rw [substrate_quotient_zero_same_level k]
    exact UniformSpace.Completion.coe_zero
  map_add' A B := by
    show ((substrateLevelToTimelessField k (A + B) : TimelessFieldRing) : TimelessFieldCompletion)
        = ((substrateLevelToTimelessField k A : TimelessFieldRing) : TimelessFieldCompletion)
          + ((substrateLevelToTimelessField k B : TimelessFieldRing) : TimelessFieldCompletion)
    simp only [substrateLevelToTimelessField]
    rw [← substrate_quotient_add_same_level k A B, UniformSpace.Completion.coe_add]

/-- **r106.c′: `levelToCompletion` at a matrix, unfolded.** -/
theorem levelToCompletion_apply (k : ℕ)
    (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    levelToCompletion k A
      = ((substrateLevelToTimelessField k A : TimelessFieldRing) : TimelessFieldCompletion) :=
  rfl

/-- **r106.d: the level embedding is *-preserving.** -/
theorem levelToCompletion_star (k : ℕ)
    (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    levelToCompletion k (star A) = star (levelToCompletion k A) := by
  rw [levelToCompletion_apply, levelToCompletion_apply]
  simp only [substrateLevelToTimelessField]
  rw [star_coe_TimelessFieldCompletion, substrate_quotient_star_same_level]

/-- **r106.e: the level embedding is ℂ-linear (scalar homogeneous).** -/
theorem levelToCompletion_smul (k : ℕ) (c : ℂ)
    (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    levelToCompletion k (c • A) = c • levelToCompletion k A := by
  rw [levelToCompletion_apply, levelToCompletion_apply]
  simp only [substrateLevelToTimelessField]
  rw [← substrate_quotient_smul_same_level c k A, UniformSpace.Completion.coe_smul]

/-- **r106.f: the level embedding is an isometry** — `‖ι_k A‖ = ‖A‖`,
    via r43 level isometry + completion `norm_coe`. -/
theorem levelToCompletion_norm (k : ℕ)
    (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    ‖levelToCompletion k A‖ = ‖A‖ := by
  rw [levelToCompletion_apply, UniformSpace.Completion.norm_coe]
  exact substrateLevelToTimelessField_opNorm_eq k A

/-- **r106.g: images of matrix unitaries are unitary in the
    completion** — the level embedding maps `Matrix.unitaryGroup` into
    `unitary T∞`. -/
theorem levelToCompletion_mem_unitary (k : ℕ)
    (M : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Fin (3 ^ k)) ℂ) :
    levelToCompletion k M ∈ unitary TimelessFieldCompletion := by
  rw [unitary.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [← levelToCompletion_star, ← (levelToCompletion k).map_mul,
        Matrix.mem_unitaryGroup_iff'.mp hM, (levelToCompletion k).map_one]
  · rw [← levelToCompletion_star, ← (levelToCompletion k).map_mul,
        Matrix.mem_unitaryGroup_iff.mp hM, (levelToCompletion k).map_one]

/-! ## §3 — The completion-level unitary averaging operator -/

/-- **r106.h: the level-k Weyl unitary in the completion** — the image
    `u_{a,b} := ι_k (C^a · S^b)` of the r104 clock-shift word. -/
noncomputable def levelWeyl (k : ℕ) (a b : Fin (3 ^ k)) : TimelessFieldCompletion :=
  levelToCompletion k (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))

/-- **r106.h′: every `levelWeyl` is unitary in `T∞`.** -/
theorem levelWeyl_mem_unitary (k : ℕ) (a b : Fin (3 ^ k)) :
    levelWeyl k a b ∈ unitary TimelessFieldCompletion :=
  levelToCompletion_mem_unitary k _ (clockShiftWord_mem_unitaryGroup (a : ℕ) (b : ℕ))

/-- **★★★ r106.i: THE COMPLETION UNITARY AVERAGING OPERATOR ★★★**

    `avgK k x := (1/(3^k)²) • Σ_{a,b} u_{a,b} · x · (u_{a,b})⋆`, the
    conjugation average over the `(3^k)²` level-k Weyl unitaries. -/
noncomputable def avgK (k : ℕ) (x : TimelessFieldCompletion) : TimelessFieldCompletion :=
  (1 / ((3 ^ k : ℕ) : ℂ) ^ 2) •
    ∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
      levelWeyl k a b * x * star (levelWeyl k a b)

/-- **r106.j: `avgK` preserves two-sided ideals** — the average of an
    ideal element stays in the ideal (finite sum of `u · x · u⋆`, each
    in `I`, then ℂ-scalar; all reducing to two-sided absorption). -/
theorem avgK_mem (I : TwoSidedIdeal TimelessFieldCompletion) (k : ℕ)
    (x : TimelessFieldCompletion) (hx : x ∈ I) : avgK k x ∈ I := by
  have hsmul : ∀ (c : ℂ) (y : TimelessFieldCompletion), y ∈ I → c • y ∈ I := by
    intro c y hy
    have hcy : c • y = (c • (1 : TimelessFieldCompletion)) * y := by
      rw [smul_mul_assoc, one_mul]
    rw [hcy]; exact I.mul_mem_left _ _ hy
  unfold avgK
  apply hsmul
  refine sum_mem (fun a _ => sum_mem (fun b _ => ?_))
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hx)

/-- **r106.k: per-term conjugation identity for the transport** —
    `u_{a,b} · ι_k A · (u_{a,b})⋆ = ι_k (C^a S^b · A · (C^a S^b)ᴴ)`. -/
theorem levelWeyl_conj (k : ℕ) (a b : Fin (3 ^ k))
    (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    levelWeyl k a b * levelToCompletion k A * star (levelWeyl k a b)
      = levelToCompletion k
          (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ) * A
            * (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))ᴴ) := by
  simp only [levelWeyl]
  rw [show star (levelToCompletion k
        (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ)))
        = levelToCompletion k
            (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))ᴴ from by
      rw [← levelToCompletion_star, Matrix.star_eq_conjTranspose],
      ← (levelToCompletion k).map_mul, ← (levelToCompletion k).map_mul]

/-- **★★★ r106.l: `avgK` ON A LEVEL ELEMENT EQUALS `τ_UHF • 1` ★★★**

    `avgK k (ι_k A) = τ_UHF(ι_k A) • 1`. The r104 matrix averaging
    identity `(1/(3^k)²)·Σ (C^aS^b) A (C^aS^b)ᴴ = (trace A / 3^k)•1`
    transported through the *-ring-hom `ι_k`, with the normalized trace
    matched to `τ_UHF` on the dense image (`UHF_trace_coe`,
    `substrate_pre_trace_of_level`). -/
theorem avgK_on_level (k : ℕ) (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ) :
    avgK k (levelToCompletion k A)
      = UHF_trace (levelToCompletion k A) • (1 : TimelessFieldCompletion) := by
  have hN : UHF_trace (levelToCompletion k A) = normalized_matrix_trace A := by
    rw [levelToCompletion_apply]
    simp only [substrateLevelToTimelessField]
    rw [UHF_trace_coe, substrate_pre_trace_of_level]
  have key := matrix_unitary_average_eq_trace_smul_one (n := 3 ^ k) A
  calc avgK k (levelToCompletion k A)
      = (1 / ((3 ^ k : ℕ) : ℂ) ^ 2) • ∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
          levelToCompletion k
            (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ) * A
              * (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))ᴴ) := by
        unfold avgK
        simp only [levelWeyl_conj]
    _ = (1 / ((3 ^ k : ℕ) : ℂ) ^ 2) • levelToCompletion k
          (∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
            clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ) * A
              * (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))ᴴ) := by
        congr 1
        simp only [map_sum]
    _ = levelToCompletion k ((1 / ((3 ^ k : ℕ) : ℂ) ^ 2) •
          ∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
            clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ) * A
              * (clockMatrix (3 ^ k) ^ (a : ℕ) * shiftMatrix (3 ^ k) ^ (b : ℕ))ᴴ) := by
        rw [levelToCompletion_smul]
    _ = levelToCompletion k ((Matrix.trace A / ((3 ^ k : ℕ) : ℂ)) • 1) := by
        rw [key]
    _ = (Matrix.trace A / ((3 ^ k : ℕ) : ℂ)) • levelToCompletion k 1 := by
        rw [levelToCompletion_smul]
    _ = (Matrix.trace A / ((3 ^ k : ℕ) : ℂ)) • (1 : TimelessFieldCompletion) := by
        rw [(levelToCompletion k).map_one]
    _ = normalized_matrix_trace A • (1 : TimelessFieldCompletion) := by
        simp only [normalized_matrix_trace]
    _ = UHF_trace (levelToCompletion k A) • (1 : TimelessFieldCompletion) := by
        rw [hN]

/-- **r106.m: `avgK` is additive on differences.** -/
theorem avgK_sub (k : ℕ) (x y : TimelessFieldCompletion) :
    avgK k (x - y) = avgK k x - avgK k y := by
  unfold avgK
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_sub, sub_mul]

/-- **★★★ r106.n: `avgK` IS A CONTRACTION ★★★** — `‖avgK k z‖ ≤ ‖z‖`.

    Each conjugation `u · z · u⋆` by a unitary is isometric
    (`norm_mul_mem_unitary` + `norm_mem_unitary_mul`), so the
    `(3^k)²`-term average, normalized by `1/(3^k)²`, is a contraction. -/
theorem avgK_contraction (k : ℕ) (z : TimelessFieldCompletion) :
    ‖avgK k z‖ ≤ ‖z‖ := by
  set N : ℝ := ((3 ^ k : ℕ) : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast Nat.pos_of_ne_zero (pow_ne_zero k (by norm_num))
  have hterm : ∀ a b : Fin (3 ^ k),
      ‖levelWeyl k a b * z * star (levelWeyl k a b)‖ = ‖z‖ := by
    intro a b
    have hu : levelWeyl k a b ∈ unitary TimelessFieldCompletion :=
      levelWeyl_mem_unitary k a b
    rw [CStarRing.norm_mul_mem_unitary _ (unitary.star_mem hu),
        CStarRing.norm_mem_unitary_mul _ hu]
  unfold avgK
  rw [norm_smul]
  have hc : ‖(1 / ((3 ^ k : ℕ) : ℂ) ^ 2)‖ = 1 / N ^ 2 := by
    rw [norm_div, norm_one, norm_pow, RCLike.norm_natCast, ← hN]
  rw [hc]
  have hsum : ‖∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
      levelWeyl k a b * z * star (levelWeyl k a b)‖ ≤ N ^ 2 * ‖z‖ := by
    calc ‖∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
            levelWeyl k a b * z * star (levelWeyl k a b)‖
        ≤ ∑ a : Fin (3 ^ k),
            ‖∑ b : Fin (3 ^ k), levelWeyl k a b * z * star (levelWeyl k a b)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _a : Fin (3 ^ k), ∑ _b : Fin (3 ^ k), ‖z‖ := by
          apply Finset.sum_le_sum
          intro a _
          calc ‖∑ b : Fin (3 ^ k), levelWeyl k a b * z * star (levelWeyl k a b)‖
              ≤ ∑ b : Fin (3 ^ k), ‖levelWeyl k a b * z * star (levelWeyl k a b)‖ :=
                norm_sum_le _ _
            _ = ∑ _b : Fin (3 ^ k), ‖z‖ := Finset.sum_congr rfl (fun b _ => hterm a b)
      _ = N ^ 2 * ‖z‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [hN]; push_cast; ring
  calc (1 / N ^ 2) * ‖∑ a : Fin (3 ^ k), ∑ b : Fin (3 ^ k),
          levelWeyl k a b * z * star (levelWeyl k a b)‖
      ≤ (1 / N ^ 2) * (N ^ 2 * ‖z‖) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ = ‖z‖ := by
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hNpos.ne'), one_mul]

/-! ## §4 — 1-Lipschitz bound for `UHF_trace` on the completion -/

/-- **r106.o: `UHF_trace` is 1-Lipschitz on the completion** —
    `dist (τ_UHF x) (τ_UHF y) ≤ dist x y`. Lifted from the r87 pre-trace
    1-Lipschitz bound via `induction_on₂` on the closed inequality. -/
theorem UHF_trace_dist_le (x y : TimelessFieldCompletion) :
    dist (UHF_trace x) (UHF_trace y) ≤ dist x y := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_le
      ((UHF_trace_uniformContinuous.continuous.comp continuous_fst).dist
        (UHF_trace_uniformContinuous.continuous.comp continuous_snd))
      (continuous_fst.dist continuous_snd)
  | ih a b =>
    rw [UHF_trace_coe, UHF_trace_coe, UniformSpace.Completion.dist_eq]
    exact substrate_pre_trace_dist_bound a b

/-! ## §5 — Nontriviality (so `‖1‖ = 1`) -/

/-- **r106.p: `T∞` is nontrivial** — `τ_UHF 1 = 1 ≠ 0 = τ_UHF 0`, so
    `(1 : T∞) ≠ 0`. Activates `NormOneClass` (hence `‖1‖ = 1`). -/
instance : Nontrivial TimelessFieldCompletion := by
  refine ⟨1, 0, ?_⟩
  intro h
  have hcoe : ((1 : TimelessFieldRing) : TimelessFieldCompletion) = 1 :=
    UniformSpace.Completion.coe_one _
  have h1 : UHF_trace (1 : TimelessFieldCompletion) = 1 := by
    rw [← hcoe, UHF_trace_coe]; exact substrate_pre_trace_one
  have h0 : UHF_trace (1 : TimelessFieldCompletion) = 0 := by
    rw [h]; exact UHF_trace_zero
  rw [h1] at h0
  exact one_ne_zero h0

/-! ## §6 — ★ The completion-tier averaging approximation ★ -/

/-- **★★★ r106.q: THE COMPLETION-TIER AVERAGING IDENTITY ★★★**

    For every `x : T∞` and every `ε > 0` there is a level `k` with

        `‖avgK k x − τ_UHF(x) • 1‖ < ε`.

    Density (r60 `substrate_finite_level_dense`) approximates `x` by a
    level element `y = ι_k A`; `avgK k y = τ_UHF(y) • 1` exactly
    (`avgK_on_level`); the contraction (`avgK_contraction`) controls the
    averaged difference and the 1-Lipschitz trace (`UHF_trace_dist_le`)
    controls the scalar difference. This is Glimm's averaging argument
    executed inside the completion. -/
theorem avgK_approx (x : TimelessFieldCompletion) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ‖avgK k x - UHF_trace x • (1 : TimelessFieldCompletion)‖ < ε := by
  obtain ⟨k, A, hA⟩ := substrate_finite_level_dense x (half_pos hε)
  refine ⟨k, ?_⟩
  set y : TimelessFieldCompletion := levelToCompletion k A with hy
  have hxy : ‖x - y‖ < ε / 2 := by
    rw [dist_eq_norm] at hA; exact hA
  have havgy : avgK k y = UHF_trace y • (1 : TimelessFieldCompletion) :=
    avgK_on_level k A
  have htrace : ‖UHF_trace y - UHF_trace x‖ ≤ ‖x - y‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm (UHF_trace y) (UHF_trace x)]
    exact UHF_trace_dist_le x y
  calc ‖avgK k x - UHF_trace x • (1 : TimelessFieldCompletion)‖
      = ‖avgK k (x - y) + (UHF_trace y - UHF_trace x) • (1 : TimelessFieldCompletion)‖ := by
        congr 1
        rw [avgK_sub, havgy, sub_smul]
        abel
    _ ≤ ‖avgK k (x - y)‖ + ‖(UHF_trace y - UHF_trace x) • (1 : TimelessFieldCompletion)‖ :=
        norm_add_le _ _
    _ = ‖avgK k (x - y)‖ + ‖UHF_trace y - UHF_trace x‖ := by
        rw [norm_smul, norm_one, mul_one]
    _ ≤ ‖x - y‖ + ‖UHF_trace y - UHF_trace x‖ := by
        gcongr; exact avgK_contraction k (x - y)
    _ ≤ ‖x - y‖ + ‖x - y‖ := by gcongr
    _ < ε := by linarith

/-! ## §7 — ★ PRIORITY 2: the completion-tier engine ★ -/

/-- **★★★ r106.r: NONZERO TRACE ON AN IDEAL FORCES `⊤` ★★★**
    (the non-circular completion-tier simplicity engine)

    If a two-sided ideal `I` contains any `x` with `τ_UHF(x) ≠ 0`, then
    `I = ⊤`.

    NO CIRCULARITY: no lower bound of the form `τ_UHF(x⋆x) > 0` is ever
    invoked. Average `x` into `I`; the average `w = avgK k x ∈ I` is
    within `ε = ‖τ_UHF(x)‖` of `τ_UHF(x) • 1` (`avgK_approx`); scaling
    by `τ_UHF(x)⁻¹` (ideals absorb ℂ-smul) places `τ_UHF(x)⁻¹ • w ∈ I`
    within norm `< 1` of `1`, i.e. `= 1 - t` with `‖t‖ < 1`; Neumann
    membership (`oneSub_mem_forces_top`) gives `I = ⊤`. -/
theorem ideal_trace_ne_zero_forces_top
    (I : TwoSidedIdeal TimelessFieldCompletion) (x : TimelessFieldCompletion)
    (hx : x ∈ I) (hτ : UHF_trace x ≠ 0) : I = ⊤ := by
  set c : ℂ := UHF_trace x with hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hτ
  obtain ⟨k, hk⟩ := avgK_approx x (ε := ‖c‖) hcpos
  set w : TimelessFieldCompletion := avgK k x with hw
  have hwI : w ∈ I := avgK_mem I k x hx
  -- ideals absorb ℂ-scalars
  have hsmul : ∀ (d : ℂ) (z : TimelessFieldCompletion), z ∈ I → d • z ∈ I := by
    intro d z hz
    have hdz : d • z = (d • (1 : TimelessFieldCompletion)) * z := by
      rw [smul_mul_assoc, one_mul]
    rw [hdz]; exact I.mul_mem_left _ _ hz
  have hcwI : c⁻¹ • w ∈ I := hsmul c⁻¹ w hwI
  have hnorm : ‖c⁻¹ • w - 1‖ < 1 := by
    have hrw : c⁻¹ • w - 1 = c⁻¹ • (w - c • 1) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hτ, one_smul]
    rw [hrw, norm_smul, norm_inv]
    calc ‖c‖⁻¹ * ‖w - c • 1‖ < ‖c‖⁻¹ * ‖c‖ :=
          mul_lt_mul_of_pos_left hk (inv_pos.mpr hcpos)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hcpos)
  refine oneSub_mem_forces_top I 1 (1 - c⁻¹ • w) one_ne_zero ?_ ?_
  · rw [norm_sub_rev]; exact hnorm
  · rw [one_smul, sub_sub_cancel]; exact hcwI

/-! ## §8 — the named M3.3 residual + the conditional close -/

/-- **★ r106.s: the M3.3 residual hypothesis — trace-detection of
    ideals.**

    Every nonzero two-sided ideal of `T∞` contains an element of nonzero
    UHF trace. This is the single honest gap remaining after the r106
    averaging engine: classically it is produced from a nonzero positive
    ideal element by the continuous functional calculus applied to a
    spectral indicator (spectral projection) plus corner invertibility,
    for which mathlib currently supplies `cfc` but neither
    `spectralProjection` nor a hereditary-subalgebra / corner API. It is
    STRICTLY SHARPER than r103's raw simplicity: the entire path from it
    to faithfulness is kernel-verified below via averaging + Neumann. -/
def SubstrateCompletionTraceDetectsIdeals : Prop :=
  ∀ I : TwoSidedIdeal TimelessFieldCompletion,
    I ≠ ⊥ → ∃ x, x ∈ I ∧ UHF_trace x ≠ 0

/-- **★★★ r106.t: TRACE-DETECTION FORCES SIMPLICITY ★★★**

    `SubstrateCompletionTraceDetectsIdeals → ∀ I, I = ⊥ ∨ I = ⊤`.
    Immediate from the r106.r averaging engine. -/
theorem completion_twoSidedIdeal_bot_or_top_of_traceDetects
    (h : SubstrateCompletionTraceDetectsIdeals) :
    ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤ := by
  intro I
  by_cases hbot : I = ⊥
  · exact Or.inl hbot
  · obtain ⟨x, hxI, hτ⟩ := h I hbot
    exact Or.inr (ideal_trace_ne_zero_forces_top I x hxI hτ)

/-- **★★★ r106.u: TRACE-DETECTION FORCES FAITHFULNESS ★★★**

    Composing r106.t with r103's `UHF_trace_faithful_of_simple`:
    trace-detection of ideals discharges completion-tier faithfulness of
    the substrate UHF trace, `τ_UHF(x⋆x) = 0 → x = 0`. -/
theorem UHF_trace_faithful_of_traceDetects
    (h : SubstrateCompletionTraceDetectsIdeals) :
    ∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0 :=
  UHF_trace_faithful_of_simple
    (completion_twoSidedIdeal_bot_or_top_of_traceDetects h)

/-! ## §9 — r106 capstone -/

/-- **★★★ r106 SUBSTRATE COMPLETION-TIER AVERAGING + M3.3 CAPSTONE ★★★**

    Bundles the r106 substrate content:

      (U1) **`oneSub_mem_forces_top`** — Neumann membership: a
           perturbation `c • (1 - t)` of the identity (`c ≠ 0`,
           `‖t‖ < 1`) inside a two-sided ideal forces `⊤`.
      (U2) **`avgK_mem`** — the completion averaging operator preserves
           two-sided ideals.
      (U3) **`avgK_contraction`** — `avgK` is a contraction
           (`‖avgK k z‖ ≤ ‖z‖`), each unitary conjugation isometric.
      (U4) **`avgK_on_level`** — `avgK k (ι_k A) = τ_UHF(ι_k A) • 1`:
           the r104 matrix averaging identity transported into `T∞`.
      (U5) **`avgK_approx`** — the completion-tier averaging identity:
           `‖avgK k x − τ_UHF(x) • 1‖ < ε` for a suitable level `k`.
      (U6) **`ideal_trace_ne_zero_forces_top`** — the NON-CIRCULAR
           engine: an ideal element of nonzero trace forces `⊤`.
      (U7) **`completion_twoSidedIdeal_bot_or_top_of_traceDetects`** and
           **`UHF_trace_faithful_of_traceDetects`** — the conditional
           close: `SubstrateCompletionTraceDetectsIdeals` forces full
           completion simplicity, hence (via r103) faithfulness.

    Kernel-only [propext, Classical.choice, Quot.sound]. Zero project
    axioms. Zero sorries.

    Substrate significance: r106 lands the analytic heart of Glimm's
    completion-tier simplicity theorem for the substrate UHF C*-algebra
    — a fully kernel-verified unitary averaging operator on
    `TimelessFieldCompletion` that is ideal-preserving, contractive, and
    trace-detecting — and reduces completion simplicity/faithfulness to
    a single sharp, standard hypothesis (`SubstrateCompletionTraceDetectsIdeals`)
    that the classical theory discharges via spectral projections /
    corner invertibility. The mathlib gap blocking the final
    unconditional close is the absence of a spectral-projection
    (indicator `cfc`) and hereditary-subalgebra / corner API. -/
theorem r106_substrate_completion_simplicity_capstone :
    (∀ (I : TwoSidedIdeal TimelessFieldCompletion) (c : ℂ)
        (t : TimelessFieldCompletion), c ≠ 0 → ‖t‖ < 1 →
        c • (1 - t) ∈ I → I = ⊤) ∧
    (∀ (I : TwoSidedIdeal TimelessFieldCompletion) (k : ℕ)
        (x : TimelessFieldCompletion), x ∈ I → avgK k x ∈ I) ∧
    (∀ (k : ℕ) (z : TimelessFieldCompletion), ‖avgK k z‖ ≤ ‖z‖) ∧
    (∀ (k : ℕ) (A : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℂ),
        avgK k (levelToCompletion k A)
          = UHF_trace (levelToCompletion k A) • (1 : TimelessFieldCompletion)) ∧
    (∀ (x : TimelessFieldCompletion) {ε : ℝ}, 0 < ε →
        ∃ k : ℕ, ‖avgK k x - UHF_trace x • (1 : TimelessFieldCompletion)‖ < ε) ∧
    (∀ (I : TwoSidedIdeal TimelessFieldCompletion) (x : TimelessFieldCompletion),
        x ∈ I → UHF_trace x ≠ 0 → I = ⊤) ∧
    (SubstrateCompletionTraceDetectsIdeals →
        ∀ I : TwoSidedIdeal TimelessFieldCompletion, I = ⊥ ∨ I = ⊤) ∧
    (SubstrateCompletionTraceDetectsIdeals →
        ∀ x : TimelessFieldCompletion, UHF_trace (star x * x) = 0 → x = 0) :=
  ⟨oneSub_mem_forces_top,
   avgK_mem,
   avgK_contraction,
   avgK_on_level,
   fun x _ hε => avgK_approx x hε,
   ideal_trace_ne_zero_forces_top,
   completion_twoSidedIdeal_bot_or_top_of_traceDetects,
   UHF_trace_faithful_of_traceDetects⟩

/-! ## §10 — Axiom audit -/

#print axioms unit_mem_forces_top
#print axioms oneSub_mem_forces_top
#print axioms levelToCompletion
#print axioms levelToCompletion_star
#print axioms levelToCompletion_smul
#print axioms levelToCompletion_norm
#print axioms levelToCompletion_mem_unitary
#print axioms levelWeyl_mem_unitary
#print axioms avgK_mem
#print axioms levelWeyl_conj
#print axioms avgK_on_level
#print axioms avgK_sub
#print axioms avgK_contraction
#print axioms UHF_trace_dist_le
#print axioms avgK_approx
#print axioms ideal_trace_ne_zero_forces_top
#print axioms completion_twoSidedIdeal_bot_or_top_of_traceDetects
#print axioms UHF_trace_faithful_of_traceDetects
#print axioms r106_substrate_completion_simplicity_capstone

end SubstrateCompletionSimplicity
end PrincipiaTractalis
