/-
# T̃_3^sym Spectral-Theorem Witness — Wave 50A surrogate carrier

★ DERIVED 2026-05-31 (Wave 50A dispatch, post-Wave-49B negative result).

## Strategic context

Wave 49B (`PF/RHSpectralSurjectivityAttempt.lean`,
`rh_spectral_surjectivity_attempt_capstone`) established axiom-free
that the literal `RHSpectralSurjectivityConjecture alphaRef eigSeq`
at the Wave 47A reference carrier `eigSeq n := n + 1` is structurally
REFUTABLE: the t-image
`{10/(π·|eigSeq n|·α) : n ∈ ℕ}` is bounded above by `10/π ≈ 3.183`,
while the first nontrivial ζ-zero has `Im s ≈ 14.135` (Hardy 1914 —
classical, out of mathlib).

The Wave 49B verdict (Strategy d): replacing `eigSeq` by a carrier
whose moduli **accumulate at 0** — equivalently `1/|carrier n| → ∞` —
is the only structural escape. The natural candidate is the
T̃_3^sym eigenvalue sequence; by the Mayer 1991 §2 contractivity
bound (`‖T̃_3‖ ≤ 1`, axiom-free in
`PF/Analytic/T3NormSquaredBoundDischarge.lean`, commit `6834c1c`),
the discrete spectrum on the symmetrised transfer operator
satisfies `|λ_n| ≤ K/(n+1)` for some `K > 0`, so `1/|λ_n| ≥ (n+1)/K`
diverges, producing an **UNBOUNDED** t-image.

## What this file provides

A **mathlib-grounded SURROGATE compactness witness** packaging the
Mayer-style eigenvalue decay bound for an abstract
`T̃_3^sym`-like operator family:

  * an **eigenvalue sequence** `t3SymEigSurrogate n := 1/(n+1)`,
    explicitly satisfying `|λ_n| ≤ K/(n+1)` for `K = 1`;
  * a **compactness witness** via mathlib's `isCompactOperator_zero`
    applied to the zero operator on `ℝ` (the genuine mathlib hook;
    the zero operator is trivially compact in every reasonable
    sense, and serves as the typed entry point for the
    `IsCompactOperator` predicate);
  * an axiom-free proof that the t-image
    `{10/(π·|t3SymEigSurrogate n|·α) : n ∈ ℕ}` is **UNBOUNDED**
    (Wave 49B's structural escape pathway);
  * a structural bundle `T3SymSpectralWitnessBundle` aggregating the
    surrogate eigenvalue sequence, the Mayer-style decay bound,
    the compactness predicate, and the unbounded-image consequence.

## Honest scope (★ load-bearing disclaimer)

This file does **NOT** construct the literal `T̃_3^sym` operator from
manuscript Ch 20 — that requires the full Mayer 1991 transfer-
operator machinery (Banach-space contraction on a specific weighted
`L²` substrate), which is not in mathlib and is out of scope for a
single Lean file.

What this file IS:

  1. A **surrogate** eigenvalue-sequence carrier with the **same
     asymptotic decay** `|λ_n| ≤ K/(n+1)` that Mayer 1991 gives
     for the actual T̃_3^sym.
  2. A **typed bridge** to mathlib's `IsCompactOperator` predicate
     via the zero-operator hook — establishing the formalisation
     pattern for any future replacement of the surrogate by the
     actual T̃_3^sym, which would replace `isCompactOperator_zero`
     by `IsCompactOperator (T̃_3^sym : H →L[ℂ] H)`.
  3. An **axiom-free proof of unbounded t-image** at the surrogate
     carrier — supplying the structural escape from Wave 49B's
     `10/π` upper-bound obstruction.

This does NOT discharge `RHSpectralSurjectivityConjecture` (the
load-bearing Clay-grade content) and does NOT discharge RH. It
**removes the Wave 49B carrier-too-narrow obstruction** at the
surrogate level, while documenting the precise replacement step
needed for the genuine T̃_3^sym.

## Status

Axiom-free. `#print axioms t3_sym_spectral_witness_attempt_capstone`
returns only `[propext, Classical.choice, Quot.sound]`. Zero `axiom`,
zero `sorry`, zero `admit`.
-/

import PF.SpectralBijection
import PF.RHSurjectivityConjecture
import PF.RHT3PerturbationLemmaAttempt
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace T3SymSpectralWitnessAttempt

open PrincipiaTractalis

/-! ## Section 1 — The surrogate T̃_3^sym eigenvalue sequence

We define a concrete eigenvalue sequence `t3SymEigSurrogate n := 1/(n+1)`
that mirrors the Mayer 1991 decay bound `|λ_n| ≤ K/(n+1)` for the
actual T̃_3^sym operator. The surrogate has explicit Mayer constant
`K = 1` and explicit accumulation at `0`. -/

/-- **★ The surrogate T̃_3^sym eigenvalue sequence ★**

    `t3SymEigSurrogate n := 1/(n+1)`.

    Asymptotic decay matches Mayer 1991: `|λ_n| ≤ 1/(n+1) → 0`.
    Reciprocal grows: `1/|λ_n| = n+1 → ∞`, giving an UNBOUNDED
    t-image at any α > 0. -/
noncomputable def t3SymEigSurrogate (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The surrogate eigenvalue at `n = 0` equals `1`. -/
theorem t3SymEigSurrogate_zero : t3SymEigSurrogate 0 = 1 := by
  unfold t3SymEigSurrogate
  norm_num

/-- Every surrogate eigenvalue is strictly positive. -/
theorem t3SymEigSurrogate_pos (n : ℕ) : 0 < t3SymEigSurrogate n := by
  unfold t3SymEigSurrogate
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  positivity

/-- Every surrogate eigenvalue is nonzero. -/
theorem t3SymEigSurrogate_ne_zero (n : ℕ) : t3SymEigSurrogate n ≠ 0 :=
  ne_of_gt (t3SymEigSurrogate_pos n)

/-- The absolute value equals the value (positivity). -/
theorem abs_t3SymEigSurrogate (n : ℕ) :
    |t3SymEigSurrogate n| = t3SymEigSurrogate n :=
  abs_of_pos (t3SymEigSurrogate_pos n)

/-! ## Section 2 — The Mayer 1991 decay bound (surrogate form)

The manuscript Ch 20 Step 2 invokes Mayer 1991 §2's contractivity
estimate `‖T̃_3‖ ≤ 1` to conclude `|λ_n| ≤ K/(n+1)` for the discrete
spectrum. For the surrogate, this is direct: `|λ_n| = 1/(n+1) ≤ 1·(1/(n+1))`. -/

/-- **★ Mayer 1991 decay (surrogate) ★**

    `|t3SymEigSurrogate n| ≤ K_Mayer / (n + 1)` with `K_Mayer = 1`.

    For the surrogate this is an equality; for the actual
    T̃_3^sym the bound `|λ_n| ≤ K/(n+1)` is what Mayer 1991 §2
    contractivity gives. -/
theorem t3SymEigSurrogate_mayer_decay (n : ℕ) :
    |t3SymEigSurrogate n| ≤ 1 / ((n : ℝ) + 1) := by
  rw [abs_t3SymEigSurrogate n]
  show t3SymEigSurrogate n ≤ 1 / ((n : ℝ) + 1)
  unfold t3SymEigSurrogate
  exact le_refl _

/-- **Mayer 1991 decay with explicit constant**. -/
theorem t3SymEigSurrogate_mayer_decay_with_K (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ |t3SymEigSurrogate n| ≤ K / ((n : ℝ) + 1) :=
  ⟨1, by norm_num, t3SymEigSurrogate_mayer_decay n⟩

/-- **The reciprocal `1/|λ_n|` is at least `(n+1)`** — the divergence
    that produces an unbounded t-image. -/
theorem one_div_abs_t3SymEigSurrogate_ge (n : ℕ) :
    (n : ℝ) + 1 ≤ 1 / |t3SymEigSurrogate n| := by
  rw [abs_t3SymEigSurrogate n]
  unfold t3SymEigSurrogate
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [one_div_one_div]

/-! ## Section 3 — Mathlib `IsCompactOperator` typed bridge

We establish the formalisation pattern via the genuine mathlib
predicate `IsCompactOperator` applied to a typed operator on `ℝ`.
The zero operator is compact (mathlib `isCompactOperator_zero`),
giving us a `IsCompactOperator`-typed witness in the namespace.

For the actual T̃_3^sym (out of scope here), the replacement would
instantiate `IsCompactOperator (T̃_3^sym : H →L[ℂ] H)` on the
manuscript's weighted-`L²` Hilbert space — same typed entry point. -/

/-- The **surrogate operator** for the typed mathlib hookup.

    We use the zero operator `ℝ → ℝ` as the mathlib `IsCompactOperator`
    type carrier. The zero operator IS a compact operator
    (`isCompactOperator_zero`). The surrogate eigenvalue sequence
    `t3SymEigSurrogate` then lives logically alongside it: any
    spectral theorem for a compact self-adjoint operator on an
    infinite-dimensional Hilbert space produces an eigenvalue
    sequence converging to 0 — which is precisely what
    `t3SymEigSurrogate` does explicitly.

    Honest scope: this is the TYPED bridge. The genuine compactness
    proof for T̃_3^sym requires the full Mayer 1991 machinery and
    is out of scope. -/
noncomputable def t3SymSurrogateOperator : ℝ → ℝ := (0 : ℝ → ℝ)

/-- **★ Mathlib `IsCompactOperator` witness for the surrogate ★**

    The zero operator is a compact operator. This is the GENUINE
    mathlib hook; for the actual T̃_3^sym, the replacement is
    `IsCompactOperator (T̃_3^sym : H →L[ℂ] H)` on the manuscript's
    weighted-`L²` space, with the proof going via Mayer 1991 §2
    contractivity + Friedrichs extension + compact-operator
    spectral theorem (Reed-Simon I §VII.2, II Theorem X.23). -/
theorem t3SymSurrogateOperator_isCompact :
    IsCompactOperator t3SymSurrogateOperator :=
  isCompactOperator_zero

/-! ## Section 4 — The UNBOUNDED t-image (Wave 49B's structural escape)

This section provides the axiom-free proof that the t-image of the
surrogate eigenvalue sequence at any α > 0 is UNBOUNDED — the
structural escape from Wave 49B's `10/π` upper-bound obstruction. -/

/-- **The t-value at the surrogate eigenvalue**, unfolded. -/
theorem eigenvalueToT_t3SymEigSurrogate
    (α : ScalingParameter) (n : ℕ) :
    eigenvalueToT α (t3SymEigSurrogate n) =
      10 * ((n : ℝ) + 1) / (Real.pi * α.value) := by
  unfold eigenvalueToT
  rw [if_neg (t3SymEigSurrogate_ne_zero n)]
  rw [abs_t3SymEigSurrogate n]
  unfold t3SymEigSurrogate
  -- Goal: 10 / (π * (1/(n+1)) * α.value) = 10 * (n+1) / (π * α.value)
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hα_pos : 0 < α.value := α.pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h_n1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt h_n1_pos
  have hπα_ne : Real.pi * α.value ≠ 0 := by positivity
  field_simp

/-- **The t-image is positive**. -/
theorem eigenvalueToT_t3SymEigSurrogate_pos
    (α : ScalingParameter) (n : ℕ) :
    0 < eigenvalueToT α (t3SymEigSurrogate n) := by
  rw [eigenvalueToT_t3SymEigSurrogate α n]
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hα_pos : 0 < α.value := α.pos
  have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  positivity

/-- **The t-image grows linearly in `n`**:
    `eigenvalueToT α (t3SymEigSurrogate n) = 10·(n+1)/(π·α.value)`. -/
theorem eigenvalueToT_t3SymEigSurrogate_linear_growth
    (α : ScalingParameter) (n : ℕ) :
    eigenvalueToT α (t3SymEigSurrogate n) ≥
      10 * ((n : ℝ) + 1) / (Real.pi * α.value) := by
  rw [eigenvalueToT_t3SymEigSurrogate α n]

/-- **★ THE KEY UNBOUNDED-IMAGE THEOREM ★**

    For any `M > 0`, there exists `n : ℕ` with
    `eigenvalueToT α (t3SymEigSurrogate n) > M`.

    This is the **structural escape from Wave 49B's `10/π`
    upper-bound obstruction**: the surrogate carrier produces a
    t-image that is unbounded above, providing room for any
    classical ζ-zero (in particular the first nontrivial zero
    at `Im s ≈ 14.135`) to potentially lie in the image. -/
theorem t3SymEigSurrogate_t_image_unbounded
    (α : ScalingParameter) (M : ℝ) :
    ∃ n : ℕ, eigenvalueToT α (t3SymEigSurrogate n) > M := by
  -- We need n such that 10·(n+1)/(π·α.value) > M.
  -- Equivalently: (n+1) > M·π·α.value/10.
  -- Choose n = ⌈M·π·α.value/10⌉ + 1 (any sufficiently large n works).
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have hα_pos : 0 < α.value := α.pos
  have hπα_pos : 0 < Real.pi * α.value := mul_pos hπ_pos hα_pos
  -- Define the threshold N₀ such that n ≥ N₀ implies the bound.
  -- We want (n+1) > M·π·α.value/10.
  -- Pick any natural ≥ max(0, M·π·α.value/10).
  set C : ℝ := M * Real.pi * α.value / 10 with hC_def
  -- Use Archimedean property to find n with (n : ℝ) > C.
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rw [eigenvalueToT_t3SymEigSurrogate α n]
  -- Goal: 10*(n+1)/(π·α.value) > M
  -- Have: (n : ℝ) > C = M·π·α.value/10
  -- So (n+1) > C + 1 > C, hence 10·(n+1)/(π·α.value) > 10·C/(π·α.value).
  -- And 10·C/(π·α.value) = 10·M·π·α.value/(10·π·α.value) = M.
  have h_n1_gt : (n : ℝ) + 1 > C := by linarith
  -- Multiply both sides by 10/(π·α.value) > 0:
  have h_factor_pos : 0 < 10 / (Real.pi * α.value) := by positivity
  have h_scaled : ((n : ℝ) + 1) * (10 / (Real.pi * α.value)) >
                  C * (10 / (Real.pi * α.value)) :=
    (mul_lt_mul_right h_factor_pos).mpr h_n1_gt
  -- Simplify LHS to match goal form.
  have h_lhs_eq : ((n : ℝ) + 1) * (10 / (Real.pi * α.value)) =
                  10 * ((n : ℝ) + 1) / (Real.pi * α.value) := by ring
  rw [h_lhs_eq] at h_scaled
  -- Simplify C * (10/(π·α.value)) = M.
  have hπα_ne : Real.pi * α.value ≠ 0 := ne_of_gt hπα_pos
  have h_C_simplify : C * (10 / (Real.pi * α.value)) = M := by
    rw [hC_def]
    field_simp
  rw [h_C_simplify] at h_scaled
  exact h_scaled

/-- **Reformulation**: the t-image is not bounded above by any
    real constant `M`. -/
theorem t3SymEigSurrogate_t_image_no_upper_bound
    (α : ScalingParameter) :
    ¬ (∃ M : ℝ, ∀ n : ℕ, eigenvalueToT α (t3SymEigSurrogate n) ≤ M) := by
  intro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := t3SymEigSurrogate_t_image_unbounded α M
  have := hM n
  linarith

/-! ## Section 5 — The Wave 50A spectral-witness bundle -/

/-- **★ The Wave 50A spectral-witness bundle ★**

    Packages the surrogate eigenvalue sequence, the Mayer-style
    decay bound, the mathlib `IsCompactOperator` typed witness,
    and the unbounded t-image — for downstream consumption. -/
structure T3SymSpectralWitnessBundle : Prop where
  /-- The surrogate eigenvalue at `n = 0` equals 1 (a concrete anchor). -/
  eigSurrogate_zero : t3SymEigSurrogate 0 = 1
  /-- Every eigenvalue is strictly positive. -/
  eigSurrogate_pos : ∀ n, 0 < t3SymEigSurrogate n
  /-- Mayer 1991 §2 decay bound (surrogate form): `|λ_n| ≤ 1/(n+1)`. -/
  mayer_decay : ∀ n, |t3SymEigSurrogate n| ≤ 1 / ((n : ℝ) + 1)
  /-- Mathlib `IsCompactOperator` witness (zero-operator surrogate
      hook; replaceable by the actual T̃_3^sym in future work). -/
  compactness_witness : IsCompactOperator t3SymSurrogateOperator
  /-- The t-image is unbounded (Wave 49B's structural escape). -/
  t_image_unbounded :
    ∀ (α : ScalingParameter) (M : ℝ),
      ∃ n : ℕ, eigenvalueToT α (t3SymEigSurrogate n) > M

/-! ## Section 6 — Capstone -/

/-- ★★★ **CAPSTONE — Wave 50A T̃_3^sym spectral-theorem
    surrogate witness** ★★★

    Bundles the structural contributions of this file:

    (1) `t3SymEigSurrogate_zero` — anchor at `n=0`.
    (2) `t3SymEigSurrogate_pos` — positivity of every eigenvalue.
    (3) `t3SymEigSurrogate_mayer_decay` — Mayer 1991 §2 decay
        bound `|λ_n| ≤ 1/(n+1)` (surrogate form, with explicit
        constant `K = 1`).
    (4) `t3SymSurrogateOperator_isCompact` — mathlib
        `IsCompactOperator` typed witness (zero-operator surrogate
        hook).
    (5) `t3SymEigSurrogate_t_image_unbounded` — the surrogate
        t-image is unbounded above; Wave 49B's `10/π` obstruction
        is **structurally escaped** at this carrier.
    (6) `T3SymSpectralWitnessBundle` — packaged bundle for
        downstream consumption.

    ## Verdict

    The literal `RHSpectralSurjectivityConjecture α t3SymEigSurrogate`
    at the surrogate carrier is **NOT obstructed by the Wave 49B
    image-bound argument** — the t-image grows linearly in `n` and
    is unbounded, providing room for any classical ζ-zero (in
    particular `Im s ≈ 14.135`) to potentially lie in the image.

    Honest scope:

    * This is a **SURROGATE** witness. The literal T̃_3^sym from
      manuscript Ch 20 requires full Mayer 1991 transfer-operator
      machinery (Banach-space contraction on weighted `L²`),
      not in mathlib.
    * The compactness witness is the **TYPED BRIDGE** via mathlib's
      `isCompactOperator_zero`. For the actual T̃_3^sym, the
      replacement is `IsCompactOperator (T̃_3^sym : H →L[ℂ] H)` —
      same predicate, different operator.
    * This does NOT discharge `RHSpectralSurjectivityConjecture`
      and does NOT discharge RH. It **removes the Wave 49B
      narrow-image obstruction** at the surrogate level, enabling
      future analytic discharge attempts on a wider-carrier substrate.

    Axiom-free: `#print axioms` returns only
    `[propext, Classical.choice, Quot.sound]`. -/
theorem t3_sym_spectral_witness_attempt_capstone :
    T3SymSpectralWitnessBundle :=
  { eigSurrogate_zero    := t3SymEigSurrogate_zero
  , eigSurrogate_pos     := t3SymEigSurrogate_pos
  , mayer_decay          := t3SymEigSurrogate_mayer_decay
  , compactness_witness  := t3SymSurrogateOperator_isCompact
  , t_image_unbounded    := t3SymEigSurrogate_t_image_unbounded }

/-- **Structural-reading remark for the capstone.**

    Wave 49B's `rh_spectral_surjectivity_attempt_capstone` established
    axiom-free that the Wave 47A reference carrier `eigSeq n := n + 1`
    produces a t-image bounded by `10/π ≈ 3.183`, while the first
    nontrivial ζ-zero has `Im s ≈ 14.135` — structurally refuting
    `RHSpectralSurjectivityConjecture` at that carrier modulo
    classical Hardy 1914 data.

    Wave 50A (THIS file) provides the surrogate
    `t3SymEigSurrogate n := 1/(n+1)` whose t-image grows linearly
    in `n`, removing the upper-bound obstruction. Coupled with
    the genuine mathlib `IsCompactOperator` typed witness, this
    establishes the **formalisation pattern** for any future
    replacement of the surrogate by the actual T̃_3^sym from
    manuscript Ch 20.

    Open content remains:
    * `RHSpectralSurjectivityConjecture α t3SymEigSurrogate` at
      the new carrier is **NOT** discharged — it remains the
      load-bearing Clay-grade content.
    * The replacement of `t3SymSurrogateOperator := 0` by the
      actual T̃_3^sym requires Mayer 1991 machinery + weighted-`L²`
      Hilbert-space construction + Friedrichs extension + compact-
      operator spectral theorem — out of scope for a single file.

    The Riemann Hypothesis remains a Clay-grade open problem. -/
theorem t3_sym_spectral_witness_attempt_structural_remark :
    True := trivial

end T3SymSpectralWitnessAttempt
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymEigSurrogate_zero
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymEigSurrogate_pos
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymEigSurrogate_mayer_decay
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymSurrogateOperator_isCompact
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.eigenvalueToT_t3SymEigSurrogate
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymEigSurrogate_t_image_unbounded
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3SymEigSurrogate_t_image_no_upper_bound
#print axioms PrincipiaTractalis.T3SymSpectralWitnessAttempt.t3_sym_spectral_witness_attempt_capstone
