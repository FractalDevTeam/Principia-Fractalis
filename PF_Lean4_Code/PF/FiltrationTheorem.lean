/-
# The Filtration Theorem — τ_Kendall = 1.000 across 8 Tested T_3^sym Truncations

★ 2026-07-05 r24 — closing the empirical rank-order invariance in Lean 4 ★

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
2026-08-23 R123 FALSIFICATION RECONCILIATION.  Docstring references below
that say "Conjecture 8.X.2 (extremal-trace uniqueness) remains open" or
"is part of Conjecture 8.X.2, which remains open" are SUPERSEDED.

The projective-limit N → ∞ version of the nine-extremal-trace claim is
NOT open — it is FALSIFIED by r123's `no_nine_distinct_tracial_states`
in `PF/AlphaFromSubstrateKTheory_r123.lean`. The manuscript Conjecture
8.X.2 (nine distinct extremal tracial states of `π(T_∞)″`) cannot hold:
the substrate has ONE tracial state (r113 + r123).

This file's kernel content (τ_Kendall = 1.000 on the empirical rank
vectors of 8 finite truncations) is PRESERVED. The empirical rank-order
stability is a legitimate observation on the tested truncations. What
CANNOT be inferred from it is a nine-extremal-trace projective-limit
theorem. See `OPEN_PROBLEMS.md` §"2026-08-23 r123 falsification
reconciliation".
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

## Why this file exists

Paper §subsec:filtration-and-extremal-traces Theorem 8.X.1 (Filtration
Theorem) reports τ_Kendall(N, N') = 1.000 across ALL 28 pairs from the
8-truncation set N ∈ {600, 1000, 1500, 2000, 3000, 5000, 15000, 25000}.
That claim currently lives only in Python (rank_order_v3_full_metrics_2026-07-05.py
on Storage 2TB) and LaTeX. This file promotes it to a kernel-checked
Lean 4 theorem.

## The load-bearing observation

The 9 canonical α values, indexed by target μ = π/(10·α) ASCENDING (equivalently
α DESCENDING), are:

  1. α_NS       = 3π/2    (μ ≈ 0.0667)
  2. α_QG       = √(2π)   (μ ≈ 0.1253)
  3. α_BSD      = 3π/4    (μ ≈ 0.1333)
  4. α_YM       = 2       (μ ≈ 0.1571)
  5. α_NP       = φ+1/4   (μ ≈ 0.1682)
  6. α_Hodge    = φ       (μ ≈ 0.1942)
  7. α_RH       = 3/2     (μ ≈ 0.2094)
  8. α_P        = √2      (μ ≈ 0.2221)
  9. α_Poincaré = 1       (μ ≈ 0.3142)

For each tested truncation N of T_3^sym on L²([0,1], dx/x), we compute the
nearest-eigenvalue rank r_i(N) ∈ ℕ for each of the 9 targets and observe
that the resulting 9-tuple is STRICTLY MONOTONE INCREASING in the canonical
order above. Two strictly-monotone rank vectors of the same length yield
Kendall τ = 1 exactly, so this single monotonicity fact implies τ_Kendall
= 1 for every pair (N, N') and for every reordering permutation.

## What this file establishes (all axiom-free, kernel-only)

  * Eight `rankVec_N{600,1000,1500,2000,3000,5000,15000,25000} : List ℕ`
    literal definitions extracted from the archived scipy.linalg.eigh
    output on Storage 2TB (eigvals_N{...}.npy files).
  * Eight `List.Sorted (· < ·) rankVec_N...` theorems, each closed by
    `decide` on the 9-element list.
  * `filtration_theorem` — the load-bearing capstone: every rank vector
    in the empirical set is strictly ascending in the canonical order.
    Consequence documented: identity permutation on Fin 9 for every
    tested truncation, hence τ_Kendall = 1.000 on every pair.

## Honest scope

  * The rank vectors here are EMPIRICAL numerical data. Lean 4 kernel does
    not compute the T_3^sym eigenvalues; we encode the archived rank data
    and verify strict monotonicity in-kernel. The numerical eigenvalue
    computation is reproducible via
    `Papers/Data/ForwardPrediction/substrate_pathb_extension_2026-07-01.py`
    (see paper §subsec:substrate-self-corroboration for runtimes).
  * The theorem covers the 8 finite truncations tested. The projective-limit
    N → ∞ generalization is part of Conjecture 8.X.2 (extremal-trace
    uniqueness) which remains open (OPEN_PROBLEMS.md Priority 1a).
  * τ_Kendall = 1.000 is tautologically true given monotone-density
    ordering, as the paper's honest-caveat note in Theorem 8.X.1
    emphasizes. This file encodes THE CLAIM ("all 8 truncations yield
    identity rank permutation on Fin 9") into Lean, not the stronger
    density-independence claim.

Stage 2026-07-05 r24 — Filtration Theorem promoted to kernel-checked form.
-/

import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace PrincipiaTractalis
namespace FiltrationTheorem

/-! ## §1 — The eight tested truncation dimensions -/

/-- The eight tested truncation dimensions of T_3^sym at which the
    9-canonical rank vector has been computed. -/
def testedTruncations : List ℕ := [600, 1000, 1500, 2000, 3000, 5000, 15000, 25000]

/-! ## §2 — Empirical rank vectors from archived scipy.linalg.eigh output

Each `rankVec_N` is the 9-element list r_i(N) = rank of nearest |λ| to
target μ_i = π/(10·α_i) among |λ|-ascending eigenvalues of the
Hermitian truncation `H_N = (T_N + T_N*)/2`, with tie-break to smaller k.

Canonical index order (i = 1, …, 9):
  1 ↦ α_NS = 3π/2         (target μ ≈ 0.06667)
  2 ↦ α_QG = √(2π)        (target μ ≈ 0.12533)
  3 ↦ α_BSD = 3π/4        (target μ ≈ 0.13333)
  4 ↦ α_YM = 2            (target μ ≈ 0.15708)
  5 ↦ α_NP = φ+1/4        (target μ ≈ 0.16821)
  6 ↦ α_Hodge = φ         (target μ ≈ 0.19416)
  7 ↦ α_RH = 3/2          (target μ ≈ 0.20944)
  8 ↦ α_P = √2            (target μ ≈ 0.22214)
  9 ↦ α_Poincaré = 1      (target μ ≈ 0.31416)

Source of numerical eigenvalues: `Papers/Data/ForwardPrediction/
substrate_pathb_extension_2026-07-01.py` + Storage 2TB
`eigvals_N{...}.npy` archives. -/

/-- Rank vector at N = 600 (N_total = 600 non-negligible eigenvalues). -/
def rankVec_N600 : List ℕ := [47, 90, 97, 109, 114, 137, 148, 155, 230]

/-- Rank vector at N = 1000 (N_total = 1000). -/
def rankVec_N1000 : List ℕ := [79, 151, 161, 181, 190, 226, 245, 255, 379]

/-- Rank vector at N = 1500 (N_total = 1500). -/
def rankVec_N1500 : List ℕ := [117, 224, 240, 269, 283, 338, 364, 381, 568]

/-- Rank vector at N = 2000 (N_total = 2000). -/
def rankVec_N2000 : List ℕ := [156, 298, 321, 358, 378, 450, 486, 507, 757]

/-- Rank vector at N = 3000 (N_total = 3000). -/
def rankVec_N3000 : List ℕ := [237, 447, 482, 540, 568, 675, 731, 762, 1138]

/-- Rank vector at N = 5000 (N_total = 4985 after numerical zero filtering). -/
def rankVec_N5000 : List ℕ := [382, 730, 787, 882, 931, 1110, 1202, 1256, 1883]

/-- Rank vector at N = 15000 (N_total = 14854 after numerical zero filtering). -/
def rankVec_N15000 : List ℕ := [1052, 2090, 2260, 2543, 2689, 3225, 3501, 3660, 5547]

/-- Rank vector at N = 25000 (N_total = 24710 after numerical zero filtering). -/
def rankVec_N25000 : List ℕ := [1710, 3435, 3719, 4189, 4434, 5328, 5787, 6050, 9200]

/-- The bundle of all 8 empirical rank vectors. -/
def empiricalRankVectors : List (List ℕ) :=
  [rankVec_N600, rankVec_N1000, rankVec_N1500, rankVec_N2000,
   rankVec_N3000, rankVec_N5000, rankVec_N15000, rankVec_N25000]

/-! ## §3 — Strict monotonicity of each rank vector -/

/-- Strict monotonicity of the N=600 rank vector. Proved by `decide` on the
    9-element list. -/
theorem rankVec_N600_strictSorted : List.Sorted (· < ·) rankVec_N600 := by decide

/-- Strict monotonicity of the N=1000 rank vector. -/
theorem rankVec_N1000_strictSorted : List.Sorted (· < ·) rankVec_N1000 := by decide

/-- Strict monotonicity of the N=1500 rank vector. -/
theorem rankVec_N1500_strictSorted : List.Sorted (· < ·) rankVec_N1500 := by decide

/-- Strict monotonicity of the N=2000 rank vector. -/
theorem rankVec_N2000_strictSorted : List.Sorted (· < ·) rankVec_N2000 := by decide

/-- Strict monotonicity of the N=3000 rank vector. -/
theorem rankVec_N3000_strictSorted : List.Sorted (· < ·) rankVec_N3000 := by decide

/-- Strict monotonicity of the N=5000 rank vector. -/
theorem rankVec_N5000_strictSorted : List.Sorted (· < ·) rankVec_N5000 := by decide

/-- Strict monotonicity of the N=15000 rank vector. -/
theorem rankVec_N15000_strictSorted : List.Sorted (· < ·) rankVec_N15000 := by decide

/-- Strict monotonicity of the N=25000 rank vector. -/
theorem rankVec_N25000_strictSorted : List.Sorted (· < ·) rankVec_N25000 := by decide

/-! ## §4 — Length uniformity: each rank vector has exactly 9 entries -/

/-- Each empirical rank vector has length 9 (the 9 canonical α classes). -/
theorem rankVec_lengths_all_nine :
    rankVec_N600.length = 9 ∧
    rankVec_N1000.length = 9 ∧
    rankVec_N1500.length = 9 ∧
    rankVec_N2000.length = 9 ∧
    rankVec_N3000.length = 9 ∧
    rankVec_N5000.length = 9 ∧
    rankVec_N15000.length = 9 ∧
    rankVec_N25000.length = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## §5 — The Filtration Theorem capstone -/

/-- **★★★ FILTRATION THEOREM (paper Theorem 8.X.1, Lean-encoded form) ★★★**

    All 8 empirical rank vectors at the tested truncations of T_3^sym are
    strictly ascending in the canonical order (α_NS, α_QG, α_BSD, α_YM,
    α_NP, α_Hodge, α_RH, α_P, α_Poincaré) — i.e. the target μ = π/(10·α)
    ascending order, equivalently α descending.

    **Interpretation.** For every tested N ∈ {600, 1000, 1500, 2000, 3000,
    5000, 15000, 25000}, the permutation π_N : Fin 9 → Fin 9 induced by
    argsort of the rank vector is the IDENTITY permutation.

    **Consequence.** Any two rank vectors r_N, r_{N'} in this bundle
    yield Kendall τ(r_N, r_{N'}) = 1 exactly, since both are strictly
    monotone increasing on the same 9-element index set. All 28 pairs
    yield τ_Kendall = 1.000 from this one monotonicity fact.

    **Honest caveat** (per paper §8.X.1). τ_Kendall = 1.000 across
    truncations is partially tautological under monotone spectral density
    of T_3^sym. The theorem establishes that the 9 canonicals project to
    9 stable CDF-positions along the truncation-spectrum density; the
    full spectral-uniqueness closure (finite discrete extremal-trace
    space equal to the 9-tuple) requires Conjecture 8.X.2, which remains
    open (OPEN_PROBLEMS.md Priority 1a). -/
theorem filtration_theorem :
    ∀ v ∈ empiricalRankVectors, List.Sorted (· < ·) v := by
  intro v hv
  simp only [empiricalRankVectors, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rankVec_N600_strictSorted
  · exact rankVec_N1000_strictSorted
  · exact rankVec_N1500_strictSorted
  · exact rankVec_N2000_strictSorted
  · exact rankVec_N3000_strictSorted
  · exact rankVec_N5000_strictSorted
  · exact rankVec_N15000_strictSorted
  · exact rankVec_N25000_strictSorted

/-- **Explicit corollary**: eight strict-sortedness facts bundled as a
    single conjunction, for citation convenience. -/
theorem filtration_theorem_bundle :
    List.Sorted (· < ·) rankVec_N600 ∧
    List.Sorted (· < ·) rankVec_N1000 ∧
    List.Sorted (· < ·) rankVec_N1500 ∧
    List.Sorted (· < ·) rankVec_N2000 ∧
    List.Sorted (· < ·) rankVec_N3000 ∧
    List.Sorted (· < ·) rankVec_N5000 ∧
    List.Sorted (· < ·) rankVec_N15000 ∧
    List.Sorted (· < ·) rankVec_N25000 :=
  ⟨rankVec_N600_strictSorted, rankVec_N1000_strictSorted,
   rankVec_N1500_strictSorted, rankVec_N2000_strictSorted,
   rankVec_N3000_strictSorted, rankVec_N5000_strictSorted,
   rankVec_N15000_strictSorted, rankVec_N25000_strictSorted⟩

/-! ## §6 — Honest scope declarations

**DOES**:
  * Encode the 8 empirical rank vectors from archived scipy.linalg.eigh
    output as literal `List ℕ` definitions.
  * Prove each is strictly ascending — kernel-checkable via `decide`.
  * Bundle the 8 monotonicity theorems as `filtration_theorem`,
    documenting τ_Kendall = 1.000 as a direct consequence.

**DOES NOT**:
  * Compute the T_3^sym eigenvalues in Lean. The rank vectors are
    empirical data extracted from Python numerical computation.
    Reproducibility path: run
    `Papers/Data/ForwardPrediction/substrate_pathb_extension_2026-07-01.py`
    followed by `rank_order_v3_full_metrics_2026-07-05.py` on Storage 2TB.
  * Prove the projective-limit N → ∞ version. That is Conjecture 8.X.2
    (extremal-trace uniqueness) — the substrate identifies the 9 α-values
    as the unique extremal tracial states of π(T_∞)″, but the finite-
    dimensional-center structure required to break Type III₁ uniqueness
    remains an open conjecture (OPEN_PROBLEMS.md Priority 1a).
  * Close the density-independence claim. τ_Kendall = 1 across truncations
    follows from monotone density plus fixed target order; the framework's
    9 canonicals project to 9 stable CDF-positions but this alone does not
    demonstrate operator-algebra spectral uniqueness. The paper §8.X.1
    honest-caveat note documents this scope.
-/

end FiltrationTheorem
end PrincipiaTractalis
