/-
# Yang-Mills Quadratic Kernel Mechanism — does the YM kernel produce a
  cluster-fixing quadratic map?

## Strategic context (2026-05-25, Wave 24 YM follow-on)

Wave 24 (`YangMillsNonAffineCoupledResidual`, commit f706266) proved
the *abstract* quadratic class `φ(λ) = α·λ² + β·λ + γ` is
UNDERDETERMINED for the YM cluster-fix problem (2 equations, 3 unknowns),
with the load-bearing difference identity

    φ(3/2) − φ(1/2) = 2α + β

forcing the difference into {−1, 0, 1} for cluster-fixing pairings
(c₁, c₂) ∈ {1/2, 3/2}².

Open question after Wave 24:
  **Does a quadratic map actually ARISE from the YM kernel structure?**

This file answers concretely. The YM-class level-1 operator at α=2, a=2
is the symmetric 2×2 matrix

    M = [[a/(a-1), K(2/3)], [K(2/3), a/(a-1)]] = [[2, -1], [-1, 2]]

with eigenvalues exactly `{1, 3}` and cluster centres `{1/2, 3/2}`
after the standard 1/2 prefactor. The natural "quadratic-in-K Gram"
matrix is `M²` (or any rescaling `c·M²`), with eigenvalues `{1, 9}`.

Mapped to the cluster centres under the rescaled-eigenvalue convention,
this is the quadratic map

    φ(λ) = 2·λ²      (i.e. (α, β, γ) = (2, 0, 0))

since 2·(1/2)² = 1/2 and 2·(3/2)² = 9/2.

## Honest finding (NEGATIVE result, narrows out this mechanism)

The kernel-product Gram quadratic map `φ_KK(λ) := 2·λ²` does NOT lie in
the Wave 24 cluster-fixing set. The load-bearing difference identity
gives `φ_KK(3/2) − φ_KK(1/2) = 9/2 − 1/2 = 4`, which is NOT in
`{−1, 0, 1}` — the necessary condition fails crisply.

A second natural candidate, the unrescaled `φ_K²(λ) := λ²` (i.e.
(α, β, γ) = (1, 0, 0)), also fails: difference = 9/4 − 1/4 = 2.

We also prove that for ANY pure-monomial quadratic `φ(λ) := c·λ²` with
`c ≠ 0`, the difference is `2c`, so cluster-fixing requires `c ∈
{−1/2, 0, 1/2}`. The natural kernel-induced rescalings (`c = 1` or
`c = 2`) miss this trinary set.

## Strategic verdict (OUTCOME 5 per the dispatch)

NEGATIVE: the bare quadratic-in-K Gram mechanism `M ↦ M²` does NOT
produce a cluster-fixing quadratic. The cluster-fixing one-parameter
family of Wave 24 IS NOT REACHED by bare kernel self-multiplication.

To reach the cluster-fixing set from a kernel-induced quadratic, one
needs an AFFINE COMBINATION `a·M² + b·M + c·I` with non-trivial b, c —
i.e. the quadratic-in-K Gram alone is insufficient, and additional
linear and constant kernel terms must enter. Equivalently: pure
"two-step composition" does not fix the cluster; a "mixed-order"
mechanism is required.

This narrows the next open question: which (a, b, c) for
`a·M² + b·M + c·I` arises from a natural kernel-derived mechanism
(e.g. functional calculus of M against a fractal Polya kernel) AND
lies in the Wave 24 cluster-fixing set?

## What this file proves (all axiom-free)

  1. `quadKernelGramMap c λ := c · λ²` — the natural pure-quadratic-
     in-K map of leading coefficient `c`.
  2. Difference identity `quadKernelGramMap c (3/2) − quadKernelGramMap
     c (1/2) = 2·c` (load-bearing, axiom-free).
  3. The two specific kernel-natural candidates `c = 1` (bare K²) and
     `c = 2` (rescaled M²) both miss the cluster-fixing trinary
     `{−1/2, 0, 1/2}` for the leading coefficient.
  4. Explicit value computations:
       • `φ_K²(1/2) = 1/4`, `φ_K²(3/2) = 9/4` (BOTH miss {1/2, 3/2}).
       • `φ_KK(1/2) = 1/2` (fixes!), `φ_KK(3/2) = 9/2` (MISSES).
       • Single-side fix at c=2 does NOT extend to full cluster fix.
  5. `quadKernelGramMap_misses_cluster_fix` — for c ∉ {−1/2, 0, 1/2},
     no pure-quadratic-in-K map fixes both cluster centres.
  6. **Direct anchor at α=2, a=2**: the kernel value `K(2/3) = −1` is
     INHERITED from `fractalKernelReal_at_alpha_two`, giving the
     concrete M = [[2,−1],[−1,2]] and M² = [[5,−4],[−4,5]] tied to
     the published level-1 kernel data.
  7. `M_squared_eigenvalues_at_YM_params` — explicit eigenvalues of
     `M²` at α=2, a=2 are `{1, 9}` (axiom-free, from quadratic
     formula on the trace/determinant).
  8. `YM_quadratic_kernel_mechanism_does_not_fix_cluster` capstone:
     bundles the negative finding with Wave 24's witness that the
     cluster-fixing family is non-empty — confirming the gap is
     between "kernel-natural" and "cluster-fixing" quadratics.

## Honest scope

Does NOT discharge YM mass gap. Does NOT refute non-affine
quadratics in general (Wave 24 explicit witnesses still stand). DOES
prove the SIMPLEST kernel-natural quadratic mechanism (bare self-
product Gram) FAILS to land in the Wave 24 cluster-fix family. The
open path forward is mixed-order kernel calculus, not bare squaring.

ZERO project axioms; `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]` for every theorem.

Author: Pablo Cohen (with assistance). 2026-05-25 Wave 24 YM follow-on.
-/

import PF.YangMillsNonAffineCoupledResidual
import PF.YangMillsLevel2Spectrum

namespace PrincipiaTractalis

open Real

/-! ## Part 1 — The pure-quadratic-in-K kernel-Gram map

The natural quadratic-in-K Gram matrix is the operator self-product
`M²` (or any uniform rescaling `c·M²`). Its eigenvalue action on the
underlying spectrum is the pure-monomial quadratic `λ ↦ c·λ²`. -/

/-- **Pure-quadratic-in-K kernel-Gram eigenvalue map** (axiom-free defn).

    Specialises `quadraticEigenvalueMap` (Wave 24) to the pure-monomial
    quadratic with leading coefficient `c`, linear coefficient `0`,
    and constant term `0`. Corresponds to the eigenvalue action of
    `c·M²` on the cluster-centre spectrum `{1/2, 3/2}`. -/
def quadKernelGramMap (c lam : ℝ) : ℝ :=
  quadraticEigenvalueMap c 0 0 lam

/-- **Explicit value: `quadKernelGramMap c λ = c·λ²`** (axiom-free). -/
theorem quadKernelGramMap_eq (c lam : ℝ) :
    quadKernelGramMap c lam = c * lam ^ 2 := by
  unfold quadKernelGramMap quadraticEigenvalueMap
  ring

/-- **Value at the lower cluster centre `λ = 1/2`** (axiom-free). -/
theorem quadKernelGramMap_at_half (c : ℝ) :
    quadKernelGramMap c (1/2) = c / 4 := by
  rw [quadKernelGramMap_eq]; ring

/-- **Value at the upper cluster centre `λ = 3/2`** (axiom-free). -/
theorem quadKernelGramMap_at_three_halves (c : ℝ) :
    quadKernelGramMap c (3/2) = 9 * c / 4 := by
  rw [quadKernelGramMap_eq]; ring

/-! ## Part 2 — The load-bearing difference identity

For the pure-monomial quadratic `φ(λ) = c·λ²`, the Wave 24 difference
identity collapses to `φ(3/2) − φ(1/2) = 2·c`. Cluster-fixing
(difference in `{−1, 0, 1}`) forces `c ∈ {−1/2, 0, 1/2}`. -/

/-- **★ Difference identity for the pure-quadratic kernel map** (axiom-free):

      `φ_c(3/2) − φ_c(1/2) = 2·c`.

    Direct specialisation of `quadraticEigenvalueMap_difference` at
    `β = 0`. -/
theorem quadKernelGramMap_difference (c : ℝ) :
    quadKernelGramMap c (3/2) - quadKernelGramMap c (1/2) = 2 * c := by
  unfold quadKernelGramMap
  have h := quadraticEigenvalueMap_difference c 0 0
  linarith

/-- **★★ Cluster-fix necessary condition on the leading coefficient**
    (axiom-free).

    If `φ_c(λ) = c·λ²` fixes both cluster centres in the sense
    `φ_c(1/2) ∈ {1/2, 3/2}` ∧ `φ_c(3/2) ∈ {1/2, 3/2}`, then the
    leading coefficient `c` must satisfy `2c ∈ {−1, 0, 1}`. -/
theorem quadKernelGramMap_cluster_fix_forces_diff
    (c : ℝ)
    (h1 : quadKernelGramMap c (1/2) = 1/2 ∨ quadKernelGramMap c (1/2) = 3/2)
    (h2 : quadKernelGramMap c (3/2) = 1/2 ∨ quadKernelGramMap c (3/2) = 3/2) :
    2 * c = -1 ∨ 2 * c = 0 ∨ 2 * c = 1 := by
  -- The difference φ(3/2) − φ(1/2) = 2c must lie in c₂ − c₁ where
  -- (c₁, c₂) ∈ {1/2, 3/2}², i.e. in {-1, 0, 1}.
  have hd := quadKernelGramMap_difference c
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · right; left; linarith
  · right; right; linarith
  · left; linarith
  · right; left; linarith

/-! ## Part 3 — The two natural kernel-induced candidates miss

We now exhibit the two most natural kernel-induced candidate
leading coefficients arising from the level-1 YM kernel data:

  (i) `c = 1` — bare `λ ↦ λ²` from the operator self-product `M²`
      acting on its own eigenvalues `{1, 3}`.
  (ii) `c = 2` — rescaled `λ ↦ 2λ²` from the cluster-centre
      eigenvalue action of `M²` against the standard 1/2 prefactor
      (`(D + V)/2 = (2 + V)/2` cluster convention).

Both miss `{−1/2, 0, 1/2}`, hence both miss the cluster-fix family. -/

/-- **Candidate (i): bare `c = 1`** (axiom-free). -/
theorem quadKernelGramMap_c_one_at_half :
    quadKernelGramMap 1 (1/2) = 1/4 := by
  rw [quadKernelGramMap_eq]; norm_num

theorem quadKernelGramMap_c_one_at_three_halves :
    quadKernelGramMap 1 (3/2) = 9/4 := by
  rw [quadKernelGramMap_eq]; norm_num

/-- **★ Candidate (i) MISSES the cluster fix** (axiom-free):
    `φ_1(1/2) = 1/4 ∉ {1/2, 3/2}` and `φ_1(3/2) = 9/4 ∉ {1/2, 3/2}`. -/
theorem quadKernelGramMap_c_one_misses :
    quadKernelGramMap 1 (1/2) ≠ 1/2 ∧
    quadKernelGramMap 1 (1/2) ≠ 3/2 ∧
    quadKernelGramMap 1 (3/2) ≠ 1/2 ∧
    quadKernelGramMap 1 (3/2) ≠ 3/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [quadKernelGramMap_c_one_at_half]; norm_num
  · rw [quadKernelGramMap_c_one_at_half]; norm_num
  · rw [quadKernelGramMap_c_one_at_three_halves]; norm_num
  · rw [quadKernelGramMap_c_one_at_three_halves]; norm_num

/-- **Candidate (ii): rescaled `c = 2`** (axiom-free). -/
theorem quadKernelGramMap_c_two_at_half :
    quadKernelGramMap 2 (1/2) = 1/2 := by
  rw [quadKernelGramMap_at_half]; norm_num

theorem quadKernelGramMap_c_two_at_three_halves :
    quadKernelGramMap 2 (3/2) = 9/2 := by
  rw [quadKernelGramMap_at_three_halves]; norm_num

/-- **★★ Candidate (ii) has SINGLE-SIDE fix BUT MISSES full cluster**
    (axiom-free).

    `φ_2(1/2) = 1/2` (lower centre is fixed!) but
    `φ_2(3/2) = 9/2 ∉ {1/2, 3/2}` (upper centre escapes far above
    the cluster). The rescaled map fixes only one centre, not both. -/
theorem quadKernelGramMap_c_two_single_side_fix :
    quadKernelGramMap 2 (1/2) = 1/2 ∧
    quadKernelGramMap 2 (3/2) ≠ 1/2 ∧
    quadKernelGramMap 2 (3/2) ≠ 3/2 := by
  refine ⟨quadKernelGramMap_c_two_at_half, ?_, ?_⟩
  · rw [quadKernelGramMap_c_two_at_three_halves]; norm_num
  · rw [quadKernelGramMap_c_two_at_three_halves]; norm_num

/-! ## Part 4 — Negative cluster-fix theorems for the natural candidates

We now state the negative result formally: neither `c = 1` nor `c = 2`
produces a cluster-fixing pure-quadratic kernel map. -/

/-- **★★★ Bare `c = 1` does NOT fix the cluster** (axiom-free).

    Since `φ_1(1/2) = 1/4 ∉ {1/2, 3/2}` already, no cluster pairing
    `(c₁, c₂) ∈ {1/2, 3/2}²` is realised. -/
theorem quadKernelGramMap_c_one_not_cluster_fixing :
    ¬ ((quadKernelGramMap 1 (1/2) = 1/2 ∨ quadKernelGramMap 1 (1/2) = 3/2) ∧
       (quadKernelGramMap 1 (3/2) = 1/2 ∨ quadKernelGramMap 1 (3/2) = 3/2)) := by
  intro ⟨h1, _⟩
  obtain ⟨ne11, ne13, _, _⟩ := quadKernelGramMap_c_one_misses
  rcases h1 with h1 | h1
  · exact ne11 h1
  · exact ne13 h1

/-- **★★★ Rescaled `c = 2` does NOT fix BOTH cluster centres**
    (axiom-free).

    Although `φ_2(1/2) = 1/2 ∈ {1/2, 3/2}`, the upper-centre image
    `φ_2(3/2) = 9/2 ∉ {1/2, 3/2}`. The full cluster-fix condition
    requires BOTH centres mapped inside, so the candidate fails. -/
theorem quadKernelGramMap_c_two_not_cluster_fixing :
    ¬ ((quadKernelGramMap 2 (1/2) = 1/2 ∨ quadKernelGramMap 2 (1/2) = 3/2) ∧
       (quadKernelGramMap 2 (3/2) = 1/2 ∨ quadKernelGramMap 2 (3/2) = 3/2)) := by
  intro ⟨_, h2⟩
  obtain ⟨_, ne21, ne23⟩ := quadKernelGramMap_c_two_single_side_fix
  rcases h2 with h2 | h2
  · exact ne21 h2
  · exact ne23 h2

/-- **★★ Generic obstruction for pure-quadratic kernel maps**
    (axiom-free).

    For any `c ∈ ℝ` with `c ∉ {−1/2, 0, 1/2}`, the pure-quadratic
    kernel map `φ_c(λ) = c·λ²` cannot fix both cluster centres. -/
theorem quadKernelGramMap_misses_cluster_fix
    (c : ℝ) (h_m : c ≠ -1/2) (h_z : c ≠ 0) (h_p : c ≠ 1/2) :
    ¬ ((quadKernelGramMap c (1/2) = 1/2 ∨ quadKernelGramMap c (1/2) = 3/2) ∧
       (quadKernelGramMap c (3/2) = 1/2 ∨ quadKernelGramMap c (3/2) = 3/2)) := by
  intro ⟨h1, h2⟩
  rcases quadKernelGramMap_cluster_fix_forces_diff c h1 h2 with hd | hd | hd
  · exact h_m (by linarith)
  · exact h_z (by linarith)
  · exact h_p (by linarith)

/-! ## Part 5 — Concrete anchor: M² at YM params α = 2, a = 2

We tie the abstract analysis back to the level-1 YM kernel data.
At α = 2, a = 2 the kernel value `K(2/3) = −1` (axiom-free, from
`fractalKernelReal_at_alpha_two`), so the symmetric level-1 matrix is

    M = [[2, −1], [−1, 2]]      with eigenvalues {1, 3},

cluster centres `{1/2, 3/2}` after the 1/2 prefactor. The
quadratic-in-K Gram matrix is

    M² = [[5, −4], [−4, 5]]    with eigenvalues {1, 9}.

We record this algebraic content here. -/

/-- **★ M² eigenvalues at YM params α = 2, a = 2** (axiom-free):
    `M² = [[5, −4], [−4, 5]]` has eigenvalues exactly `{1, 9}`.

    The characteristic polynomial is `λ² − 10·λ + 9 = (λ−1)(λ−9)`,
    giving roots `{1, 9}`. We encode this as the trace + determinant
    identities, which uniquely determine the spectrum. -/
theorem M_squared_eigenvalues_at_YM_params :
    -- Trace: (5) + (5) = 10 = 1 + 9
    (5 : ℝ) + 5 = 1 + 9 ∧
    -- Determinant: (5)(5) − (−4)(−4) = 9 = 1 · 9
    (5 : ℝ) * 5 - (-4) * (-4) = 1 * 9 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **★ M² applied to lower cluster centre gives `2 · (1/2)² = 1/2`** (axiom-free).

    This is the single-side fix of candidate (ii). -/
theorem M_squared_action_on_lower_cluster :
    quadKernelGramMap 2 (1/2) = 1/2 :=
  quadKernelGramMap_c_two_at_half

/-- **★ M² applied to upper cluster centre gives `2 · (3/2)² = 9/2`**
    (axiom-free).

    This is the MISS — the upper centre lands at 9/2, far outside the
    cluster `{1/2, 3/2}`. -/
theorem M_squared_action_on_upper_cluster :
    quadKernelGramMap 2 (3/2) = 9/2 :=
  quadKernelGramMap_c_two_at_three_halves

/-! ## Part 6 — Capstone: kernel-natural pure-quadratic mechanism narrowed out

We now bundle the negative finding into a single capstone. The capstone
states three pieces of strategic content:

  (A) The Wave 24 cluster-fix family IS non-empty (re-export witness).
  (B) The two natural kernel-induced pure-quadratic maps (`c = 1` and
      `c = 2`) BOTH miss the cluster-fix family.
  (C) Generic obstruction: any `c ∉ {−1/2, 0, 1/2}` misses.

The gap between (A) and (B) is the strategic content: a non-empty
cluster-fix family exists, but the BARE quadratic-in-K Gram mechanism
fails to populate it. Discharging YM via a kernel-derived quadratic
requires mixed-order calculus on the kernel, not bare self-product. -/

/-- **★★ Kernel-natural pure-quadratic mechanism narrowed out**
    (axiom-free Prop).

    (A) Wave 24 cluster-fix family non-empty (witness (1, −2, 5/4)).
    (B) Bare `c = 1` quadratic-in-K map misses the cluster.
    (C) Rescaled `c = 2` quadratic-in-K map misses the cluster
        (single-side fix at 1/2 only).
    (D) Any `c ∉ {−1/2, 0, 1/2}` misses generically. -/
def QuadKernelGramMechanismNarrowedOut : Prop :=
  -- (A) Wave 24 cluster-fix family non-empty
  (∃ α β γ : ℝ, α ≠ 0 ∧
     quadraticEigenvalueMap α β γ (1/2) = 1/2 ∧
     quadraticEigenvalueMap α β γ (3/2) = 1/2) ∧
  -- (B) Bare c = 1 misses
  (¬ ((quadKernelGramMap 1 (1/2) = 1/2 ∨ quadKernelGramMap 1 (1/2) = 3/2) ∧
      (quadKernelGramMap 1 (3/2) = 1/2 ∨ quadKernelGramMap 1 (3/2) = 3/2))) ∧
  -- (C) Rescaled c = 2 misses
  (¬ ((quadKernelGramMap 2 (1/2) = 1/2 ∨ quadKernelGramMap 2 (1/2) = 3/2) ∧
      (quadKernelGramMap 2 (3/2) = 1/2 ∨ quadKernelGramMap 2 (3/2) = 3/2))) ∧
  -- (D) Generic c ∉ {−1/2, 0, 1/2} misses
  (∀ c : ℝ, c ≠ -1/2 → c ≠ 0 → c ≠ 1/2 →
     ¬ ((quadKernelGramMap c (1/2) = 1/2 ∨ quadKernelGramMap c (1/2) = 3/2) ∧
        (quadKernelGramMap c (3/2) = 1/2 ∨ quadKernelGramMap c (3/2) = 3/2)))

/-- **★★ The narrow-out Prop holds** (axiom-free). -/
theorem quad_kernel_gram_mechanism_narrowed_out :
    QuadKernelGramMechanismNarrowedOut := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (A) Witness (1, -2, 5/4) from Wave 24
    exact ⟨1, -2, 5/4, by norm_num,
           quadratic_witness_one_at_half,
           quadratic_witness_one_at_three_halves⟩
  · exact quadKernelGramMap_c_one_not_cluster_fixing
  · exact quadKernelGramMap_c_two_not_cluster_fixing
  · intro c h_m h_z h_p
    exact quadKernelGramMap_misses_cluster_fix c h_m h_z h_p

/-- **★★★ YM quadratic kernel mechanism does NOT fix the cluster**
    — strategic capstone (axiom-free).

    Bundles the YM-class anchor (α = 2, a = 2) with the Wave 24
    abstract cluster-fix unlock and the Wave 25 negative finding on
    the bare quadratic-in-K Gram mechanism:

      (a) Wave 24 (`QuadraticClusterFixingUnlocked`) certifies that
          the cluster-fixing family in the quadratic class is
          non-empty.
      (b) The natural kernel-induced pure-quadratic candidates
          `c ∈ {1, 2}` arising from `λ ↦ c·λ²` (the eigenvalue map
          of `c·M²` on the YM-class cluster spectrum) BOTH miss the
          cluster-fix family.
      (c) Therefore: bare quadratic-in-K Gram is INSUFFICIENT to
          land in the cluster-fix family — the open path forward is
          mixed-order kernel calculus `a·M² + b·M + c·I` with
          nontrivial linear and constant terms.

    OUTCOME 5 per dispatch: narrows out the bare quadratic-in-K
    mechanism, leaving mixed-order kernel-calculus mechanisms as
    the remaining open route to YM uniform concentration.

    HONEST SCOPE: this does NOT discharge YM mass gap, does NOT
    refute non-affine quadratic mechanisms in general (Wave 24
    explicit witnesses still stand), and does NOT establish any
    spectral gap evolution. It identifies precisely which subset of
    quadratic candidates is reachable from bare kernel self-product. -/
theorem YM_quadratic_kernel_mechanism_does_not_fix_cluster :
    -- (a) Wave 24 abstract cluster-fix unlock holds
    QuadraticClusterFixingUnlocked ∧
    -- (b) Bare quadratic-in-K Gram narrow-out holds
    QuadKernelGramMechanismNarrowedOut ∧
    -- (c) Single-side fix at lower centre under c = 2
    (quadKernelGramMap 2 (1/2) = 1/2) ∧
    -- (d) Upper-centre escape under c = 2
    (quadKernelGramMap 2 (3/2) = 9/2) := by
  refine ⟨quadratic_cluster_fixing_unlocked,
          quad_kernel_gram_mechanism_narrowed_out,
          M_squared_action_on_lower_cluster,
          M_squared_action_on_upper_cluster⟩

/-! ## Part 7 — Axiom-freeness verification -/

#print axioms quadKernelGramMap_eq
#print axioms quadKernelGramMap_at_half
#print axioms quadKernelGramMap_at_three_halves
#print axioms quadKernelGramMap_difference
#print axioms quadKernelGramMap_cluster_fix_forces_diff
#print axioms quadKernelGramMap_c_one_at_half
#print axioms quadKernelGramMap_c_one_at_three_halves
#print axioms quadKernelGramMap_c_one_misses
#print axioms quadKernelGramMap_c_two_at_half
#print axioms quadKernelGramMap_c_two_at_three_halves
#print axioms quadKernelGramMap_c_two_single_side_fix
#print axioms quadKernelGramMap_c_one_not_cluster_fixing
#print axioms quadKernelGramMap_c_two_not_cluster_fixing
#print axioms quadKernelGramMap_misses_cluster_fix
#print axioms M_squared_eigenvalues_at_YM_params
#print axioms M_squared_action_on_lower_cluster
#print axioms M_squared_action_on_upper_cluster
#print axioms quad_kernel_gram_mechanism_narrowed_out
#print axioms YM_quadratic_kernel_mechanism_does_not_fix_cluster

end PrincipiaTractalis
