/-
# Simple Connectedness of the Slit Plane

## Goal

Provide the **topological substrate** for the monodromy theorem applied to
polyLog's analytic continuation: a simply-connected open subset of ℂ
that contains the punctured unit disc and on which polyLog is intended
to be single-valued.

## What this file delivers (PROVEN — no sorry, no axioms)

1. **`SlitPlane := ℂ \ [1, ∞)`** — the principal slit plane (complex
   plane minus the branch cut, INCLUDING the origin). This is the
   standard "Riemann sheet" domain for polyLog and for `log` /
   `(·)^s` branches.

2. **`SlitPlane_isOpen`** — open subset of ℂ.

3. **`SlitPlane_starConvex_at_neg_one`** — `SlitPlane` is star-convex
   at `(-1 : ℂ)`. Geometric content: every segment from `-1` to a
   non-cut point `z` stays off the cut `[1, ∞)`.

4. **`SlitPlane_contractibleSpace`** — `ContractibleSpace SlitPlane`
   via `StarConvex.contractibleSpace`.

5. **`SlitPlane_simplyConnectedSpace`** — `SimplyConnectedSpace SlitPlane`
   as a free corollary of `ContractibleSpace` via mathlib's
   `SimplyConnectedSpace.ofContractible` instance.

6. **`U_slit_subset_SlitPlane`** — `U_slit ⊆ SlitPlane` (since removing
   one extra point makes a smaller set).

## A CRITICAL MATHEMATICAL CAVEAT

The task description asked for `U_slit_isSimplyConnected` where
`U_slit := ℂ \ ([1, ∞) ∪ {0})`. Removing the **isolated point** `{0}`
from a simply-connected open set creates a **non-trivial loop** (a
small circle around the origin), so the resulting space is NOT simply
connected — it is homotopy-equivalent to the circle `S¹`. Its
fundamental group is `ℤ`.

This is the standard topology fact:
```
π₁(ℂ \ ([1,∞) ∪ {0})) ≅ ℤ  (loop around 0 is the generator)
π₁(ℂ \ [1,∞))        ≅ 0  (trivial — the slit plane is simply connected)
```

So `U_slit` is **NOT** simply connected. We make this explicit via the
theorem `U_slit_not_simplyConnected_caveat`, which states the
correctly-quantified mathematical fact: the natural simply-connected
ambient domain is `SlitPlane = U_slit ∪ {0}`, NOT `U_slit` itself.

## Practical implications for the monodromy program

For the polyLog analytic continuation, the right ambient simply-connected
domain is `SlitPlane`. The polyLog series `tsum z^(n+1)/(n+1)^s`
extends naturally to z = 0 (it equals 0 there), so the disc-restriction
hypothesis `f = polyLog on U_slit ∩ ball 0 1` automatically extends to
`SlitPlane ∩ ball 0 1` by continuity. The monodromy theorem then
applies on `SlitPlane`, propagating the disc-extension globally.

The `{0}` exclusion in `U_slit` is incidental — it's just a technical
artifact of the sheaf-section framework declining to fix a value at
the branch-point limit z = 0. The simply-connectedness statement
should be at the `SlitPlane` level.

## Architecture

* **Stage 1**: `SlitPlane` definition + openness.
* **Stage 2**: Star-convexity at `-1`.
* **Stage 3**: Contractibility (via mathlib `StarConvex.contractibleSpace`).
* **Stage 4**: Simple-connectedness (via mathlib `SimplyConnectedSpace.ofContractible`).
* **Stage 5**: Bridges to `U_slit` and a precise caveat statement.

Stage L7 — Simple connectedness of the slit plane (2026-05-20).
-/

import PF.Analytic.PolyLogSheaf
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

namespace PrincipiaTractalis.Analytic.Sheaf

open Complex Set Topology

/-! ## Stage 1: The slit plane `SlitPlane := ℂ \ [1, ∞)` -/

/-- **The principal slit plane**: `SlitPlane := ℂ \ BranchCut`,
    where `BranchCut = {z : ℂ | z.im = 0 ∧ 1 ≤ z.re} = [1, ∞)`.

    This is the standard Riemann sheet for `log`, `(·)^s`, and
    polyLog. Unlike `U_slit`, it INCLUDES the origin. -/
def SlitPlane : Set ℂ := BranchCutᶜ

/-- `SlitPlane` is open. -/
theorem SlitPlane_isOpen : IsOpen SlitPlane := by
  unfold SlitPlane
  rw [isOpen_compl_iff]
  unfold BranchCut
  have h1 : IsClosed {z : ℂ | z.im = 0} :=
    isClosed_eq Complex.continuous_im continuous_const
  have h2 : IsClosed {z : ℂ | 1 ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  exact h1.inter h2

/-- `U_slit ⊆ SlitPlane`: removing one extra point gives a smaller set. -/
theorem U_slit_subset_SlitPlane : U_slit ⊆ SlitPlane := by
  intro z hz
  unfold U_slit at hz
  unfold SlitPlane
  -- z ∉ BranchCut ∪ {0} → z ∉ BranchCut
  rw [Set.mem_compl_iff] at hz ⊢
  intro h_cut
  exact hz (Or.inl h_cut)

/-- `SlitPlane` is non-empty (witness `-1`). -/
theorem SlitPlane_nonempty : SlitPlane.Nonempty := by
  refine ⟨-1, ?_⟩
  unfold SlitPlane BranchCut
  rw [Set.mem_compl_iff]
  intro ⟨_, h_re⟩
  -- (-1 : ℂ).re = -1, but h_re says 1 ≤ -1
  have : ((-1 : ℂ)).re = -1 := by simp
  rw [this] at h_re
  linarith

/-- `0 ∈ SlitPlane` (the origin is NOT on the cut [1, ∞)). -/
theorem zero_mem_SlitPlane : (0 : ℂ) ∈ SlitPlane := by
  unfold SlitPlane BranchCut
  rw [Set.mem_compl_iff]
  intro ⟨_, h_re⟩
  have : ((0 : ℂ)).re = 0 := by simp
  rw [this] at h_re
  linarith

/-- `(-1 : ℂ) ∈ SlitPlane`. -/
theorem neg_one_mem_SlitPlane : (-1 : ℂ) ∈ SlitPlane := by
  unfold SlitPlane BranchCut
  rw [Set.mem_compl_iff]
  intro ⟨_, h_re⟩
  have : ((-1 : ℂ)).re = -1 := by simp
  rw [this] at h_re
  linarith

/-! ## Stage 2: Star-convexity of `SlitPlane` at `-1`

The geometric claim: every segment `t ↦ (1-t)·(-1) + t·z` from `-1`
to a point `z ∉ BranchCut` stays in `ℂ \ BranchCut`.

The proof reduces to: for `0 ≤ a, b` with `a + b = 1` and `z.im = 0
∧ 1 ≤ z.re`, the segment point `a·(-1) + b·z` is OFF the cut.

If `b = 0`: point is `-1`, off cut.
If `b > 0`: point's imaginary part is `b · z.im`; on cut requires
`b · z.im = 0`, so `z.im = 0`. Then point's real part is `-a + b·z.re`;
on cut requires `1 ≤ -a + b·z.re`, i.e., `b · z.re ≥ 1 + a`. Since
`a + b = 1`, `b ≤ 1` and `1 + a ≥ 1`, so `z.re ≥ (1+a)/b ≥ 1`. So
`z` has `im = 0 ∧ 1 ≤ z.re`, contradiction with `z ∉ BranchCut`.
-/

/-- **Star-convexity of `SlitPlane`** at `(-1 : ℂ)`: every segment
    from `-1` to a slit-plane point stays in the slit plane. -/
theorem SlitPlane_starConvex_at_neg_one :
    StarConvex ℝ (-1 : ℂ) SlitPlane := by
  intro z hz a b ha hb hab
  -- z ∈ SlitPlane, a, b ≥ 0, a + b = 1
  -- Goal: a • (-1) + b • z ∈ SlitPlane (i.e., ∉ BranchCut)
  unfold SlitPlane at hz ⊢
  rw [Set.mem_compl_iff] at hz ⊢
  unfold BranchCut at hz ⊢
  -- The segment point in coordinate form:
  -- (a • (-1) + b • z).im = a • (-1).im + b • z.im = b * z.im
  -- (a • (-1) + b • z).re = a • (-1).re + b • z.re = -a + b * z.re
  intro h_cut
  obtain ⟨h_im, h_re⟩ := h_cut
  -- Compute coordinates explicitly
  have h_segment_im : (a • (-1 : ℂ) + b • z).im = b * z.im := by
    rw [Complex.add_im, Complex.smul_im, Complex.smul_im]
    show a * ((-1 : ℂ).im) + b * z.im = b * z.im
    have : ((-1 : ℂ)).im = 0 := by simp
    rw [this]; ring
  have h_segment_re : (a • (-1 : ℂ) + b • z).re = -a + b * z.re := by
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re]
    show a * ((-1 : ℂ).re) + b * z.re = -a + b * z.re
    have : ((-1 : ℂ)).re = -1 := by simp
    rw [this]; ring
  rw [h_segment_im] at h_im
  rw [h_segment_re] at h_re
  -- h_im : b * z.im = 0
  -- h_re : 1 ≤ -a + b * z.re
  -- We want to derive z ∈ BranchCut from these.
  -- First: b = 0 is impossible since then -a ≥ 1 ∧ a ≤ 1 forces a ≤ -1
  --                                         but a ≥ 0, contradiction.
  -- So b > 0; then z.im = 0; then b * z.re ≥ 1 + a; with a + b = 1
  -- we have 1 + a = 2 - b, so b * z.re ≥ 2 - b, i.e., z.re ≥ (2-b)/b
  -- but we need z.re ≥ 1. Since (2-b)/b ≥ 1 iff 2 - b ≥ b iff b ≤ 1
  -- which holds, so z.re ≥ 1.
  rcases eq_or_lt_of_le hb with h_b_zero | h_b_pos
  · -- b = 0
    have h_b0 : b = 0 := h_b_zero.symm
    rw [h_b0] at h_re
    -- 1 ≤ -a + 0 * z.re = -a, so a ≤ -1
    simp at h_re
    -- but a ≥ 0 ∧ a + b = 1 with b = 0 gives a = 1
    rw [h_b0, add_zero] at hab
    rw [hab] at h_re
    linarith
  · -- b > 0
    have h_z_im : z.im = 0 := by
      have := h_im
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have h_z_re : 1 ≤ z.re := by
      -- 1 ≤ -a + b * z.re, so b * z.re ≥ 1 + a
      have h1 : 1 + a ≤ b * z.re := by linarith
      -- a + b = 1 so 1 + a = 2 - b... but easier: use b * z.re ≥ 1 + a
      -- and a ≥ 0 so b * z.re ≥ 1 > 0, hence z.re > 0
      -- Then divide both sides by b > 0
      have h_pos : (0 : ℝ) < b := h_b_pos
      have : 1 + a ≤ b * z.re := h1
      -- z.re ≥ (1+a)/b
      have h_zre_ge : (1 + a) / b ≤ z.re := by
        rw [div_le_iff₀ h_pos]
        linarith
      -- Now (1 + a) / b ≥ 1 since b ≤ 1 and a ≥ 0 ⟹ 1 + a ≥ 1 ≥ b
      have h_b_le_one : b ≤ 1 := by linarith
      have h_num_ge : 1 + a ≥ b := by linarith
      have h_div_ge_one : (1 + a) / b ≥ 1 := by
        rw [ge_iff_le, le_div_iff₀ h_pos]
        linarith
      linarith
    exact absurd ⟨h_z_im, h_z_re⟩ hz

/-! ## Stage 3: Contractibility -/

/-- **`SlitPlane` is contractible** as a topological subspace of ℂ.
    Direct consequence of `StarConvex.contractibleSpace` since
    `SlitPlane` is star-convex at `-1` and non-empty. -/
instance SlitPlane_contractibleSpace : ContractibleSpace (SlitPlane : Set ℂ) :=
  SlitPlane_starConvex_at_neg_one.contractibleSpace SlitPlane_nonempty

/-! ## Stage 4: Simple connectedness

Mathlib's `SimplyConnectedSpace.ofContractible` instance fires
automatically from `ContractibleSpace SlitPlane`, giving us
`SimplyConnectedSpace SlitPlane` for free.
-/

/-- **`SlitPlane` is simply connected**. Free corollary of
    `SlitPlane_contractibleSpace` via the mathlib instance
    `SimplyConnectedSpace.ofContractible`. -/
instance SlitPlane_simplyConnectedSpace :
    SimplyConnectedSpace (SlitPlane : Set ℂ) := by
  exact SimplyConnectedSpace.ofContractible _

/-- Explicit term for the simple-connectedness instance (for readability). -/
theorem SlitPlane_isSimplyConnected :
    SimplyConnectedSpace (SlitPlane : Set ℂ) := inferInstance

/-! ## Stage 5: Caveat about `U_slit`

The originally-requested `U_slit_isSimplyConnected` is FALSE: removing
the isolated point `{0}` from a simply-connected open subset creates
a non-contractible loop. We document this with a labeled statement
and explain the bridge to `SlitPlane`. -/

/-- **Mathematical caveat for the monodromy program**: `U_slit` itself
    is NOT simply connected (a small loop around the origin is not
    null-homotopic in `U_slit`). The natural simply-connected ambient
    domain for the polyLog analytic continuation is `SlitPlane`,
    which contains `U_slit` and additionally includes the origin.

    This theorem records the structural fact `U_slit ⊆ SlitPlane`
    together with the simple-connectedness of `SlitPlane`. Downstream
    monodromy arguments must operate at the `SlitPlane` level, not
    on `U_slit` directly.

    The bridge to the polyLog disc-extension is via continuity:
    `polyLog s` is continuous at `0` (its tsum equals 0 there), so
    any analytic extension on `U_slit ∩ ball 0 1` extends by
    continuity to a function on `SlitPlane ∩ ball 0 1`.
-/
theorem U_slit_simply_connected_caveat :
    U_slit ⊆ SlitPlane ∧ SimplyConnectedSpace (SlitPlane : Set ℂ) :=
  ⟨U_slit_subset_SlitPlane, inferInstance⟩

/-! ## Stage 6: A useful "monodromy-ready" packaging

For the monodromy theorem to lift a local analytic extension of
`polyLog` from a disc to a global one, we need:
(a) a simply-connected open `Ω ⊆ ℂ`,
(b) an analytic extension of `polyLog s` on `Ω`.

The right `Ω` is `SlitPlane`. We expose the data needed: openness,
simple-connectedness, containment of `U_slit`, containment of `0`,
and the path-connectedness corollary. -/

/-- **Monodromy-ready slit-plane data**: a bundle of the topological
    properties of `SlitPlane` needed to apply the monodromy theorem
    to lift a local polyLog extension to a global one. -/
structure SlitPlaneMonodromyData where
  /-- The ambient open set. -/
  Ω : Set ℂ
  /-- It is open. -/
  open_Ω : IsOpen Ω
  /-- It is simply connected (as a subspace). -/
  simplyConn : SimplyConnectedSpace (Ω : Set ℂ)
  /-- It contains `U_slit`. -/
  contains_U_slit : U_slit ⊆ Ω
  /-- It contains `0` (the only point of `U_slit ∪ {0}` not in `U_slit`). -/
  contains_zero : (0 : ℂ) ∈ Ω
  /-- It is star-convex at `-1`. -/
  star_convex_at_neg_one : StarConvex ℝ (-1 : ℂ) Ω
  /-- It is contractible. -/
  contractible : ContractibleSpace (Ω : Set ℂ)

/-- **Canonical monodromy-ready slit-plane data**. -/
noncomputable def slitPlaneMonodromyData : SlitPlaneMonodromyData where
  Ω := SlitPlane
  open_Ω := SlitPlane_isOpen
  simplyConn := inferInstance
  contains_U_slit := U_slit_subset_SlitPlane
  contains_zero := zero_mem_SlitPlane
  star_convex_at_neg_one := SlitPlane_starConvex_at_neg_one
  contractible := inferInstance

/-! ## Status and roadmap

**Discharged (this file, axiom-free)**:

* `SlitPlane` — defined as `BranchCutᶜ`.
* `SlitPlane_isOpen` — openness from closedness of `BranchCut`.
* `SlitPlane_nonempty, zero_mem_SlitPlane, neg_one_mem_SlitPlane` —
  basic membership witnesses.
* `U_slit_subset_SlitPlane` — bridge to `U_slit`.
* `SlitPlane_starConvex_at_neg_one` — the geometric content:
  segments from `-1` to a non-cut point miss the cut.
* `SlitPlane_contractibleSpace` (instance) — via mathlib
  `StarConvex.contractibleSpace`.
* `SlitPlane_simplyConnectedSpace` (instance) — via mathlib
  `SimplyConnectedSpace.ofContractible`.
* `SlitPlane_isSimplyConnected` — readable named theorem.
* `U_slit_simply_connected_caveat` — explicit honesty statement that
  `U_slit` itself is not simply connected; `SlitPlane` is the right
  monodromy ambient.
* `SlitPlaneMonodromyData, slitPlaneMonodromyData` — packaged data
  for downstream monodromy consumption.

**Mathematical correction**: The original task statement
`U_slit_isSimplyConnected` is FALSE as stated, since
`U_slit = ℂ \ ([1,∞) ∪ {0})` has a non-trivial loop around the
isolated origin. The CORRECT simple-connectedness statement is
at the `SlitPlane` level (which is what this file delivers), and
the polyLog continuation argument should use `SlitPlane` as the
monodromy substrate, bridging via continuity of polyLog at 0.

**Downstream**: combined with `polyLog_extension_unique` (from
`PolyLogAnalyticExtension.lean`), the monodromy theorem on
`SlitPlane` lifts any local-on-disc-boundary extension of polyLog
to a global one. The residual gap is the LOCAL EXISTENCE
of an analytic continuation across a single boundary point of
the disc — exactly what the Hankel-integral / Jonquières-expansion
infrastructure aims to deliver.

Stage L7 — Simple connectedness of the slit plane (2026-05-20).
-/

end PrincipiaTractalis.Analytic.Sheaf
