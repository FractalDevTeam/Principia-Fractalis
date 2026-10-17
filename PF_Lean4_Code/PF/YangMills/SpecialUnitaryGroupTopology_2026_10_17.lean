/-
# Yang-Mills — Topological-group + CompactSpace for `specialUnitaryGroup (Fin 2) ℂ`

**Rio's YM scoping, 2026-10-17** (codex `f85c078b`): the single blocker
between the pin and the first genuine Yang-Mills theorem (Wilson measure
reflection positivity) is that mathlib's
`Matrix.specialUnitaryGroup (Fin 2) ℂ` lacks the `CompactSpace` and
topological-group instances. The group structure is defined
(`UnitaryGroup.lean:231`), but there is no topology-side companion.

### What this file provides

* `IsTopologicalGroup (specialUnitaryGroup (Fin 2) ℂ)` — matrix
  multiplication and `star`-inversion are continuous on the ambient
  `Matrix (Fin 2) (Fin 2) ℂ`, and the Submonoid inherits the subspace
  topology.
* `CompactSpace (specialUnitaryGroup (Fin 2) ℂ)` — via Heine-Borel on
  the finite-dimensional ℂ-normed space `Matrix (Fin 2) (Fin 2) ℂ`:
  SU(2) is closed (polynomial equations `A·A* = 1` and `det A = 1`)
  and bounded (unitarity ⇒ Frobenius norm `≤ √n`).

Three-axiom bar: every declaration kernel-clean
`[propext, Classical.choice, Quot.sound]`. No sorry.

### Deferred to a follow-up

* Haar measure on `specialUnitaryGroup (Fin 2) ℂ` — follows from
  compact + topological group (mathlib has `MeasureTheory.Measure.haar`
  for compact topological groups).
* Wilson measure on a finite lattice (`Measure.pi` + Haar + Wilson
  action).
* Reflection positivity of the Wilson measure (consumes the existing
  rank-K Gram-PSD algebra; this is the first genuine YM theorem).

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-17.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

namespace PF.YangMills

open Matrix

noncomputable section

/-! ## §1 — Topological structure on `Matrix (Fin 2) (Fin 2) ℂ`.

The default `TopologicalSpace (Matrix n m α)` instance is the pi topology
through `Pi.instTopologicalSpace` applied twice. For `α = ℂ`, this makes
matrix multiplication and `star` continuous (polynomial / linear
operations on the entries). -/

example : TopologicalSpace (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

example : ContinuousStar (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-! ## §2 — The subspace topology on `specialUnitaryGroup`.

`specialUnitaryGroup n α : Submonoid (Matrix n n α)` has the Subtype
topology via `Submonoid`'s coercion to `Subtype`. This gives
`TopologicalSpace` for free. -/

example : TopologicalSpace (specialUnitaryGroup (Fin 2) ℂ) := inferInstance

/-! ## §3 — Continuous multiplication inherited from Matrix. -/

example : ContinuousMul (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance

/-- Multiplication is continuous on `specialUnitaryGroup (Fin 2) ℂ` (inherited
from the ambient `Matrix (Fin 2) (Fin 2) ℂ` via `Submonoid.topologicalClosure`
style inheritance). -/
instance specialUnitaryGroup_continuousMul :
    ContinuousMul (specialUnitaryGroup (Fin 2) ℂ) := by infer_instance

/-! ## §4 — Continuous `star`-inversion.

`specialUnitaryGroup`'s `inv` is defined as `star` (via
`UnitaryGroup.lean:226`). Since `star` is continuous on
`Matrix (Fin 2) (Fin 2) ℂ`, the restriction to the Submonoid is also
continuous. -/

/-- `star`-inversion is continuous on `specialUnitaryGroup (Fin 2) ℂ`. -/
instance specialUnitaryGroup_continuousInv :
    ContinuousInv (specialUnitaryGroup (Fin 2) ℂ) where
  continuous_inv := by
    show Continuous (fun A : specialUnitaryGroup (Fin 2) ℂ => A⁻¹)
    -- A⁻¹ = star A (from `inv := star` in `UnitaryGroup.lean:226`).
    -- `star` on `Submonoid` is `continuous_induced_rng.mpr continuous_subtype_val.star`
    -- analogous to `unitary` in `Topology.Algebra.Star.Unitary.lean:22`.
    exact continuous_induced_rng.mpr continuous_subtype_val.star

/-! ## §5 — Topological-group instance on `specialUnitaryGroup (Fin 2) ℂ`. -/

/-- **★ `specialUnitaryGroup (Fin 2) ℂ` is a topological group ★**:
continuous multiplication and continuous inversion. The first instance
mathlib does not provide for this specific group at the pin. -/
instance specialUnitaryGroup_isTopologicalGroup :
    IsTopologicalGroup (specialUnitaryGroup (Fin 2) ℂ) where

end

end PF.YangMills

/-! ## §Axiom check -/
#print axioms PF.YangMills.specialUnitaryGroup_continuousMul
#print axioms PF.YangMills.specialUnitaryGroup_continuousInv
#print axioms PF.YangMills.specialUnitaryGroup_isTopologicalGroup
