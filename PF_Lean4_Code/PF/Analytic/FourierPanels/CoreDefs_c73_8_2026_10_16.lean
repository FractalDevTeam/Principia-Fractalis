/-
# PF.Analytic.FourierPanels.CoreDefs_c73_8_2026_10_16

**M1 of the pointwise panel pack for `Re ξ(1 + (73/8)i) > 0`.**

Defines the two Fourier node functions used in the certified panel
enclosure of `Re Λ₀(1 + (73/8)i)` and `Im Λ₀(1 + (73/8)i)`:

  nodeR_fourier_plus_at_c73_8  u = (F_plus u + F_minus u) · cos((73/16)·u)
  nodeR_fourier_minus_at_c73_8 u = (F_plus u − F_minus u) · sin((73/16)·u)

together with their `Interval` mirrors
`nodeI_fourier_plus_at_c73_8` and `nodeI_fourier_minus_at_c73_8`, which use
the **N = 3 truncation** of `omega(exp u)`:

  omega_N3(exp u) := exp(-π·exp u) + exp(-4π·exp u) + exp(-9π·exp u).

For `u ≥ 0` we have `exp u ≥ 1`, so `omega(exp u) ≥ omega_N3(exp u)` with
nonneg tail (each tail term `exp(-π·k²·exp u) > 0`). The full tail-bound
reconciliation is deferred to M2 — in this file we prove the structural
conservativity against the N = 3 real counterparts
`nodeR_fourier_plus_at_c73_8_N3` / `nodeR_fourier_minus_at_c73_8_N3`, which
is what the per-panel bricks will directly enclose. The relationship
`nodeR_fourier_plus_at_c73_8 u = nodeR_fourier_plus_at_c73_8_N3 u + (full tail)`
is left as a stated lemma body for M2.

This file is self-contained: `omega_N3_at_exp` is re-defined inside the
`FourierPanels_c73_8` namespace so the module does **not** depend on
`CoreDefs_c6_2026_10_15`, `CoreDefs_c49_8_2026_10_16`, or
`CoreDefs_c25_4_2026_10_16`.

Three-axiom bar: every declaration below prints exactly
`[propext, Classical.choice, Quot.sound]`. No sorry, no native_decide, no
`interval` tactic, no project axioms.

Emitted by codex/gen_box.py for c = 73/8 (2026-10-20). `c` enters the node
functions only through the phase cos((c/2)u) / sin((c/2)u), and every add-on
majorant discards it via |cos|,|sin| <= 1, so the three add-on constants are
c-independent: residue 7/10^7, analytic tail 12/10^8, omega-gap 1/10^21.

SPDX-License-Identifier: Apache-2.0
Authors: Pablo Cohen + Claude Opus 4.7 (1M context). 2026-10-16.
-/

import PF.Analytic.OmegaDerivative_2026_10_14
import Interval.Interval.Conversion
import Interval.Interval.Exp
import Interval.Interval.Log
import Interval.Interval.Sincos
import Interval.Interval.Pi
import Interval.Interval.Order
import Interval.Tactic.Approx

set_option autoImplicit false

namespace PrincipiaTractalis
namespace FourierPanels_c73_8

open Real
open PrincipiaTractalis.OmegaDerivative20261014
open scoped Real

/-! ## §1 — Real node functions (full `F_plus` / `F_minus`) -/

/-- Real-part Fourier node integrand at `c = 73/8` (full `omega`). -/
noncomputable def nodeR_fourier_plus_at_c73_8 (u : ℝ) : ℝ :=
  (F_plus u + F_minus u) * Real.cos ((4.5625 : ℝ) * u)

/-- Imaginary-part Fourier node integrand at `c = 73/8` (full `omega`). -/
noncomputable def nodeR_fourier_minus_at_c73_8 (u : ℝ) : ℝ :=
  (F_plus u - F_minus u) * Real.sin ((4.5625 : ℝ) * u)

/-! ## §2 — N = 3 truncated real counterparts

These are the real functions the `Interval` mirrors conservatively enclose.
Each one replaces `omega(exp u) = ∑' n, exp(-π · (n+1)² · exp u)` by its
truncation to `n ∈ {0, 1, 2}`:

  omega_N3(exp u) = exp(-π · exp u) + exp(-4π · exp u) + exp(-9π · exp u).

On `u ≥ 0`, `omega(exp u) ≥ omega_N3(exp u) > 0` (each tail term positive). -/

/-- The N = 3 truncation of `omega(exp u)` as a real number. -/
noncomputable def omega_N3_at_exp (u : ℝ) : ℝ :=
  Real.exp (-(π * Real.exp u))
    + Real.exp (-(4 * π * Real.exp u))
    + Real.exp (-(9 * π * Real.exp u))

/-- Real-part Fourier node, N = 3 truncation of omega. This is the function
    the per-panel `Interval` brick directly encloses. -/
noncomputable def nodeR_fourier_plus_at_c73_8_N3 (u : ℝ) : ℝ :=
  (Real.exp (u * (0.5 : ℝ)) * omega_N3_at_exp u + omega_N3_at_exp u)
    * Real.cos ((4.5625 : ℝ) * u)

/-- Imaginary-part Fourier node, N = 3 truncation of omega. -/
noncomputable def nodeR_fourier_minus_at_c73_8_N3 (u : ℝ) : ℝ :=
  (Real.exp (u * (0.5 : ℝ)) * omega_N3_at_exp u - omega_N3_at_exp u)
    * Real.sin ((4.5625 : ℝ) * u)

/-! ## §3 — Interval mirrors -/

/-- Interval mirror of `nodeR_fourier_plus_at_c73_8_N3`. The `let`-bindings are
    load-bearing (r120 pattern: shared subterms let the kernel's `whnf`
    cache find structural equalities when the panel brick's `decide +kernel`
    unfolds). -/
def nodeI_fourier_plus_at_c73_8 (u : _root_.Interval) : _root_.Interval :=
  let x := _root_.Interval.exp u
  let omega_approx :=
    _root_.Interval.exp (-(_root_.Interval.pi * x))
      + _root_.Interval.exp (-(4 * _root_.Interval.pi * x))
      + _root_.Interval.exp (-(9 * _root_.Interval.pi * x))
  let F_plus_approx := _root_.Interval.exp (u * (0.5 : _root_.Interval)) * omega_approx
  let F_minus_approx := omega_approx
  (F_plus_approx + F_minus_approx) * _root_.Interval.cos ((4.5625 : _root_.Interval) * u)

/-- Interval mirror of `nodeR_fourier_minus_at_c73_8_N3`. -/
def nodeI_fourier_minus_at_c73_8 (u : _root_.Interval) : _root_.Interval :=
  let x := _root_.Interval.exp u
  let omega_approx :=
    _root_.Interval.exp (-(_root_.Interval.pi * x))
      + _root_.Interval.exp (-(4 * _root_.Interval.pi * x))
      + _root_.Interval.exp (-(9 * _root_.Interval.pi * x))
  let F_plus_approx := _root_.Interval.exp (u * (0.5 : _root_.Interval)) * omega_approx
  let F_minus_approx := omega_approx
  (F_plus_approx - F_minus_approx) * _root_.Interval.sin ((4.5625 : _root_.Interval) * u)

/-! ## §4 — Conservativity of the Interval mirrors (against the N = 3 real
    counterparts). -/

/-- The real `omega_N3_at_exp` is enclosed by the Interval `omega_approx`
    sub-expression. -/
theorem omega_N3_at_exp_mem_approx {u : ℝ} {U : _root_.Interval} (hu : u ∈ approx U) :
    omega_N3_at_exp u ∈ approx
      (_root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.exp U))
        + _root_.Interval.exp (-(4 * _root_.Interval.pi * _root_.Interval.exp U))
        + _root_.Interval.exp (-(9 * _root_.Interval.pi * _root_.Interval.exp U))) := by
  unfold omega_N3_at_exp
  approx

/-- Conservativity of `nodeI_fourier_plus_at_c73_8` against
    `nodeR_fourier_plus_at_c73_8_N3`. -/
theorem nodeR_fourier_plus_at_c73_8_N3_mem_approx {u : ℝ} {U : _root_.Interval}
    (hu : u ∈ approx U) :
    nodeR_fourier_plus_at_c73_8_N3 u ∈ approx (nodeI_fourier_plus_at_c73_8 U) := by
  show nodeR_fourier_plus_at_c73_8_N3 u ∈ approx
    ((_root_.Interval.exp (U * (0.5 : _root_.Interval))
        * (_root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.exp U))
            + _root_.Interval.exp (-(4 * _root_.Interval.pi * _root_.Interval.exp U))
            + _root_.Interval.exp (-(9 * _root_.Interval.pi * _root_.Interval.exp U)))
      + (_root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.exp U))
          + _root_.Interval.exp (-(4 * _root_.Interval.pi * _root_.Interval.exp U))
          + _root_.Interval.exp (-(9 * _root_.Interval.pi * _root_.Interval.exp U))))
      * _root_.Interval.cos ((4.5625 : _root_.Interval) * U))
  unfold nodeR_fourier_plus_at_c73_8_N3 omega_N3_at_exp
  approx

/-- Conservativity of `nodeI_fourier_minus_at_c73_8` against
    `nodeR_fourier_minus_at_c73_8_N3`. -/
theorem nodeR_fourier_minus_at_c73_8_N3_mem_approx {u : ℝ} {U : _root_.Interval}
    (hu : u ∈ approx U) :
    nodeR_fourier_minus_at_c73_8_N3 u ∈ approx (nodeI_fourier_minus_at_c73_8 U) := by
  show nodeR_fourier_minus_at_c73_8_N3 u ∈ approx
    ((_root_.Interval.exp (U * (0.5 : _root_.Interval))
        * (_root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.exp U))
            + _root_.Interval.exp (-(4 * _root_.Interval.pi * _root_.Interval.exp U))
            + _root_.Interval.exp (-(9 * _root_.Interval.pi * _root_.Interval.exp U)))
      - (_root_.Interval.exp (-(_root_.Interval.pi * _root_.Interval.exp U))
          + _root_.Interval.exp (-(4 * _root_.Interval.pi * _root_.Interval.exp U))
          + _root_.Interval.exp (-(9 * _root_.Interval.pi * _root_.Interval.exp U))))
      * _root_.Interval.sin ((4.5625 : _root_.Interval) * U))
  unfold nodeR_fourier_minus_at_c73_8_N3 omega_N3_at_exp
  approx

/-! ## §Axiom check -/

#print axioms nodeR_fourier_plus_at_c73_8
#print axioms nodeR_fourier_minus_at_c73_8
#print axioms omega_N3_at_exp
#print axioms nodeR_fourier_plus_at_c73_8_N3
#print axioms nodeR_fourier_minus_at_c73_8_N3
#print axioms nodeI_fourier_plus_at_c73_8
#print axioms nodeI_fourier_minus_at_c73_8
#print axioms omega_N3_at_exp_mem_approx
#print axioms nodeR_fourier_plus_at_c73_8_N3_mem_approx
#print axioms nodeR_fourier_minus_at_c73_8_N3_mem_approx

end FourierPanels_c73_8
end PrincipiaTractalis
