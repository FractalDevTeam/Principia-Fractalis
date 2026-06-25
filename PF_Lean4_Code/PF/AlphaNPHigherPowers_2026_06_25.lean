/-
# PF.AlphaNPHigherPowers_2026_06_25

★★★★★★★★ 2026-06-25 — NEW algebraic identities: higher powers of α_NP
expressed in the (α_Hodge, 1) basis, plus the structural recurrence.

## Context

The substrate's α_NP value equals `α_Hodge + 1/4 = φ + 1/4`. Since
`α_Hodge² = α_Hodge + 1` (golden-ratio recurrence), the powers of α_NP
all live in the rank-2 ℚ-module `ℚ·α_Hodge ⊕ ℚ·1`. Each power has a
closed form

  α_NP^k = a_k · α_Hodge + b_k

with `a_k, b_k ∈ ℚ`. The corpus already proves the k=2 case
(`α_NP_sq` in `PF.CrossMillenniumMoreInvariants` — Appendix B's M2 of
the clean paper):

  α_NP² = (3/2) · α_Hodge + 17/16,  i.e.  (a_2, b_2) = (3/2, 17/16).

## What this file adds

  ✓ **α_NP³**: explicit closed form

      α_NP³ = (47/16) · α_Hodge + 113/64

  ✓ **α_NP⁴**: explicit closed form

      α_NP⁴ = (87/16) · α_Hodge + 865/256

  ✓ The **structural recurrence**

      a_{k+1} = (5/4) · a_k + b_k,    b_{k+1} = a_k + (1/4) · b_k

    derived directly from `α_NP = α_Hodge + 1/4` and the Fibonacci
    relation `α_Hodge² = α_Hodge + 1`.

  ✓ **Substrate signature**: the 2×2 recurrence matrix is

      M = ⎡ 5/4   1   ⎤
          ⎣ 1    1/4 ⎦

    with characteristic polynomial `det(M − λI) = λ² − (3/2)λ − 11/16`.
    Multiplying by 16 gives `16λ² − 24λ − 11 = 0` — the NP polylog
    quadratic itself. The roots are α_NP and its Galois conjugate
    `(3 − 2√5)/4`. The recurrence underlying the α_NP power expansion
    has the substrate's NP-class polylog quadratic as its
    characteristic polynomial; the substrate's algebraic signature is
    intrinsic to the power-expansion recurrence.

## Why this is non-trivial

Neither identity (α_NP³ nor α_NP⁴) is currently in the corpus. The
substrate's full power-expansion of α_NP is a new algebraic structure
made visible here. Each closed form follows from the k=2 identity by
direct algebra; the recurrence is the structural witness that the
NP-polylog quadratic `16x² − 24x − 11 = 0` is intrinsic to the
substrate's α_NP power expansion, not a separate axiom.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumMoreInvariants
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis.AlphaNPHigherPowers

open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — The k = 3 closed form

`α_NP³ = (47/16) · α_Hodge + 113/64`.

Derivation. With `α_Hodge² = α_Hodge + 1` and the k=2 identity
`α_NP² = (3/2)·α_Hodge + 17/16` (M2):

  α_NP³ = α_NP² · α_NP
        = ((3/2)·α_Hodge + 17/16) · (α_Hodge + 1/4)
        = (3/2)·α_Hodge² + (3/8)·α_Hodge + (17/16)·α_Hodge + 17/64
        = (3/2)·(α_Hodge + 1) + (3/8 + 17/16)·α_Hodge + 17/64
        = (3/2)·α_Hodge + 3/2 + (23/16)·α_Hodge + 17/64
        = (47/16)·α_Hodge + 113/64.
-/

/-- **α_NP³ in the (α_Hodge, 1) basis**:

    α_NP³ = (47/16) · α_Hodge + 113/64. -/
theorem α_NP_cubed :
    α_NP ^ 3 = (47 / 16) * α_Hodge + 113 / 64 := by
  have h_sq : α_NP ^ 2 = (3 / 2) * α_Hodge + 17 / 16 := α_NP_sq
  have h_NP : α_NP = α_Hodge + 1 / 4 := by
    unfold α_NP α_Hodge phi; ring
  have h_Hodge_sq : α_Hodge ^ 2 = α_Hodge + 1 := by
    unfold α_Hodge; exact phi_sq_eq
  calc α_NP ^ 3
      = α_NP ^ 2 * α_NP := by ring
    _ = ((3 / 2) * α_Hodge + 17 / 16) * (α_Hodge + 1 / 4) := by rw [h_sq, h_NP]
    _ = (3 / 2) * α_Hodge ^ 2 + (3 / 8) * α_Hodge
        + (17 / 16) * α_Hodge + 17 / 64 := by ring
    _ = (3 / 2) * (α_Hodge + 1) + (3 / 8) * α_Hodge
        + (17 / 16) * α_Hodge + 17 / 64 := by rw [h_Hodge_sq]
    _ = (47 / 16) * α_Hodge + 113 / 64 := by ring

/-! ## §2 — The k = 4 closed form

`α_NP⁴ = (87/16) · α_Hodge + 865/256`.

Derivation (using the same Fibonacci substitution):

  α_NP⁴ = α_NP³ · α_NP
        = ((47/16)·α_Hodge + 113/64) · (α_Hodge + 1/4)
        = (47/16)·α_Hodge² + (47/64)·α_Hodge + (113/64)·α_Hodge + 113/256
        = (47/16)·(α_Hodge + 1) + (160/64)·α_Hodge + 113/256
        = (47/16)·α_Hodge + 47/16 + (5/2)·α_Hodge + 113/256
        = (87/16)·α_Hodge + 865/256.
-/

/-- **α_NP⁴ in the (α_Hodge, 1) basis**:

    α_NP⁴ = (87/16) · α_Hodge + 865/256. -/
theorem α_NP_fourth :
    α_NP ^ 4 = (87 / 16) * α_Hodge + 865 / 256 := by
  have h_cubed : α_NP ^ 3 = (47 / 16) * α_Hodge + 113 / 64 := α_NP_cubed
  have h_NP : α_NP = α_Hodge + 1 / 4 := by
    unfold α_NP α_Hodge phi; ring
  have h_Hodge_sq : α_Hodge ^ 2 = α_Hodge + 1 := by
    unfold α_Hodge; exact phi_sq_eq
  calc α_NP ^ 4
      = α_NP ^ 3 * α_NP := by ring
    _ = ((47 / 16) * α_Hodge + 113 / 64) * (α_Hodge + 1 / 4) := by rw [h_cubed, h_NP]
    _ = (47 / 16) * α_Hodge ^ 2 + (47 / 64) * α_Hodge
        + (113 / 64) * α_Hodge + 113 / 256 := by ring
    _ = (47 / 16) * (α_Hodge + 1) + (47 / 64) * α_Hodge
        + (113 / 64) * α_Hodge + 113 / 256 := by rw [h_Hodge_sq]
    _ = (87 / 16) * α_Hodge + 865 / 256 := by ring

/-! ## §3 — The structural recurrence

The substrate's α_NP power expansion satisfies the recurrence

  a_{k+1} = (5/4)·a_k + b_k,    b_{k+1} = a_k + (1/4)·b_k.

The recurrence's 2×2 transition matrix has characteristic polynomial

  λ² − (3/2)λ − 11/16 = 0,  equivalently  16λ² − 24λ − 11 = 0,

which is the substrate's NP polylog quadratic. The eigenvalues are
α_NP and its Galois conjugate `(3 − 2√5)/4`. The substrate's NP
algebraic signature is intrinsic to the power-expansion recurrence,
not an additional axiom.

The lemma below is the concrete statement: from any closed form
`α_NP^k = a·α_Hodge + b`, the next closed form
`α_NP^(k+1) = a'·α_Hodge + b'` is given by `a' = (5/4)a + b` and
`b' = a + b/4`.
-/

/-- **Substrate recurrence step**: if `α_NP^k = a · α_Hodge + b`, then
    `α_NP^(k+1) = ((5/4)·a + b) · α_Hodge + (a + b/4)`.

    Substrate signature: the 2×2 matrix `M = ⎡5/4, 1; 1, 1/4⎤` has
    characteristic polynomial `λ² − (3/2)λ − 11/16 = 0`, i.e.\
    `16λ² − 24λ − 11 = 0` — the NP polylog quadratic. -/
theorem α_NP_power_recurrence (k : ℕ) (a b : ℝ)
    (h : α_NP ^ k = a * α_Hodge + b) :
    α_NP ^ (k + 1) = ((5 / 4) * a + b) * α_Hodge + (a + b / 4) := by
  have h_NP : α_NP = α_Hodge + 1 / 4 := by
    unfold α_NP α_Hodge phi; ring
  have h_Hodge_sq : α_Hodge ^ 2 = α_Hodge + 1 := by
    unfold α_Hodge; exact phi_sq_eq
  calc α_NP ^ (k + 1)
      = α_NP ^ k * α_NP := by ring
    _ = (a * α_Hodge + b) * (α_Hodge + 1 / 4) := by rw [h, h_NP]
    _ = a * α_Hodge ^ 2 + (a / 4) * α_Hodge + b * α_Hodge + b / 4 := by ring
    _ = a * (α_Hodge + 1) + (a / 4) * α_Hodge + b * α_Hodge + b / 4 := by
        rw [h_Hodge_sq]
    _ = ((5 / 4) * a + b) * α_Hodge + (a + b / 4) := by ring

end PrincipiaTractalis.AlphaNPHigherPowers

-- ★ Axiom check ★
#print axioms PrincipiaTractalis.AlphaNPHigherPowers.α_NP_cubed
#print axioms PrincipiaTractalis.AlphaNPHigherPowers.α_NP_fourth
#print axioms PrincipiaTractalis.AlphaNPHigherPowers.α_NP_power_recurrence
