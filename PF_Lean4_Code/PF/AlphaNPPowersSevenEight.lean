/-
# PF.AlphaNPPowersSevenEight

★ 2026-06-17 — Extend the α_NP power tower with closed forms for
α_NP^7 and α_NP^8 in `ℚ + ℚ·α_Hodge` form, following the established
pattern (α_NP^2 through α_NP^6 already in `CrossMillenniumMoreInvariants`).

## Closed forms

  (A) `α_NP^7 = (145403/4096)·α_Hodge + 359441/16384`
      Numerically α_NP^7 ≈ 79.36.

  (B) `α_NP^8 = (135807/2048)·α_Hodge + 2685889/65536`
      Numerically α_NP^8 ≈ 148.27.

Each closed form is verified by ring-level computation against the
golden ratio relation α_Hodge² = α_Hodge + 1 + the existing α_NP^k
closed forms.

## Numerical brackets

  * α_NP^7 ∈ (79, 80)
  * α_NP^8 ∈ (148, 149)

Both brackets verifiable axiom-free via `norm_num` + the closed forms.

ZERO project axioms. Kernel-only `[propext, Classical.choice, Quot.sound]`.
-/

import PF.CrossMillenniumSharedInvariants
import PF.CrossMillenniumMoreInvariants
import PF.TuringEncoding.AlphaCanonical

namespace PrincipiaTractalis
namespace AlphaNPPowersSevenEight

open Real
open PrincipiaTractalis.CrossMillenniumSharedInvariants
open PrincipiaTractalis.CrossMillenniumMoreInvariants
open PrincipiaTractalis.TuringEncoding

/-! ## §1 — α_NP^7 -/

/-- **`α_NP^7 = (145403/4096)·α_Hodge + 359441/16384`** — extends the
    α_NP power tower from α_NP^6.

    Derivation: α_NP^7 = α_NP · α_NP^6 = (α_Hodge + 1/4) ·
    ((9729/512)·α_Hodge + 48113/4096); expand using
    α_Hodge² = α_Hodge + 1; collect. -/
theorem α_NP_seventh :
    α_NP ^ 7 = (145403/4096) * α_Hodge + 359441/16384 := by
  have h_split : α_NP ^ 7 = α_NP ^ 3 * α_NP ^ 4 := by ring
  rw [h_split, α_NP_cubed, α_NP_fourth]
  ring_nf
  have h := phi_sq_eq
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := by unfold α_Hodge; exact h
  nlinarith [h_Hodge]

/-- **α_NP^7 numerical bracket**: `α_NP^7 ∈ (79, 80)`. -/
theorem α_NP_seventh_bracket :
    (79 : ℝ) < α_NP ^ 7 ∧ α_NP ^ 7 < (80 : ℝ) := by
  rw [α_NP_seventh]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by nlinarith [h_phi_lb], by nlinarith [h_phi_ub]⟩

/-! ## §2 — α_NP^8 -/

/-- **`α_NP^8 = (135807/2048)·α_Hodge + 2685889/65536`** — extends the
    α_NP power tower to the 8th power.

    Derivation: α_NP^8 = α_NP · α_NP^7 = (α_Hodge + 1/4) ·
    ((145403/4096)·α_Hodge + 359441/16384); expand; collect. -/
theorem α_NP_eighth :
    α_NP ^ 8 = (135807/2048) * α_Hodge + 2685889/65536 := by
  have h_split : α_NP ^ 8 = α_NP ^ 4 * α_NP ^ 4 := by ring
  rw [h_split, α_NP_fourth]
  ring_nf
  have h := phi_sq_eq
  have h_Hodge : α_Hodge ^ 2 = α_Hodge + 1 := by unfold α_Hodge; exact h
  nlinarith [h_Hodge]

/-- **α_NP^8 numerical bracket**: `α_NP^8 ∈ (148, 149)`. -/
theorem α_NP_eighth_bracket :
    (148 : ℝ) < α_NP ^ 8 ∧ α_NP ^ 8 < (149 : ℝ) := by
  rw [α_NP_eighth]
  have h_phi_lb : (1.6180339887 : ℝ) ≤ α_Hodge := by
    unfold α_Hodge; exact phi_in_interval_10digit.1
  have h_phi_ub : α_Hodge ≤ (1.6180339888 : ℝ) := by
    unfold α_Hodge; exact phi_in_interval_10digit.2
  exact ⟨by nlinarith [h_phi_lb], by nlinarith [h_phi_ub]⟩

/-! ## §3 — α_NP power-tower extension capstone -/

/-- **★ α_NP power tower extended to 8th power ★** — bundles
    α_NP^7 and α_NP^8 closed forms plus brackets. -/
theorem α_NP_power_tower_extended_to_eighth :
    α_NP ^ 7 = (145403/4096) * α_Hodge + 359441/16384 ∧
    α_NP ^ 8 = (135807/2048) * α_Hodge + 2685889/65536 ∧
    ((79 : ℝ) < α_NP ^ 7 ∧ α_NP ^ 7 < (80 : ℝ)) ∧
    ((148 : ℝ) < α_NP ^ 8 ∧ α_NP ^ 8 < (149 : ℝ)) :=
  ⟨α_NP_seventh,
   α_NP_eighth,
   α_NP_seventh_bracket,
   α_NP_eighth_bracket⟩

end AlphaNPPowersSevenEight
end PrincipiaTractalis

-- Axiom checks. Expected: `[propext, Classical.choice, Quot.sound]`.
#print axioms PrincipiaTractalis.AlphaNPPowersSevenEight.α_NP_seventh
#print axioms PrincipiaTractalis.AlphaNPPowersSevenEight.α_NP_eighth
#print axioms
  PrincipiaTractalis.AlphaNPPowersSevenEight.α_NP_power_tower_extended_to_eighth
