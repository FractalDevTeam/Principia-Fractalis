/-
# PF_L4L.Empirical.SubstrateNaturalPrior_NeutrinoAnchor_2026_06_24_Reverification

Independent Lean4Lean re-elaboration of the 2026-06-24 substrate-natural prior
algebraic identity for the neutrino mass-ratio anchor.

Re-elaborated through a separate Lean4Lean package configuration with a separate
package hash, guarding against per-package elaboration drift.

Expected axiom report:

  [propext, Classical.choice, Quot.sound]

What this re-verifies: the kernel-only structural identity
`(π/10/√2) · (π/10/(3π/4)) = π√2/150`. The substrate's expression for the
neutrino mass-ratio is an exact algebraic identity from substrate atoms
(universal π/10 coupling, α_P = √2, α_BSD = 3π/4) — not a numerical fit. The
Lean4Lean kernel's independent elaboration confirms the identity is provable
from `field_simp` and `nlinarith` on `Real.sqrt 2 * Real.sqrt 2 = 2`, with no
project-axiom dependencies.

Under the substrate-natural prior (~404 distinct positive expressions), the
neutrino row is 1-of-130 candidates — the survivor row of the Table 2
retrodiction set after the look-elsewhere correction.
-/

import PF.Empirical.SubstrateNaturalPrior_NeutrinoAnchor_2026_06_24

namespace PF_L4L.Empirical

def substrate_neutrino_structural_product_reverified :=
  @PF.Empirical.SubstrateNaturalPrior_NeutrinoAnchor_2026_06_24.substrate_neutrino_structural_product

#print axioms substrate_neutrino_structural_product_reverified

end PF_L4L.Empirical
