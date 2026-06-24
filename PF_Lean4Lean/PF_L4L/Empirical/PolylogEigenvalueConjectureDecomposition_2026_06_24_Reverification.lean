/-
# PF_L4L.Empirical.PolylogEigenvalueConjectureDecomposition_2026_06_24_Reverification

Independent Lean4Lean re-elaboration of the 2026-06-24 typed decomposition of
`PolylogEigenvalueConjecture` into five named kernel-only sub-claims.

Re-elaborated through a separate Lean4Lean package configuration with a separate
package hash, guarding against per-package elaboration drift.

Expected axiom report for each:

  [propext, Classical.choice, Quot.sound]

Sub-claims 1--4 are substrate-internal open Props (encoded with no project axioms;
their content is the algebraic statement). Sub-claim 5 (distinctness α_P ≠ α_NP)
is kernel-only proven on the assumption of `PolylogEigenvalueConjecture` itself.
The `polylog_eigenvalue_conjunction_iff_parts` bridge theorem and the
`polylog_eigenvalue_implies_distinctness` theorem are both kernel-only.
-/

import PF.PolylogEigenvalueConjectureDecomposition_2026_06_24

namespace PF_L4L.Empirical

def PolylogEigenvalueConjecture_P_UniquenessEqn_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.PolylogEigenvalueConjecture_P_UniquenessEqn

#print axioms PolylogEigenvalueConjecture_P_UniquenessEqn_reverified

def PolylogEigenvalueConjecture_P_Positivity_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.PolylogEigenvalueConjecture_P_Positivity

#print axioms PolylogEigenvalueConjecture_P_Positivity_reverified

def PolylogEigenvalueConjecture_NP_UniquenessEqn_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.PolylogEigenvalueConjecture_NP_UniquenessEqn

#print axioms PolylogEigenvalueConjecture_NP_UniquenessEqn_reverified

def PolylogEigenvalueConjecture_NP_Positivity_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.PolylogEigenvalueConjecture_NP_Positivity

#print axioms PolylogEigenvalueConjecture_NP_Positivity_reverified

def PolylogEigenvalueConjecture_Distinctness_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.PolylogEigenvalueConjecture_Distinctness

#print axioms PolylogEigenvalueConjecture_Distinctness_reverified

def polylog_eigenvalue_conjunction_iff_parts_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.polylog_eigenvalue_conjunction_iff_parts

#print axioms polylog_eigenvalue_conjunction_iff_parts_reverified

def polylog_eigenvalue_implies_distinctness_reverified :=
  @PrincipiaTractalis.PolylogEigenvalueConjectureDecomposition.polylog_eigenvalue_implies_distinctness

#print axioms polylog_eigenvalue_implies_distinctness_reverified

end PF_L4L.Empirical
