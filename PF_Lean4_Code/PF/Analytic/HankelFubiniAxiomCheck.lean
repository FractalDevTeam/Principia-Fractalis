/-
# Axiom Audit — HankelFubini

Verifies that the Fubini deliverable depends only on standard mathlib
axioms (no project-level axioms used).
-/

import PF.Analytic.HankelFubini

namespace PrincipiaTractalis.Analytic.HankelFubini

-- These #print axioms commands run at elaboration time and emit
-- the axiom dependency list of each theorem in the build trace.
#print axioms tsum_integral_eq_integral_tsum
#print axioms integrand_integrable_per_term
#print axioms summable_integral_norm
#print axioms capstone

end PrincipiaTractalis.Analytic.HankelFubini
