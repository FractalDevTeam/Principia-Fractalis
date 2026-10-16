import PF.SpectralGap
import PF.TuringEncoding.AlphaRealizationNoGo
import PF.PNP_FrameworkMillenniumAnswer

/-! Axiom audit for the P-vs-NP spectral-gap claim. -/

open PrincipiaTractalis

-- 1. The spectral-gap layer: what is its axiom set, and what does it SAY?
#print axioms PrincipiaTractalis.spectral_gap_positive
#print axioms PrincipiaTractalis.P_neq_NP
#print axioms PrincipiaTractalis.pvsnp_spectral_separation

-- 2. The TYPE of the theorem named `P_neq_NP` -- does it mention any
--    complexity object at all?
#check @PrincipiaTractalis.P_neq_NP
#check @PrincipiaTractalis.pvsnp_spectral_separation

-- 3. The definitions behind lambda_0_P / lambda_0_NP: constants or spectra?
#print PrincipiaTractalis.lambda_0_P
#print PrincipiaTractalis.lambda_0_NP

-- 4. The no-go: its statement and axiom set.
#check @PrincipiaTractalis.TuringEncoding.alpha_realization_canonical_pair_iff_classes_distinct
#print axioms
  PrincipiaTractalis.TuringEncoding.alpha_realization_canonical_pair_iff_classes_distinct

-- 5. Is alpha_of_class opaque (i.e. no definitional content)?
#print PrincipiaTractalis.TuringEncoding.alpha_of_class
