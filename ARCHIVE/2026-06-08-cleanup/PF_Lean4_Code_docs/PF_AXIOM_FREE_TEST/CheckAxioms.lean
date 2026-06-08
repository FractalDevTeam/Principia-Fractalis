-- Test file to check for axioms in the AXIOM_FREE modules
-- This will be modified to import each module and check axioms

import PF.TuringEncoding.Operators
import PF.P_NP_Complete_Proof
import PF.SpectralEmbedding

-- Check axioms in key theorems from the standard versions
#print axioms PrincipiaTractalis.TuringEncoding.P_neq_NP_from_spectral_gap
#print axioms PrincipiaTractalis.P_NEQ_NP
#print axioms PrincipiaTractalis.spectral_embedding_masses
