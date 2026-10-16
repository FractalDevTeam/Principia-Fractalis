/-
# FinalDemo_t14p5 — conditional end-to-end wiring check for Re ξ(1+(29/2)i) < 0

NOT the unconditional result.  This file proves ONLY the last link of the chain:
that the P6 reduction (`re_xi_14p5_neg_of_edge_lb`) composed with REALISTIC
certified lower bounds on `Re Λ₀(1+(29/2)i)` and `Im Λ₀(1+(29/2)i)` discharges the
rational margin by `norm_num` and yields `Re ξ(1+(29/2)i) < 0`.

The two hypotheses `h_reA`, `h_imA` are exactly what the 40-segment midpoint panels
+ `box0_envelope_le` + `re/im_Lambda0_close_to_truncated_integral` must PRODUCE
(as `box14p5_re_enclosure` / `box14p5_im_enclosure`).  They are the whole remaining
gap; everything downstream of them is proved here, kernel-clean.

Margin that closes (exact rationals):
  (29/2)^2 = 841/4,  841/4 · 47357/10⁷ = 39827237/4·10⁷ = 0.995680925
  (29/2)   · 3/10⁴   = 87/20000        = 0.00435
  sum = 1.000030925 > 1         ⇒ Re ξ = (1 - sum')/2 < 0.
(True values ≈ Re Λ₀ 4.739e-3, so 47357/10⁷ is a safe lower bound widening the Re
margin to ~3.3e-6 against the ~2.0e-6 quadrature budget; the Im lower bound 3/10⁴
is a placeholder for what the Im panels certify.)

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RightEdgeSignsPilot_t14p5

set_option autoImplicit false

namespace PrincipiaTractalis
namespace RightEdgeSignsPilot14p5

open Complex
open PrincipiaTractalis.RiemannXiEntire

/-- CONDITIONAL on the two certified Λ₀ lower bounds (the panel-produced
enclosure endpoints), `Re ξ(1+(29/2)i) < 0`.  The `norm_num` discharges the
rational margin, so the only unproved inputs are `h_reA`, `h_imA`. -/
theorem re_xi_14p5_neg_demo
    (h_reA : (47357 / 10000000 : ℝ) ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).re)
    (h_imA : (3 / 10000 : ℝ) ≤ (completedRiemannZeta₀ (⟨1, 29 / 2⟩ : ℂ)).im) :
    (riemannXiEntire (⟨1, 29 / 2⟩ : ℂ)).re < 0 :=
  re_xi_14p5_neg_of_edge_lb h_reA h_imA (by norm_num)

#print axioms re_xi_14p5_neg_demo

end RightEdgeSignsPilot14p5
end PrincipiaTractalis
