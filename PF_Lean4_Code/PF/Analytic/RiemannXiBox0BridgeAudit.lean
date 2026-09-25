/-
# PF.Analytic.RiemannXiBox0BridgeAudit

Axiom audit for the complete r331b Box-0 closure chain: envelope majorant,
integrability, the 39+39 adjacent-interval joins (sampled), the four cumulative
finite bounds, the `Ioc` rewrites, the Λ₀ bounds after one application of the
§8 envelope, the exact rational margins, both enclosures, and the
unconditional top-edge theorem.

Expected only: `[propext, Classical.choice, Quot.sound]` for every check.
No project axioms.  No `sorry`.  No `native_decide`.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiBox0Bridge

open PrincipiaTractalis.RiemannXiBox0Envelope
open PrincipiaTractalis.RiemannXiBox0Bridge

-- ★★ §8 envelope majorant chain ★★
#print axioms exp_neg_pi_le
#print axioms one_sub_exp_neg_pi_ge
#print axioms one_sub_exp_neg_pi_pos
#print axioms exp_neg_five_pi_le
#print axioms exp_neg_sixteen_pi_le
#print axioms two_div_pi_le
#print axioms box0_envelope_le

-- ★★ integrability ★★
#print axioms re_integrable
#print axioms im_integrable

-- ★★ joins (canary sample: first, middle, last) ★★
#print axioms re_join_1
#print axioms re_join_20
#print axioms re_join_39
#print axioms im_join_1
#print axioms im_join_20
#print axioms im_join_39

-- ★★ cumulative finite bounds over [1,5] ★★
#print axioms finite_re_lower
#print axioms finite_re_upper
#print axioms finite_im_lower
#print axioms finite_im_upper

-- ★★ intervalIntegral → Ioc 1 5 ★★
#print axioms re_interval_eq_Ioc
#print axioms im_interval_eq_Ioc

-- ★★ Λ₀ bounds (§8 envelope applied exactly once) ★★
#print axioms re_Lambda0_lower
#print axioms re_Lambda0_upper
#print axioms im_Lambda0_lower
#print axioms im_Lambda0_upper

-- ★★ exact rational margins ★★
#print axioms RE_MARGIN_pos
#print axioms IM_LO_MARGIN_pos
#print axioms IM_HI_MARGIN_pos

-- ★★ enclosures ★★
#print axioms box0_re_enclosure
#print axioms box0_im_enclosure

-- ★★★★ BOX 0 CLOSED ★★★★
#print axioms top15_box0_re_lt_neg_1e4
