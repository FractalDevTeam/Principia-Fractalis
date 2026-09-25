/-
# PF.Analytic.RiemannXiBox0Panels.Seg02Audit

Axiom audit for OPT-40-TIGHT Stage-2 segment 2 (r331b rework).

Uses `#print axioms` on every load-bearing theorem: the new tight Re
lower-bound node certificates, per-panel chunks, raw segment sums, midpoint
scaling, and the four segment-2 integral endpoints.

Expected only: `[propext, Classical.choice, Quot.sound]` for every check.
No project axioms.  No `sorry`.  No `native_decide`.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiBox0Panels.Seg02

open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P1
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P2
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P3
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P4
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P5
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02P6
open PrincipiaTractalis.RiemannXiBox0Panels.Seg02
open PrincipiaTractalis.Box0Seg02M

-- ★★ Selected node theorems (canary sample across panels) ★★
#print axioms node_0_bounds
#print axioms node_4_bounds
#print axioms node_8_bounds
#print axioms node_12_bounds
#print axioms node_16_bounds

-- ★★ All six production chunk theorems ★★
#print axioms seg2_p1_chunk_bounds
#print axioms seg2_p2_chunk_bounds
#print axioms seg2_p3_chunk_bounds
#print axioms seg2_p4_chunk_bounds
#print axioms seg2_p5_chunk_bounds
#print axioms seg2_p6_chunk_bounds

-- ★★ Raw segment sum bounds ★★
#print axioms seg2_re_midpoint_sum_eq_raw
#print axioms seg2_im_midpoint_sum_eq_raw
#print axioms seg2_re_midpoint_sum_lower
#print axioms seg2_re_midpoint_sum_upper
#print axioms seg2_im_midpoint_sum_lower
#print axioms seg2_im_midpoint_sum_upper

-- ★★ M certificate ★★
#print axioms box0_seg2_M_le_MHI

-- ★★★★ FOUR SEGMENT-2 INTEGRAL THEOREMS ★★★★
#print axioms box0_seg2_re_integral_lower
#print axioms box0_seg2_re_integral_upper
#print axioms box0_seg2_im_integral_lower
#print axioms box0_seg2_im_integral_upper
