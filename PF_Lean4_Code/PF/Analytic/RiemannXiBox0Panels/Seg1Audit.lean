/-
# PF.Analytic.RiemannXiBox0Panels.Seg1Audit

Axiom audit for Stage-1 assembly.  Uses `#print axioms` on every
load-bearing theorem: per-panel chunks, raw segment sums, M certificate,
midpoint scaling, and the four Stage-1 integral endpoints.

Expected only: `[propext, Classical.choice, Quot.sound]` for every check.
No project axioms.  No `sorry`.  No `native_decide`.

SPDX-License-Identifier: Apache-2.0
-/

import PF.Analytic.RiemannXiBox0Panels.Seg1

open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P1
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P2
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P3
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P4
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P5
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P6
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P7
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1P8
open PrincipiaTractalis.RiemannXiBox0Panels.Seg1
open PrincipiaTractalis.Box0Seg1MPrototype

-- ★★ Selected node theorems (canary sample: boundary + neg-sin transition) ★★
#print axioms node_3_bounds
#print axioms node_6_bounds
#print axioms node_7_bounds
#print axioms node_8_bounds
#print axioms node_22_bounds

-- ★★ All eight production chunk theorems ★★
#print axioms seg1_p1_chunk_bounds
#print axioms seg1_p2_chunk_bounds
#print axioms seg1_p3_chunk_bounds
#print axioms seg1_p4_chunk_bounds
#print axioms seg1_p5_chunk_bounds
#print axioms seg1_p6_chunk_bounds
#print axioms seg1_p7_chunk_bounds
#print axioms seg1_p8_chunk_bounds

-- ★★ Raw segment sum bounds (§1) ★★
#print axioms seg1_re_sum_lower
#print axioms seg1_re_sum_upper
#print axioms seg1_im_sum_lower
#print axioms seg1_im_sum_upper

-- ★★ Midpoint-form equality and bounds (§3, §4) ★★
#print axioms seg1_re_midpoint_sum_eq_raw
#print axioms seg1_im_midpoint_sum_eq_raw
#print axioms seg1_re_midpoint_sum_lower
#print axioms seg1_re_midpoint_sum_upper
#print axioms seg1_im_midpoint_sum_lower
#print axioms seg1_im_midpoint_sum_upper

-- ★★ M certificate (§9) ★★
#print axioms box0_seg1_M_le_three

-- ★★★★ FOUR STAGE-1 INTEGRAL THEOREMS ★★★★
#print axioms box0_seg1_re_integral_lower
#print axioms box0_seg1_re_integral_upper
#print axioms box0_seg1_im_integral_lower
#print axioms box0_seg1_im_integral_upper
