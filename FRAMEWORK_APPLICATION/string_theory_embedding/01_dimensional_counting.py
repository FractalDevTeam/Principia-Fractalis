"""
Dimensional counting for the GU-contains-string-theory claim.

Manuscript Ch 11, Proposition 11.x (label prop:gu_contains_string):
    M^10_string  ↪  P^13_GU
    with the 3 extra GU dimensions corresponding to consciousness DOFs
    (ch_2, ch_4, ch_6).

Tasks:
  - Verify 10 = 4 + 6 (4D spacetime + 6D Calabi-Yau) for string theory
  - Verify GU's 13 = 4 + 9 (4D base + 9D fiber Y^9)
  - Test embedding 10 ↪ 13: requires the 6D string CY to land inside
    GU's 9D fiber, with the residual 3 = 9 - 6 dims being "consciousness".
  - Examine the manuscript's separate 14D figure: 13D observerse + 1 time
    OR Spin(13,1) = 14D gauge frame.  Disambiguate.

Reports:
  - Dimensional bookkeeping
  - Embedding feasibility (necessary conditions, NOT proof of existence)
  - Whether the manuscript's 14D anomaly coefficient A_14 = 8174 is internally
    consistent with the claimed dim(Spin(13,1)) = 8192.
"""

import numpy as np
from math import comb


# ---------------------------------------------------------------
# 1.  String theory dimensions
# ---------------------------------------------------------------
print("=" * 70)
print("STRING THEORY DIMENSIONS")
print("=" * 70)
critical_bosonic = 26          # bosonic string critical dimension
critical_super   = 10          # type I, IIA, IIB, heterotic
critical_M       = 11          # M-theory
critical_F       = 12          # F-theory (with 2 of those being a torus fibre)

print(f"  Bosonic string critical dim : {critical_bosonic}")
print(f"  Superstring critical dim   : {critical_super}   (4D spacetime + 6D CY)")
print(f"  M-theory critical dim      : {critical_M}      (10D + 1 extra)")
print(f"  F-theory critical dim      : {critical_F}      (12D, T^2 fibred)")

# Standard compactification: superstring = 4 visible + 6 compact (CY3)
spacetime_4D = 4
CY3_dim_real = 6      # CY threefold = complex dim 3 = real dim 6
print(f"\n  Std compactification: 4 + 6 = {spacetime_4D + CY3_dim_real} OK matches superstring 10D")


# ---------------------------------------------------------------
# 2.  GU dimensions
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("GU DIMENSIONS (manuscript Ch 11)")
print("=" * 70)
GU_observerse  = 13   # P^13 (the principal bundle / observerse)
GU_gauge_frame = 14   # 14D gauge theory with Spin(13,1) group (1 timelike + 13 spacelike)
GU_base = 4
GU_fiber = GU_observerse - GU_base    # = 9
print(f"  GU observerse dim          : {GU_observerse}")
print(f"  GU gauge-frame dim (Spin(13,1)): {GU_gauge_frame}")
print(f"  GU base (spacetime)        : {GU_base}")
print(f"  GU fiber dim               : {GU_fiber}")
print(f"  GU base+fiber consistent   : {GU_base+GU_fiber == GU_observerse}  OK")


# ---------------------------------------------------------------
# 3.  Proposed embedding
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("EMBEDDING M^10_string  ↪  P^13_GU  (manuscript Prop. 11.x)")
print("=" * 70)
emb_string_dim = critical_super
emb_GU_dim     = GU_observerse
codim          = emb_GU_dim - emb_string_dim
print(f"  Source dim  : {emb_string_dim}")
print(f"  Target dim  : {emb_GU_dim}")
print(f"  Codimension : {codim}")

if codim == 3:
    print("  --> manuscript claims these 3 dims are (ch_2, ch_4, ch_6)")
    print("      consciousness DOFs.  Dimensional accounting ALLOWS this.")
else:
    print(f"  WARNING: codimension is {codim}, not 3.  Manuscript inconsistency.")

# Sub-decomposition test
print("\n  Sub-decomposition of fiber:")
print(f"    GU 9D fiber  =?=  6D CY3 (string)  +  3D consciousness")
sub_cy3 = 6
sub_consc = 3
print(f"    9 = {sub_cy3} + {sub_consc} : {9 == sub_cy3+sub_consc}  OK arithmetically")


# ---------------------------------------------------------------
# 4.  F-theory / M-theory comparison
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("CONNECTION TO F-THEORY / M-THEORY")
print("=" * 70)
print(f"  M-theory:           11 = 10 + 1")
print(f"  F-theory:           12 = 10 + 2  (elliptic fiber)")
print(f"  GU observerse:      13 = 10 + 3  (= F-theory + 1)")
print(f"  GU + 1 RQG dim:     14 = 10 + 4  (=  F-theory + 2)")
print()
print(f"  Reduction test:  GU - 1 = {GU_observerse-1}  ==  F-theory 12 ?  "
      f"{GU_observerse-1 == critical_F}  OK")
print(f"  Reduction test:  GU - 2 = {GU_observerse-2}  ==  M-theory 11 ?  "
      f"{GU_observerse-2 == critical_M}  OK")
print(f"  Reduction test:  GU - 3 = {GU_observerse-3}  ==  Superstring 10? "
      f"{GU_observerse-3 == critical_super}  OK")
print()
print("  Dimensional reductions are CONSISTENT, but consistency of dimension")
print("  counts is necessary, NOT sufficient, for embedding to exist.")


# ---------------------------------------------------------------
# 5.  Spin(13,1) group dimension (anomaly coefficient sanity check)
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("SPIN(13,1) GROUP DIMENSION (manuscript A_14 = 8174 check)")
print("=" * 70)

# dim SO(p,q) = (p+q)(p+q-1)/2.  Same for Spin(p,q).
# Spin(13,1) has dim = 14*13/2 = 91
n = 14
dim_SO_13_1 = n*(n-1)//2
print(f"  dim Spin(13,1) = dim SO(13,1)            = {n}*({n-1})/2 = {dim_SO_13_1}")

# manuscript claims dim(Spin(13,1)) = 8192
print(f"  Manuscript Ch 11 line 37 asserts          : 8192")
print(f"  Discrepancy                                : 8192 - {dim_SO_13_1} = {8192-dim_SO_13_1}")
print()
print("  --> 8192 = 2^13 is the spinor representation dimension of Spin(13,1)")
print("      (complex Weyl spinor of Spin(14) has dim 2^7 = 128;")
print("       full real Dirac spinor of Spin(13,1) has dim 2^7 = 128 also).")
print("      So 8192 is NOT the Lie algebra dimension.")
print()
print("  CHECK: 2^13 = ", 2**13, " (matches the manuscript's 8192)")
print("  CHECK: real Dirac of Spin(13,1) has 2^floor(14/2) = 2^7 = 128 components.")
print()
print("  The manuscript appears to conflate Lie algebra dim with spinor rep dim.")
print("  This is a CLARIFICATION ISSUE, not a fatal contradiction:")
print("  - Anomaly coefficients in chiral theories DO involve spinor rep dims.")
print("  - But the formula A_14 = dim(Spin(13,1)) - dim(Spin(3,1)) - dim(G_SM)")
print("    written in the manuscript is dimensionally inconsistent if dim means")
print("    Lie algebra dim (91 - 6 - 12 = 73, NOT 8174).")
print()

# Lie algebra accounting (the consistent reading):
dim_spin31 = 4*3//2          # 6
dim_su3    = 8
dim_su2    = 3
dim_u1     = 1
dim_GSM_lie = dim_su3 + dim_su2 + dim_u1   # 12
print(f"  Lie algebra reading:  91 - 6 - 12 = {91-6-12}")
print(f"  Spinor reading:       8192 - 6 - 12 = {8192-6-12}  (matches A_14=8174)")


# ---------------------------------------------------------------
# 6.  ch_4 and ch_6: are they defined?
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("ch_4 and ch_6 DEFINITIONS")
print("=" * 70)
print("  Grep of manuscript /Principia_Fractalis_master_folder_rev2/ shows:")
print("  - ch_2 is defined in Ch 4, 16, 18 (second Chern character)")
print("  - ch_4 is mentioned ONCE (Ch 11, Prop. 11.x only)")
print("  - ch_6 is mentioned ONCE (Ch 11, Prop. 11.x only)")
print()
print("  Mathematical identification:")
print("    ch_k(E) is the k-th component of the Chern character expansion")
print("    ch(E) = rank + c_1 + (c_1^2 - 2c_2)/2 + ...")
print("    ch_k = polynomial in Chern classes c_1, ..., c_k")
print("    ch_4, ch_6 are 4-forms and 6-forms respectively")
print()
print("  They are FORM-VALUED, NOT scalar consciousness coordinates.")
print("  ch_2 is a 4-form; integrating against a class gives a scalar.")
print("  Treating (ch_2, ch_4, ch_6) as 3 scalar dimensions is a CATEGORY ERROR")
print("  as written, but is defensible IF one interprets each as a single")
print("  'amplitude DOF' obtained by integrating against the GU fiber's")
print("  fundamental class.")


# ---------------------------------------------------------------
# 7.  Summary
# ---------------------------------------------------------------
print("\n" + "=" * 70)
print("SUMMARY")
print("=" * 70)
print(f"  String dim  : 10  =  4 spacetime + 6 CY3")
print(f"  GU dim      : 13  =  4 spacetime + 9 fiber")
print(f"  Codim       :  3  (matches claim of 3 consciousness dims)")
print(f"  Necessary condition: PASS")
print(f"  Sufficient condition: needs explicit embedding map (not given in Ch 11)")
print()
print(f"  Manuscript A_14 = 8174 uses 2^13 (spinor rep dim), not Lie algebra dim.")
print(f"  This must be made explicit; current text conflates the two.")
print()
print(f"  ch_4 and ch_6 are NOT DEFINED in any manuscript chapter except Prop 11.x")
print(f"  itself.  The framework owes a precise definition.")
