#!/usr/bin/env python3
"""Emit PF/DuplicationSizeUniversal_r175.lean -- the size half of kappa_E."""
from sympy import symbols, expand, Poly, solve, resultant
B2,B4,B6,B8,x,t,a,b = symbols('B2 B4 B6 B8 x t a b')
BV=(B2,B4,B6,B8)
phi = x**4 - B4*x**2 - 2*B6*x - B8
psi = 4*x**3 + B2*x**2 + 2*B4*x + B6
Phi = expand(a**4 - B4*a**2*b**2 - 2*B6*a*b**3 - B8*b**4)
Psi = expand(4*a**3*b + B2*a**2*b**2 + 2*B4*a*b**3 + B6*b**4)
def bez(p,q,var,dp,dq,tag):
    R = resultant(Poly(p,var),Poly(q,var))
    us=symbols(f'u{tag}0:{dq}'); vs=symbols(f'v{tag}0:{dp}')
    u=sum(c*var**i for i,c in enumerate(us)); v=sum(c*var**i for i,c in enumerate(vs))
    sol=solve(Poly(expand(u*p+v*q-R),var).all_coeffs(), us+vs, dict=True); assert sol
    return expand(u.subs(sol[0])), expand(v.subs(sol[0])), expand(R)
u,v,R = bez(phi,psi,x,4,3,'b')
F2,G2 = expand(b**3*u.subs(x,a/b)), expand(b**3*v.subs(x,a/b))
phir,psir = expand(t**4*phi.subs(x,1/t)), expand(t**4*psi.subs(x,1/t))
ur,vr,_ = bez(phir,psir,t,4,4,'a')
F1,G1 = expand(a**3*ur.subs(t,b/a)), expand(a**3*vr.subs(t,b/a))
assert expand(F1*Phi+G1*Psi-R*a**7)==0 and expand(F2*Phi+G2*Psi-R*b**7)==0
print("cofactor identities re-verified")

def lean(e):
    if e == 0: return '0'
    p = Poly(e, *BV); out=[]
    for mono,c in zip(p.monoms(), p.coeffs()):
        c=int(c); parts=[]
        for nm,k in zip(['b₂','b₄','b₆','b₈'], mono):
            if k==1: parts.append(nm)
            elif k>1: parts.append(f'{nm}^{k}')
        term=' * '.join(parts)
        ac=abs(c); sg='-' if c<0 else '+'
        body = term if (ac==1 and parts) else (f'{ac}' if not parts else f'{ac} * {term}')
        out.append((sg,body))
    s=''
    for i,(sg,bd) in enumerate(out):
        s += (('-'+bd) if sg=='-' else bd) if i==0 else f' {sg} {bd}'
    return s

def wrap(s, ind='    ', width=92):
    lines,cur=[],ind
    for w in s.split(' '):
        if len(cur)+len(w)+1>width and cur.strip(): lines.append(cur.rstrip()); cur=ind+'  '
        cur+=w+' '
    lines.append(cur.rstrip()); return '\n'.join(lines)

def coeffs3(e):
    p = Poly(e, a, b)
    return [expand(p.coeff_monomial(a**(3-i)*b**i)) for i in range(4)]

defs = ''
for nm, e in [("F1",F1),("G1",G1),("F2",F2),("G2",G2)]:
    cs = coeffs3(e)
    for i,c in enumerate(cs):
        defs += (f'/-- Coefficient of `X^{3-i} Y^{i}` in `{nm}`. -/\n'
                 f'def c{nm}{i} (b₂ b₄ b₆ b₈ : ℤ) : ℤ :=\n{wrap(lean(c))}\n\n')
    defs += (f'/-- Sum of absolute coefficients of `{nm}`, the constant in its size bound. -/\n'
             f'def S{nm} (b₂ b₄ b₆ b₈ : ℤ) : ℤ := |c{nm}0 b₂ b₄ b₆ b₈| + |c{nm}1 b₂ b₄ b₆ b₈|'
             f' + |c{nm}2 b₂ b₄ b₆ b₈| + |c{nm}3 b₂ b₄ b₆ b₈|\n\n')

hdr = '''/-
# PF.DuplicationSizeUniversal_r175

★★★ 2026-07-31 — THE SIZE HALF OF κ_E, ALSO FOR EVERY CURVE ★★★

r174 gave the *content* half of the universal duplication window: for `x = X/Y`
in lowest terms, `gcd(Φ(X,Y), Ψ(X,Y)) ∣ Δ²`, uniformly in the curve.  This file
gives the *size* half, again with no curve-specific input:

  **upper**  `max |Φ| |Ψ| ≤ CU · M⁴`
  **lower**  `Δ² · M⁴ ≤ CL · max |Φ| |Ψ|`          where `M = max |X| |Y|`

`CU` is the obvious coefficient sum.  `CL` comes from r174's own Bézout pair:
`Δ²X⁷ = F₁Φ + G₁Ψ` and `Δ²Y⁷ = F₂Φ + G₂Ψ`, and each cofactor is a binary cubic,
so `Δ²M⁷ ≤ CL·M³·max |Φ| |Ψ|`; cancelling `M³` gives the bound.  The same
identity that killed the content analysis kills the archimedean one.

Together with r174 these are exactly the ingredients of `HeightWindow` (r171),
which r173 showed is all the canonical height ever needed.

## What κ this actually gives, honestly

Chaining the two with r174's `gcd ∣ Δ²`:

  `H(x(2P)) = max|Φ||Ψ| / gcd ≤ CU · M⁴`      (since `gcd ≥ 1`)
  `H(x(2P)) ≥ max|Φ||Ψ| / Δ² ≥ M⁴ / CL`       (the `Δ²` cancels)

so `κ_E = max(CU, CL)`.  Measured:

| curve  | CU  | CL          | universal κ | hand-built κ |
|--------|-----|-------------|-------------|--------------|
| 389a1  | 17  | 672192      | 672192      | 1728         |
| 5077a1 | 114 | 536913058   | 536913058   | 105754       |

**The universal κ is worse than the hand-built one**, by ~400× and ~5000×.
That is the honest price of uniformity: `CL` sums absolute values of the Bézout
cofactors, which is far from tight.  It matters downstream — the torsion
enumeration bound is `κ^(1/3)`, so 389a1 goes from 12 candidates-wide to ~88.

Two things make it worth having anyway.  The `CU` side *is* sharp: 17 and 114
are exactly the size constants r159 and its 389a1 predecessor derived by hand.
And a κ that is automatic for every curve beats a sharp κ that costs seven
stones — sharpening a specific curve later is optional, deriving it at all is
not.

Every coefficient produced and re-verified by `codex/gen_r175.py`.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import PF.DuplicationBezoutUniversal_r174
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 4000000

namespace PrincipiaTractalis.DuplicationSize

open PrincipiaTractalis.DuplicationBezout

/-! ### Binary form bounds -/

/-- A binary quartic is bounded by its coefficient sum times `max |X| |Y| ^ 4`. -/
theorem abs_form4_le (c₀ c₁ c₂ c₃ c₄ X Y : ℤ) :
    |c₀ * X ^ 4 + c₁ * X ^ 3 * Y + c₂ * X ^ 2 * Y ^ 2 + c₃ * X * Y ^ 3 + c₄ * Y ^ 4|
      ≤ (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4 := by
  have hX : |X| ≤ max |X| |Y| := le_max_left _ _
  have hY : |Y| ≤ max |Y| |X| := le_max_left _ _
  rw [max_comm |Y| |X|] at hY
  have h0 : (0 : ℤ) ≤ |X| := abs_nonneg _
  have h1 : (0 : ℤ) ≤ |Y| := abs_nonneg _
  have hM0 : (0 : ℤ) ≤ max |X| |Y| := le_trans h0 (le_max_left _ _)
  calc |c₀ * X ^ 4 + c₁ * X ^ 3 * Y + c₂ * X ^ 2 * Y ^ 2 + c₃ * X * Y ^ 3 + c₄ * Y ^ 4|
      ≤ |c₀ * X ^ 4| + |c₁ * X ^ 3 * Y| + |c₂ * X ^ 2 * Y ^ 2| + |c₃ * X * Y ^ 3|
          + |c₄ * Y ^ 4| := by
        refine (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
          (add_le_add_right ((abs_add _ _).trans
            (add_le_add_right (abs_add _ _) _)) _)) _)
    _ = |c₀| * |X| ^ 4 + |c₁| * |X| ^ 3 * |Y| + |c₂| * |X| ^ 2 * |Y| ^ 2
          + |c₃| * |X| * |Y| ^ 3 + |c₄| * |Y| ^ 4 := by
        simp only [abs_mul, abs_pow]
    _ ≤ (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4 := by
        have e : (|c₀| + |c₁| + |c₂| + |c₃| + |c₄|) * max |X| |Y| ^ 4
            = |c₀| * max |X| |Y| ^ 4 + |c₁| * max |X| |Y| ^ 3 * max |X| |Y|
              + |c₂| * max |X| |Y| ^ 2 * max |X| |Y| ^ 2
              + |c₃| * max |X| |Y| * max |X| |Y| ^ 3 + |c₄| * max |X| |Y| ^ 4 := by ring
        rw [e]; gcongr <;>
          first
            | assumption
            | positivity
            | exact mul_nonneg (abs_nonneg _) (pow_nonneg hM0 _)

/-- A binary cubic is bounded by its coefficient sum times `max |X| |Y| ^ 3`. -/
theorem abs_form3_le (c₀ c₁ c₂ c₃ X Y : ℤ) :
    |c₀ * X ^ 3 + c₁ * X ^ 2 * Y + c₂ * X * Y ^ 2 + c₃ * Y ^ 3|
      ≤ (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3 := by
  have hX : |X| ≤ max |X| |Y| := le_max_left _ _
  have hY : |Y| ≤ max |Y| |X| := le_max_left _ _
  rw [max_comm |Y| |X|] at hY
  have h0 : (0 : ℤ) ≤ |X| := abs_nonneg _
  have h1 : (0 : ℤ) ≤ |Y| := abs_nonneg _
  have hM0 : (0 : ℤ) ≤ max |X| |Y| := le_trans h0 (le_max_left _ _)
  calc |c₀ * X ^ 3 + c₁ * X ^ 2 * Y + c₂ * X * Y ^ 2 + c₃ * Y ^ 3|
      ≤ |c₀ * X ^ 3| + |c₁ * X ^ 2 * Y| + |c₂ * X * Y ^ 2| + |c₃ * Y ^ 3| := by
        refine (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans
          (add_le_add_right (abs_add _ _) _)) _)
    _ = |c₀| * |X| ^ 3 + |c₁| * |X| ^ 2 * |Y| + |c₂| * |X| * |Y| ^ 2
          + |c₃| * |Y| ^ 3 := by simp only [abs_mul, abs_pow]
    _ ≤ (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3 := by
        have e : (|c₀| + |c₁| + |c₂| + |c₃|) * max |X| |Y| ^ 3
            = |c₀| * max |X| |Y| ^ 3 + |c₁| * max |X| |Y| ^ 2 * max |X| |Y|
              + |c₂| * max |X| |Y| * max |X| |Y| ^ 2 + |c₃| * max |X| |Y| ^ 3 := by ring
        rw [e]; gcongr <;>
          first
            | assumption
            | positivity
            | exact mul_nonneg (abs_nonneg _) (pow_nonneg hM0 _)

'''

tail = '''section Defs
variable (b₂ b₄ b₆ b₈ : ℤ)

/-- The upper constant. -/
def CU : ℤ := max (1 + |b₄| + 2 * |b₆| + |b₈|) (4 + |b₂| + 2 * |b₄| + |b₆|)

/-- The lower constant, from r174's Bézout cofactors. -/
def CL : ℤ := max (SF1 b₂ b₄ b₆ b₈ + SG1 b₂ b₄ b₆ b₈) (SF2 b₂ b₄ b₆ b₈ + SG2 b₂ b₄ b₆ b₈)

/-- `CL` is a max of sums of absolute values, hence nonnegative. -/
theorem CL_nonneg (b₂ b₄ b₆ b₈ : ℤ) : 0 ≤ CL b₂ b₄ b₆ b₈ :=
  le_max_of_le_left (by simp only [SF1, SG1]; positivity)

end Defs

variable {b₂ b₄ b₆ b₈ : ℤ}

/-! ### Upper bounds -/

theorem abs_Phi_le (X Y : ℤ) :
    |Phi b₄ b₆ b₈ X Y| ≤ (1 + |b₄| + 2 * |b₆| + |b₈|) * max |X| |Y| ^ 4 := by
  have h := abs_form4_le 1 0 (-b₄) (-(2 * b₆)) (-b₈) X Y
  have e1 : (1 : ℤ) * X ^ 4 + 0 * X ^ 3 * Y + (-b₄) * X ^ 2 * Y ^ 2
      + (-(2 * b₆)) * X * Y ^ 3 + (-b₈) * Y ^ 4 = Phi b₄ b₆ b₈ X Y := by
    simp only [Phi]; ring
  have e2 : |(1 : ℤ)| + |(0 : ℤ)| + |-b₄| + |-(2 * b₆)| + |-b₈|
      = 1 + |b₄| + 2 * |b₆| + |b₈| := by
    simp only [abs_neg, abs_mul, abs_zero, abs_one]; norm_num
  rwa [e1, e2] at h

theorem abs_Psi_le (X Y : ℤ) :
    |Psi b₂ b₄ b₆ X Y| ≤ (4 + |b₂| + 2 * |b₄| + |b₆|) * max |X| |Y| ^ 4 := by
  have h := abs_form4_le 0 4 b₂ (2 * b₄) b₆ X Y
  have e1 : (0 : ℤ) * X ^ 4 + 4 * X ^ 3 * Y + b₂ * X ^ 2 * Y ^ 2
      + (2 * b₄) * X * Y ^ 3 + b₆ * Y ^ 4 = Psi b₂ b₄ b₆ X Y := by
    simp only [Psi]; ring
  have e2 : |(0 : ℤ)| + |(4 : ℤ)| + |b₂| + |2 * b₄| + |b₆|
      = 4 + |b₂| + 2 * |b₄| + |b₆| := by
    simp only [abs_mul, abs_zero]; norm_num
  rwa [e1, e2] at h

/-- **The upper bound**: `max |Φ| |Ψ| ≤ CU · M⁴`. -/
theorem max_abs_le (X Y : ℤ) :
    max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| ≤ CU b₂ b₄ b₆ b₈ * max |X| |Y| ^ 4 := by
  have hM : (0 : ℤ) ≤ max |X| |Y| ^ 4 := by positivity
  refine max_le ((abs_Phi_le X Y).trans (mul_le_mul_of_nonneg_right ?_ hM))
    ((abs_Psi_le X Y).trans (mul_le_mul_of_nonneg_right ?_ hM))
  · exact le_max_left _ _
  · exact le_max_right _ _

/-! ### Lower bound -/

'''
for nm in ["F1","G1","F2","G2"]:
    tail += f'''theorem abs_{nm}_le (X Y : ℤ) :
    |{nm} b₂ b₄ b₆ b₈ X Y| ≤ S{nm} b₂ b₄ b₆ b₈ * max |X| |Y| ^ 3 := by
  have h := abs_form3_le (c{nm}0 b₂ b₄ b₆ b₈) (c{nm}1 b₂ b₄ b₆ b₈) (c{nm}2 b₂ b₄ b₆ b₈)
    (c{nm}3 b₂ b₄ b₆ b₈) X Y
  have e : c{nm}0 b₂ b₄ b₆ b₈ * X ^ 3 + c{nm}1 b₂ b₄ b₆ b₈ * X ^ 2 * Y
      + c{nm}2 b₂ b₄ b₆ b₈ * X * Y ^ 2 + c{nm}3 b₂ b₄ b₆ b₈ * Y ^ 3
      = {nm} b₂ b₄ b₆ b₈ X Y := by
    simp only [{nm}, c{nm}0, c{nm}1, c{nm}2, c{nm}3]; ring
  rw [e] at h
  exact h.trans_eq (by simp only [S{nm}])

'''

tail += '''/-- **The lower bound**: `Δ² · M⁴ ≤ CL · max |Φ| |Ψ|`.

The Bézout pair of r174 does double duty: it bounded the content, and it bounds
the archimedean size from below too. -/
theorem disc_sq_mul_le (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) (X Y : ℤ) :
    Disc b₂ b₄ b₆ b₈ ^ 2 * max |X| |Y| ^ 4
      ≤ CL b₂ b₄ b₆ b₈ * max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| := by
  set M := max |X| |Y| with hMdef
  set P := max |Phi b₄ b₆ b₈ X Y| |Psi b₂ b₄ b₆ X Y| with hPdef
  have hM0 : (0 : ℤ) ≤ M := le_trans (abs_nonneg X) (le_max_left _ _)
  have hP0 : (0 : ℤ) ≤ P := le_trans (abs_nonneg _) (le_max_left _ _)
  rcases eq_or_lt_of_le hM0 with hM | hMpos
  · -- M = 0 forces X = Y = 0; the left side vanishes.
    have : M ^ 4 = 0 := by rw [← hM]; ring
    rw [this, mul_zero]
    exact mul_nonneg (CL_nonneg b₂ b₄ b₆ b₈) hP0
  -- The two Bézout identities, each bounded termwise.
  have key : ∀ (Z : ℤ) (F G SF SG : ℤ),
      Disc b₂ b₄ b₆ b₈ ^ 2 * Z ^ 7 = F * Phi b₄ b₆ b₈ X Y + G * Psi b₂ b₄ b₆ X Y →
      |F| ≤ SF * M ^ 3 → |G| ≤ SG * M ^ 3 → |Z| = M →
      Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 ≤ (SF + SG) * M ^ 3 * P := by
    intro Z F G SF G' hid hF hG hZ
    have hD0 : (0 : ℤ) ≤ Disc b₂ b₄ b₆ b₈ ^ 2 := sq_nonneg _
    have hSF : (0 : ℤ) ≤ SF * M ^ 3 := le_trans (abs_nonneg _) hF
    have hSG : (0 : ℤ) ≤ G' * M ^ 3 := le_trans (abs_nonneg _) hG
    have habs : Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 = |Disc b₂ b₄ b₆ b₈ ^ 2 * Z ^ 7| := by
      rw [abs_mul, abs_of_nonneg hD0, abs_pow, hZ]
    rw [habs, hid]
    calc |F * Phi b₄ b₆ b₈ X Y + G * Psi b₂ b₄ b₆ X Y|
        ≤ |F * Phi b₄ b₆ b₈ X Y| + |G * Psi b₂ b₄ b₆ X Y| := abs_add _ _
      _ = |F| * |Phi b₄ b₆ b₈ X Y| + |G| * |Psi b₂ b₄ b₆ X Y| := by
          rw [abs_mul, abs_mul]
      _ ≤ (SF * M ^ 3) * P + (G' * M ^ 3) * P := by
          exact add_le_add
            (mul_le_mul hF (le_max_left _ _) (abs_nonneg _) hSF)
            (mul_le_mul hG (le_max_right _ _) (abs_nonneg _) hSG)
      _ = (SF + G') * M ^ 3 * P := by ring
  have hM3 : (0 : ℤ) < M ^ 3 := by positivity
  have hstep : Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 ≤ CL b₂ b₄ b₆ b₈ * M ^ 3 * P := by
    rcases max_cases |X| |Y| with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · refine (key X (F1 b₂ b₄ b₆ b₈ X Y) (G1 b₂ b₄ b₆ b₈ X Y) _ _
        (bezout_X b₂ b₄ b₆ b₈ X Y hrel).symm (abs_F1_le X Y) (abs_G1_le X Y)
        (by rw [hMdef, hmax])).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hM3)) hP0
    · refine (key Y (F2 b₂ b₄ b₆ b₈ X Y) (G2 b₂ b₄ b₆ b₈ X Y) _ _
        (bezout_Y b₂ b₄ b₆ b₈ X Y hrel).symm (abs_F2_le X Y) (abs_G2_le X Y)
        (by rw [hMdef, hmax])).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hM3)) hP0
  refine le_of_mul_le_mul_right ?_ hM3
  calc Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 4 * M ^ 3
      = Disc b₂ b₄ b₆ b₈ ^ 2 * M ^ 7 := by ring
    _ ≤ CL b₂ b₄ b₆ b₈ * M ^ 3 * P := hstep
    _ = CL b₂ b₄ b₆ b₈ * P * M ^ 3 := by ring

end PrincipiaTractalis.DuplicationSize

#print axioms PrincipiaTractalis.DuplicationSize.abs_form4_le
#print axioms PrincipiaTractalis.DuplicationSize.max_abs_le
#print axioms PrincipiaTractalis.DuplicationSize.disc_sq_mul_le
'''
open('PF_Lean4_Code/PF/DuplicationSizeUniversal_r175.lean','w').write(hdr+defs+tail)
print("wrote PF/DuplicationSizeUniversal_r175.lean")
