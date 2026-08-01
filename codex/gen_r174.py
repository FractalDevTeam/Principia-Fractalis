#!/usr/bin/env python3
"""Emit PF/DuplicationBezoutUniversal_r174.lean from verified sympy data."""
from sympy import symbols, expand, Poly, solve, resultant, div, total_degree
B2,B4,B6,B8,x,t,a,b = symbols('B2 B4 B6 B8 x t a b')
BV=(B2,B4,B6,B8)
disc = expand(-B2**2*B8 - 8*B4**3 - 27*B6**2 + 9*B2*B4*B6)
Phi  = expand(a**4 - B4*a**2*b**2 - 2*B6*a*b**3 - B8*b**4)
Psi  = expand(4*a**3*b + B2*a**2*b**2 + 2*B4*a*b**3 + B6*b**4)
phi  = x**4 - B4*x**2 - 2*B6*x - B8
psi  = 4*x**3 + B2*x**2 + 2*B4*x + B6

def bez(p,q,var,dp,dq,tag):
    R = resultant(Poly(p,var),Poly(q,var))
    us=symbols(f'u{tag}0:{dq}'); vs=symbols(f'v{tag}0:{dp}')
    u=sum(c*var**i for i,c in enumerate(us)); v=sum(c*var**i for i,c in enumerate(vs))
    sol=solve(Poly(expand(u*p+v*q-R),var).all_coeffs(), us+vs, dict=True); assert sol
    u,v=expand(u.subs(sol[0])),expand(v.subs(sol[0]))
    assert expand(u*p+v*q-R)==0
    return u,v,expand(R)

u,v,R  = bez(phi,psi,x,4,3,'b')
F2, G2 = expand(b**3*u.subs(x,a/b)), expand(b**3*v.subs(x,a/b))
phir, psir = expand(t**4*phi.subs(x,1/t)), expand(t**4*psi.subs(x,1/t))
ur,vr,Ra = bez(phir,psir,t,4,4,'a')
F1, G1 = expand(a**3*ur.subs(t,b/a)), expand(a**3*vr.subs(t,b/a))

assert expand(Ra-R)==0
assert expand(F1*Phi+G1*Psi - R*a**7)==0
assert expand(F2*Phi+G2*Psi - R*b**7)==0
rel = 4*B8 - B2*B6 + B4**2
q_,r_ = div(Poly(expand(R-disc**2),*BV), Poly(rel,*BV)); assert r_.as_expr()==0
Q = expand(q_.as_expr())
assert expand(R - disc**2 - Q*rel)==0
print("all sympy identities re-verified")

def L(e):
    s = str(expand(e)).replace('**','^')
    for k,w in [('B2','b₂'),('B4','b₄'),('B6','b₆'),('B8','b₈')]:
        s = s.replace(k,w)
    return s.replace('a','X').replace('b₂','b₂').replace('*b','*b')  # placeholder

def lean(e):
    """sympy -> Lean, with a->X, b->Y, B2->b₂ ..."""
    p = Poly(e, a, b, *BV)
    out = []
    for mono, c in zip(p.monoms(), p.coeffs()):
        c = int(c)
        parts = []
        for nm, k in zip(['X','Y','b₂','b₄','b₆','b₈'], mono):
            if k == 1: parts.append(nm)
            elif k > 1: parts.append(f'{nm}^{k}')
        term = ' * '.join(parts) if parts else '1'
        sign = '-' if c < 0 else '+'
        ac = abs(c)
        body = term if ac == 1 and parts else (f'{ac}' if not parts else f'{ac} * {term}')
        out.append((sign, body))
    s = ''
    for i,(sg,bd) in enumerate(out):
        if i == 0: s += ('-' + bd) if sg == '-' else bd
        else:      s += f' {sg} {bd}'
    return s

def wrap(s, ind='    ', width=94):
    words, lines, cur = s.split(' '), [], ind
    for w in words:
        if len(cur) + len(w) + 1 > width and cur.strip() != '':
            lines.append(cur.rstrip()); cur = ind + '  '
        cur += w + ' '
    lines.append(cur.rstrip())
    return '\n'.join(lines)

data = {'Phi':Phi,'Psi':Psi,'Disc':disc,'Res':R,'Corr':Q,'F1':F1,'G1':G1,'F2':F2,'G2':G2}
stats = {k: len(Poly(vv,a,b,*BV).terms()) for k,vv in data.items()}
open('codex/r174_data.txt','w').write(
    '\n\n'.join(f'-- {k} ({stats[k]} monomials)\n{lean(vv)}' for k,vv in data.items()))

hdr = f'''/-
# PF.DuplicationBezoutUniversal_r174

★★★ 2026-07-31 — THE DUPLICATION CONTENT BOUND, FOR EVERY CURVE AT ONCE ★★★

r157–r163 built the quasi-parallelogram layer for 5077a1 by hand: level-1
certificates, a content bound `d ∣ 5⁴·5077⁴` whose extra factor of 5 had to be
shown forced by a Hermite-normal-form argument, then size bounds and the
upper/lower products.  Seven stones, all curve-specific, and r147/r156 needed
the same seven again for 389a1.

**None of it was necessary.**  Write `x = X/Y` in lowest terms and homogenise
the duplication map `x(2P) = φ(x)/ψ(x)`:

  Φ(X,Y) = X⁴ − b₄X²Y² − 2b₆XY³ − b₈Y⁴
  Ψ(X,Y) = 4X³Y + b₂X²Y² + 2b₄XY³ + b₆Y⁴

Then `Res_x(φ, ψ) = Δ²` — a *universal* polynomial identity — and the Sylvester
cofactors give two explicit Bézout witnesses

  F₁·Φ + G₁·Ψ = Δ²·X⁷        F₂·Φ + G₂·Ψ = Δ²·Y⁷

so for coprime X,Y any common divisor of Φ and Ψ divides Δ²·gcd(X⁷,Y⁷) = Δ².
**One lemma, every rational elliptic curve, no per-curve content analysis.**

## What made this tractable

Stating it over `a₁..a₆` gives cofactors of 1853 monomials at degree 18 — too
big to be comfortable.  Φ, Ψ and Δ mention *only* the b-invariants, so working
in `ℤ[b₂,b₄,b₆,b₈]` instead drops that to **{stats['F1']+stats['G1']+stats['F2']+stats['G2']} monomials at degree 9**.

In that free basis `Res` is not literally `Δ²`; the two agree exactly modulo
mathlib's `WeierstrassCurve.b_relation`, `4b₈ = b₂b₆ − b₄²`.  The correction
multiplier is only {stats['Corr']} monomials, so each identity closes with a single
`linear_combination`.

Every coefficient here was produced and re-verified by `codex/gen_r174.py`;
nothing was transcribed by hand.

Kernel axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`,
no project axioms, no `native_decide`.

Author: Pablo Cohen + Claude. 2026-07-31.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- The cofactor defs are a few hundred integer monomials each; elaborating them
-- exceeds the default budget on instance unification alone.
set_option maxHeartbeats 4000000

namespace PrincipiaTractalis.DuplicationBezout

section Defs
variable (b₂ b₄ b₆ b₈ X Y : ℤ)

/-- Numerator of the duplication map, homogenised at `x = X/Y`. -/
def Phi : ℤ := {lean(Phi)}

/-- Denominator of the duplication map, homogenised at `x = X/Y`. -/
def Psi : ℤ := {lean(Psi)}

/-- The discriminant, in terms of the b-invariants. -/
def Disc : ℤ := {lean(disc)}

'''
def block(name, e, doc, args='b₂ b₄ b₆ b₈ X Y'):
    return f'/-- {doc} -/\ndef {name} : ℤ :=\n{wrap(lean(e))}\n\n'

body  = block('F1', F1, 'Bézout cofactor of `Phi` for the `X⁷` identity.')
body += block('G1', G1, 'Bézout cofactor of `Psi` for the `X⁷` identity.')
body += block('F2', F2, 'Bézout cofactor of `Phi` for the `Y⁷` identity.')
body += block('G2', G2, 'Bézout cofactor of `Psi` for the `Y⁷` identity.')

thms = f'''end Defs

/-- **Bézout, X-side.**  Holds for every curve, given only mathlib's b-relation. -/
theorem bezout_X (b₂ b₄ b₆ b₈ X Y : ℤ) (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    F1 b₂ b₄ b₆ b₈ X Y * Phi b₄ b₆ b₈ X Y
      + G1 b₂ b₄ b₆ b₈ X Y * Psi b₂ b₄ b₆ X Y
      = Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7 := by
  simp only [F1, G1, Phi, Psi, Disc]
  -- multiplier = (Res - Δ²)/(4b₈ - b₂b₆ + b₄²), inlined: it enters only here,
  -- after `simp`, so a `def` for it would never get unfolded.
  linear_combination (
{wrap(lean(Q), ind='    ')}) * X ^ 7 * hrel

/-- **Bézout, Y-side.** -/
theorem bezout_Y (b₂ b₄ b₆ b₈ X Y : ℤ) (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    F2 b₂ b₄ b₆ b₈ X Y * Phi b₄ b₆ b₈ X Y
      + G2 b₂ b₄ b₆ b₈ X Y * Psi b₂ b₄ b₆ X Y
      = Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7 := by
  simp only [F2, G2, Phi, Psi, Disc]
  linear_combination (
{wrap(lean(Q), ind='    ')}) * Y ^ 7 * hrel

/-- **THE CONTENT BOUND, UNIFORMLY IN THE CURVE.**  For `x = X/Y` in lowest
terms, the numerator and denominator of `x(2P)` share no factor beyond `Δ²`.

This is what r158 proved for 5077a1 alone, at the cost of a Hermite-normal-form
argument to show the stray factor of 5 was forced.  Here it is free. -/
theorem dvd_disc_sq_of_isCoprime (b₂ b₄ b₆ b₈ : ℤ)
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) {{X Y d : ℤ}}
    (hXY : IsCoprime X Y) (hP : d ∣ Phi b₄ b₆ b₈ X Y) (hQ : d ∣ Psi b₂ b₄ b₆ X Y) :
    d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 := by
  obtain ⟨s, u, hsu⟩ : IsCoprime (X ^ 7) (Y ^ 7) := hXY.pow
  have hX : d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7 := by
    rw [← bezout_X b₂ b₄ b₆ b₈ X Y hrel]; exact dvd_add (hP.mul_left _) (hQ.mul_left _)
  have hY : d ∣ Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7 := by
    rw [← bezout_Y b₂ b₄ b₆ b₈ X Y hrel]; exact dvd_add (hP.mul_left _) (hQ.mul_left _)
  have : Disc b₂ b₄ b₆ b₈ ^ 2
      = s * (Disc b₂ b₄ b₆ b₈ ^ 2 * X ^ 7) + u * (Disc b₂ b₄ b₆ b₈ ^ 2 * Y ^ 7) := by
    linear_combination (Disc b₂ b₄ b₆ b₈ ^ 2) * hsu.symm
  rw [this]
  exact dvd_add (hX.mul_left _) (hY.mul_left _)


/-! ### Validation against the two curves already built by hand.

Not decoration: these are the exact curves whose content bounds cost r158 (and
its 389a1 predecessor) a hand-built Hermite-normal-form argument each.  If the
universal statement did not specialise to them, it would be wrong. -/

section Validation

/-- 389a1: `(a₁,a₂,a₃,a₄,a₆) = (0,1,1,-2,0)`, giving `(b₂,b₄,b₆,b₈) = (4,-4,1,-3)`. -/
theorem b_relation_389a1 : (4 : ℤ) * (-3) = 4 * 1 - (-4) ^ 2 := by decide

theorem disc_389a1 : Disc 4 (-4) 1 (-3) = 389 := by decide

/-- The content bound for 389a1 is `Δ² = 389² = 151321`, with no curve-specific
argument of any kind. -/
theorem content_389a1 {{X Y d : ℤ}} (hXY : IsCoprime X Y)
    (hP : d ∣ Phi (-4) 1 (-3) X Y) (hQ : d ∣ Psi 4 (-4) 1 X Y) :
    d ∣ 151321 := by
  have := dvd_disc_sq_of_isCoprime 4 (-4) 1 (-3) b_relation_389a1 hXY hP hQ
  rwa [disc_389a1] at this

/-- 5077a1: `(a₁,a₂,a₃,a₄,a₆) = (0,0,1,-7,6)`, giving `(b₂,b₄,b₆,b₈) = (0,-14,25,-49)`. -/
theorem b_relation_5077a1 : (4 : ℤ) * (-49) = 0 * 25 - (-14) ^ 2 := by decide

theorem disc_5077a1 : Disc 0 (-14) 25 (-49) = 5077 := by decide

/-- The content bound for 5077a1 is `Δ² = 5077² = 25775929`.  Compare r158,
which proved `d ∣ 5⁴·5077⁴` and needed a Hermite-normal-form argument to show
the stray factor of 5 was forced. -/
theorem content_5077a1 {{X Y d : ℤ}} (hXY : IsCoprime X Y)
    (hP : d ∣ Phi (-14) 25 (-49) X Y) (hQ : d ∣ Psi 0 (-14) 25 X Y) :
    d ∣ 25775929 := by
  have := dvd_disc_sq_of_isCoprime 0 (-14) 25 (-49) b_relation_5077a1 hXY hP hQ
  rwa [disc_5077a1] at this

end Validation

end PrincipiaTractalis.DuplicationBezout

#print axioms PrincipiaTractalis.DuplicationBezout.bezout_X
#print axioms PrincipiaTractalis.DuplicationBezout.bezout_Y
#print axioms PrincipiaTractalis.DuplicationBezout.dvd_disc_sq_of_isCoprime
#print axioms PrincipiaTractalis.DuplicationBezout.content_389a1
#print axioms PrincipiaTractalis.DuplicationBezout.content_5077a1
'''
open('PF_Lean4_Code/PF/DuplicationBezoutUniversal_r174.lean','w').write(hdr+body+thms)
print("wrote PF/DuplicationBezoutUniversal_r174.lean")
print("  monomials:", {k:stats[k] for k in ['F1','G1','F2','G2','Corr']})
