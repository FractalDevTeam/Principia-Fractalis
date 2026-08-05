#!/usr/bin/env python3
# gen_r197.py -- generates PF/SecantSizeLower_r197.lean (2026-08-05)
# Term-by-term size bounds for the 8 secant Bezout cofactors (r195/r196),
# corner lemmas, and the universal secant size LOWER bound.
import sympy as sp

B2,B4,B6,B8,a1,b1,a2,b2 = sp.symbols('B2 B4 B6 B8 a1 b1 a2 b2')

CERTS = {
 'sfCert₁': ('B₂ B₄ B₆', 'SecantContentBridge', B2**2*a1**2*b1**4*b2 + 2*B2*B4*a1*b1**5*b2 + 8*B2*a1**3*b1**3*b2 + 2*B2*a1**2*a2*b1**4 + B4**2*b1**6*b2 + 6*B4*a1**2*b1**4*b2 + 2*B4*a1*a2*b1**5 - 2*B6*a1*b1**5*b2 + 16*a1**4*b1**2*b2 + 12*a1**3*a2*b1**3),
 'sfCert₂': ('B₂ B₄ B₆', 'SecantContentBridge', 2*B2*a1**2*b1**4*b2 - B2*a1*a2*b1**5 + 3*B4*a1*b1**5*b2 - B4*a2*b1**6 + B6*b1**6*b2 + 10*a1**3*b1**3*b2 - 6*a1**2*a2*b1**4),
 'prCert₁': ('B₄ B₆ B₈', 'SecantContentBridge', B4**2*a1**2*b1**4*b2 + 2*B4*B6*a1*b1**5*b2 - 2*B4*a1**4*b1**2*b2 - B4*a1**3*a2*b1**3 + B6**2*b1**6*b2 - B6*a1**3*b1**3*b2 - B6*a1**2*a2*b1**4 + B8*a1**2*b1**4*b2 + a1**6*b2 + 2*a1**5*a2*b1),
 'prCert₂': ('B₄ B₆ B₈', 'SecantContentBridge', -2*B4*a1**2*b1**4*b2 + B4*a1*a2*b1**5 - 3*B6*a1*b1**5*b2 + B6*a2*b1**6 - B8*b1**6*b2 + 3*a1**4*b1**2*b2 - 2*a1**3*a2*b1**3),
 'sfCertA₁': ('B₂ B₄ B₆', 'SecantContentUniversal', B2**2*a1**4*a2*b1**2 + B2*B4*a1**4*b1**2*b2 + 4*B2*B4*a1**3*a2*b1**3 + B2*B6*a1**3*b1**3*b2 + 2*B2*B6*a1**2*a2*b1**4 + 4*B2*a1**5*a2*b1 + 3*B4**2*a1**3*b1**3*b2 + 4*B4**2*a1**2*a2*b1**4 + 5*B4*B6*a1**2*b1**4*b2 + 4*B4*B6*a1*a2*b1**5 + 2*B4*a1**5*b1*b2 + 6*B4*a1**4*a2*b1**2 + 2*B6**2*a1*b1**5*b2 + B6**2*a2*b1**6 + 2*B6*a1**4*b1**2*b2 + 2*B6*a1**3*a2*b1**3 + 4*a1**6*a2),
 'sfCertA₂': ('B₂ B₄ B₆', 'SecantContentUniversal', -B2*a1**5*b1*b2 + 2*B2*a1**4*a2*b1**2 - 3*B4*a1**4*b1**2*b2 + 5*B4*a1**3*a2*b1**3 - 2*B6*a1**3*b1**3*b2 + 3*B6*a1**2*a2*b1**4 - 2*a1**6*b2 + 6*a1**5*a2*b1),
 'prCertA₁': ('B₄ B₆ B₈', 'SecantContentUniversal', B4**2*a1**4*a2*b1**2 + B4*B6*a1**4*b1**2*b2 + 4*B4*B6*a1**3*a2*b1**3 + B4*B8*a1**3*b1**3*b2 + 2*B4*B8*a1**2*a2*b1**4 + 3*B6**2*a1**3*b1**3*b2 + 4*B6**2*a1**2*a2*b1**4 + 5*B6*B8*a1**2*b1**4*b2 + 4*B6*B8*a1*a2*b1**5 + B6*a1**5*a2*b1 + 2*B8**2*a1*b1**5*b2 + B8**2*a2*b1**6 + B8*a1**4*a2*b1**2),
 'prCertA₂': ('B₄ B₆ B₈', 'SecantContentUniversal', B4*a1**5*b1*b2 - 2*B4*a1**4*a2*b1**2 + 3*B6*a1**4*b1**2*b2 - 5*B6*a1**3*a2*b1**3 + 2*B8*a1**3*b1**3*b2 - 3*B8*a1**2*a2*b1**4 + a1**6*a2),
}

def leanexp(e):
    return str(e).replace('**','^').replace('B2','B₂').replace('B4','B₄').replace('B6','B₆').replace('B8','B₈')

def gen_cert(name, bargs, poly):
    P = sp.Poly(sp.expand(poly), a1, b1, a2, b2)
    entries = []
    for mono, coef in zip(P.monoms(), P.coeffs()):
        i, j, k, l = mono
        assert i + j == 6 and k + l == 1
        c2 = 'a₂' if k == 1 else 'b₂'
        entries.append((leanexp(coef), i, j, c2))
    Sdef = " + ".join(f"|{q}|" for q,_,_,_ in entries)
    lines = []
    lines.append(f"def S{name} ({bargs} : ℤ) : ℤ :=\n  " + Sdef)
    lines.append("")
    lines.append(f"theorem S{name}_nonneg ({bargs} : ℤ) : 0 ≤ S{name} {bargs} := by")
    lines.append(f"  rw [S{name}]")
    lines.append("  repeat' apply add_nonneg")
    lines.append("  all_goals exact abs_nonneg _")
    lines.append("")
    lines.append(f"theorem abs_{name}_le ({bargs} a₁ b₁ a₂ b₂ : ℤ) :")
    lines.append(f"    |{name} {bargs} a₁ b₁ a₂ b₂|")
    lines.append(f"      ≤ S{name} {bargs} * (max |a₁| |b₁| ^ 6 * max |a₂| |b₂|) := by")
    lines.append("  have hM : (0:ℤ) ≤ max |a₁| |b₁| := le_trans (abs_nonneg a₁) (le_max_left _ _)")
    lines.append("  have hH : (0:ℤ) ≤ max |a₂| |b₂| := le_trans (abs_nonneg a₂) (le_max_left _ _)")
    lines.append("  have ha : |a₁| ≤ max |a₁| |b₁| := le_max_left _ _")
    lines.append("  have hb : |b₁| ≤ max |a₁| |b₁| := le_max_right _ _")
    lines.append("  have hA : |a₂| ≤ max |a₂| |b₂| := le_max_left _ _")
    lines.append("  have hB : |b₂| ≤ max |a₂| |b₂| := le_max_right _ _")
    for n,(q,i,j,c2) in enumerate(entries, 1):
        hc = 'hA' if c2 == 'a₂' else 'hB'
        lines.append(f"  have h{n} := abs_le.mp (term_bound ({q}) a₁ b₁ {c2} {i} {j} ha hb {hc} hM hH (by norm_num))")
    lines.append(f"  rw [{name}, S{name}, abs_le]")
    facts1 = ", ".join(f"h{n}.1" for n in range(1, len(entries)+1))
    facts2 = ", ".join(f"h{n}.2" for n in range(1, len(entries)+1))
    lines.append("  constructor")
    lines.append(f"  · linarith [{facts1}, {facts2}]")
    lines.append(f"  · linarith [{facts1}, {facts2}]")
    return "\n".join(lines)

blocks = [gen_cert(n, b, p) for n,(b,_,p) in CERTS.items()]
body = "\n\n".join(blocks)

open('PF_Lean4_Code/PF/SecantSizeLower_r197_gen.txt','w').write(body)
print("generated", len(body.splitlines()), "lines of cert bounds")
