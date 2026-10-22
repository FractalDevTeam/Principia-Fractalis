import sympy as sp

a, b, x = sp.symbols('a b x', integer=True)

# duplication forms for y^2 = x^3 - 2 :  x(2P) = f(x)/g(x), f = x^4+16x, g = 4x^3-8
# homogenised with x = a/b :  F/D with
F = a**4 + 16*a*b**3
D = 4*a**3*b - 8*b**4
print("F =", sp.expand(F))
print("D =", sp.expand(D))
print()

# --- sanity: matches the chapter's 2P at (3,5) ---
print("F(3,1)/D(3,1) =", sp.Rational(int(F.subs({a:3,b:1})), int(D.subs({a:3,b:1}))), " (expect 129/100)")
print()

# --- resultant of the two quartic forms ---
Fx = sp.Poly(F.subs({a: x, b: 1}), x)
Dx = sp.Poly(D.subs({a: x, b: 1}), x)
R = sp.resultant(Fx, Dx)
print("Res_x(F(x,1), D(x,1)) =", R, " = ", sp.factor(R))
print("  discriminant of y^2=x^3-2:  -16*(4*0^3+27*(-2)^2) =", -16*(27*4))
print()

# --- Bezout, dehomogenised in a (b=1) ---
g1, p1, q1 = sp.gcdex(Fx.as_expr(), Dx.as_expr(), x)
# sympy gcdex returns (s,t,h) with s*f + t*g = h  (ordering varies) -> normalise
s, t, h = sp.gcdex(Fx.as_expr(), Dx.as_expr(), x)
chk = sp.expand(s*Fx.as_expr() + t*Dx.as_expr() - h)
print("gcdex check (should be 0):", sp.simplify(chk), "   h =", h)
# clear denominators
den = sp.lcm([sp.denom(sp.together(c)) for c in [sp.simplify(s), sp.simplify(t)]])
S = sp.expand(sp.simplify(s)*den); T = sp.expand(sp.simplify(t)*den)
print("  S*F + T*D =", sp.expand(S*Fx.as_expr()+T*Dx.as_expr()), " (constant =", den, "* h )")
print("  S =", S)
print("  T =", T)
print()

# --- the key arithmetic fact: which primes can divide gcd(F,D) ---
# p | a  branch:  p | 4*(a^3-2b^3) and p|a, gcd(a,b)=1  =>  p | 8b^3 => p | 8 => p=2
# p ! a branch:  p | a^3+16b^3 and p | a^3-2b^3  => p | 18b^3 => p | 18 => p in {2,3}
print("prime-support argument: every prime divisor of gcd(F,D) lies in {2,3}")
print("  (p|a: p | 8b^3 ; p!a: subtract to get p | 18b^3)")
print()

# --- measure the actual gcd over many coprime pairs, to see the true bound ---
import math
mx = 0; arg = None
for A in range(-60, 61):
    for B in range(1, 61):
        if math.gcd(A, B) != 1: continue
        FA = A**4 + 16*A*B**3
        DA = 4*A**3*B - 8*B**4
        if FA == 0 and DA == 0: continue
        gg = math.gcd(FA, DA)
        if gg > mx:
            mx = gg; arg = (A, B, FA, DA)
print("max gcd(F,D) over coprime |a|<=60, 1<=b<=60:", mx, " at (a,b,F,D) =", arg)
print("  factored:", sp.factorint(mx) if mx else None)
print()

# --- the orbit of x=3 under x -> f/g, exact rationals, with naive heights ---
def step(q):
    return (q**4 + 16*q) / (4*q**3 - 8)
q = sp.Rational(3)
print("orbit of x=3 under the duplication map (naiveHeight = max(|num|,den)):")
for n in range(6):
    H = max(abs(sp.numer(q)), abs(sp.denom(q)))
    print("  n=%d  H=%-28s  x=%s" % (n, H, q if len(str(q)) < 60 else str(q)[:57]+"..."))
    q = sp.nsimplify(step(q))
    q = sp.Rational(sp.numer(q), sp.denom(q))
