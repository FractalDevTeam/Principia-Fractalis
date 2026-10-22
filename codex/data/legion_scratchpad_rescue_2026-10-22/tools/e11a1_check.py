from fractions import Fraction as F

# 11a1 : y^2 + y = x^3 - x^2   ->  a1=0, a2=-1, a3=1, a4=0, a6=0
a1, a2, a3, a4, a6 = 0, -1, 1, 0, 0

def on_curve(P):
    if P is None: return True
    x, y = P
    return y*y + a1*x*y + a3*y == x**3 + a2*x*x + a4*x + a6

def negY(x, y):  return -y - a1*x - a3

def neg(P):
    if P is None: return None
    x, y = P
    return (x, negY(x, y))

def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2:
        if y1 == negY(x2, y2):          # P = -Q
            return None
        # doubling
        lam = F(3*x1*x1 + 2*a2*x1 + a4 - a1*y1, 2*y1 + a1*x1 + a3)
    else:
        lam = F(y2 - y1, x2 - x1)
    mu = y1 - lam*x1
    x3 = lam*lam + a1*lam - a2 - x1 - x2
    y3 = -(lam + a1)*x3 - mu - a3
    return (x3, y3)

P = (F(0), F(0))
print("11a1 : y^2 + y = x^3 - x^2      a = (0,-1,1,0,0)")
print("P = (0,0) on curve:", on_curve(P))
print()
print("multiples of P:")
Q = P
for n in range(1, 8):
    print("  %d*P = %s   on_curve=%s" % (n, "O" if Q is None else str(Q), on_curve(Q)))
    if Q is None:
        print("  --> order of P is", n)
        break
    Q = add(Q, P)

print()
print("the full rational torsion of 11a1 (expected Z/5):")
pts = [None]
Q = P
while Q is not None:
    pts.append(Q); Q = add(Q, P)
print("  #points found in <P> =", len(pts))
for q in pts:
    print("   ", "O" if q is None else q)

print()
print("doubling data needed for Lean:")
print("  negY 0 0 =", negY(F(0), F(0)))
print("  2P =", add(P, P))
print("  slope at P =", F(3*0*0 + 2*a2*0 + a4 - a1*0, 2*0 + a1*0 + a3))
print()
print("NOTE: rank(11a1) = 0 is CLASSICAL (needs descent / upper bound);")
print("      nothing here proves it, and the template proves only rank >= 1,")
print("      which is FALSE for this curve.")
