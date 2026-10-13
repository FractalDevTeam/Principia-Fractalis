# Certified RH-below-15 box march with Arb (python-flint) ball arithmetic.
# RIGOROUS: an arb comparison (ball > 0) is True only if the WHOLE ball is > 0.
# For each right-edge segment we grow each t-box as wide as Arb can still certify
# the required sign, and count the certified boxes. This is the real campaign
# simulation -> the actual certified box count, vs the naive generator's 232.
#
#   Re xi(1+it) = Re of (s(s-1)Lambda0(s)+1)/2,  s=1+it
#   Lambda0(s) = pi^(-s/2) Gamma(s/2) zeta(s) + 1/s + 1/(1-s)   (mathlib conv.)
#   R1: Re xi > 0 on [0,13]   R2: Im xi > 0 on [13,29/2]   R3: Re xi < 0 on [29/2,15]
import subprocess, sys
subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", "python-flint"])
from flint import ctx, arb, acb
ctx.prec = 160  # bits

# --- diagnostics: confirm the ball constructor semantics (repr shows [mid +/- rad]) ---
tb = arb(0.5, 0.25)
print("python-flint OK. prec=%d bits. test ball arb(0.5,0.25) =" % ctx.prec, tb,
      "| >0 rigorously?", tb > 0, "| >0.3?", tb > arb('0.3'))

PI = arb.pi()

def xi_ball(tmid, trad):
    t = arb(tmid, trad)              # ball: midpoint tmid, radius trad
    s = acb(arb(1), t)               # s = 1 + i t
    half = s / 2
    G = acb(PI) ** (-half) * half.gamma()     # pi^(-s/2) Gamma(s/2)
    L0 = G * s.zeta() + 1/s + 1/(1 - s)
    xi = (s * (s - 1) * L0 + 1) / 2
    return xi.real, xi.imag

def re_pos(c, r): re, im = xi_ball(c, r); return re > 0
def im_pos(c, r): re, im = xi_ball(c, r); return im > 0
def re_neg(c, r): re, im = xi_ball(c, r); return re < 0

def march(a, b, ok, label, cap=5000):
    xf = float(a); bf = float(b); boxes = 0; minr = 1e9; maxr = 0.0
    while xf < bf - 1e-12:
        rem = bf - xf
        # largest h in (0, rem] s.t. box [xf, xf+h] certifies the sign
        if ok(xf + rem/2, rem/2):
            h = rem
        else:
            lo, hi = 0.0, rem
            for _ in range(50):
                mid = (lo + hi) / 2
                if ok(xf + mid/2, mid/2): lo = mid
                else: hi = mid
            h = lo
        if h < 1e-9:
            print("  %-10s STUCK at t=%.6f (box -> 0)" % (label, xf)); return None
        boxes += 1; r = h/2; minr = min(minr, r); maxr = max(maxr, r); xf += h
        if boxes > cap:
            print("  %-10s exceeded cap %d" % (label, cap)); return None
    print("  %-10s %4d certified boxes over [%s,%s]  (box radius %.2e .. %.2e)"
          % (label, boxes, a, b, minr, maxr))
    return boxes

re0, im0 = xi_ball(14.5, 0.0)
print("spot: Re xi(1+14.5i) =", re0, " Im =", im0)
print()
print("=== certified Arb box march (rigorous sign over each whole box) ===")
b1 = march(0, 13, re_pos, "R1 Re>0")
b2 = march(13, 14.5, im_pos, "R2 Im>0")
b3 = march(14.5, 15, re_neg, "R3 Re<0")
if None not in (b1, b2, b3):
    print()
    print("TOTAL certified boxes [0,15] = %d   (naive theta-generator was 232)" % (b1+b2+b3))
    print("Each box = ONE direct Arb xi evaluation; the naive count was an interval-")
    print("dependency artifact, not the mathematics. This is a certified campaign sim,")
    print("NOT a Lean proof and NOT progress on the open Riemann Hypothesis.")
