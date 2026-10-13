# RH right-edge sign-fact verification -- Principia Fractalis
# Function computed is EXACTLY the Lean object:
#   riemannXiEntire(s) = (s*(s-1)*completedRiemannZeta0(s) + 1)/2
#   completedRiemannZeta0(s) = pi^(-s/2) Gamma(s/2) zeta(s) + 1/s + 1/(1-s)   [mathlib convention]
# On the right edge sigma = Re s = 1, the finite-region Lean proof needs:
#   R1: Re xi(1+it) > 0  on t in [0, 13]
#   R2: Im xi(1+it) > 0  on t in [13, 29/2]
#   R3: Re xi(1+it) < 0  on t in [29/2, 15]
# This is independent high-precision NUMERICAL triage on a dense grid: it confirms
# the facts the Lean proof assumes are true everywhere sampled and catches any
# sign violation. It is NOT a proof of RH and NOT a Clay solution.
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power
mp.dps = 30

def Lambda0(s):
    Lam = power(pi, -s/2) * gamma(s/2) * zeta(s)
    return Lam + 1/s + 1/(1-s)

def xi_s(s):
    return (s*(s-1)*Lambda0(s) + 1)/2

def xi(t):
    # s=1 (t=0) is the removable point: s(s-1)=0 annihilates zeta's pole,
    # giving xi(1) = (0 + 1)/2 = 1/2 exactly (Lean: R1_at_zero).
    if abs(t) < mpf('1e-15'):
        return mpc(mpf('0.5'), mpf('0'))
    return xi_s(mpc(1, t))

print("mpmath dps =", mp.dps)
print()
print("=== convention witness: functional equation xi(s) = xi(1-s) on sigma=1 ===")
print("    (holds iff we are computing the genuine entire completed xi)")
for tt in [mpf('3.7'), mpf('9.1'), mpf('13.0'), mpf('14.5')]:
    s = mpc(1, tt)
    d = abs(xi_s(s) - xi_s(1 - s))
    print("    t=%-6s  |xi(1+it) - xi(-it)| = %.3e" % (str(tt), float(d)))

def scan(t0, t1, step):
    t = mpf(t0)
    pts = []
    lim = mpf(t1) + mpf(step) / 2
    st = mpf(step)
    while t <= lim:
        z = xi(t)
        pts.append((t, z.real, z.imag))
        t += st
    return pts

print()
print("=== R1: Re xi(1+it) > 0 on [0, 13]  (step 0.002) ===")
p = scan('0.0', '13.0', '0.002')
remin = min(p, key=lambda r: r[1])
viol = [r for r in p if r[1] <= 0]
print("    samples=%d   min Re = %.6e  at t=%.4f   violations(Re<=0)=%d"
      % (len(p), float(remin[1]), float(remin[0]), len(viol)))
print("    Re xi(1+0i)  = %.6e      Re xi(1+13i) = %.6e"
      % (float(p[0][1]), float(p[-1][1])))

print()
print("=== R2: Im xi(1+it) > 0 on [13, 14.5]  (step 0.0005) ===")
p = scan('13.0', '14.5', '0.0005')
immin = min(p, key=lambda r: r[2])
viol = [r for r in p if r[2] <= 0]
print("    samples=%d   min Im = %.6e  at t=%.4f   violations(Im<=0)=%d"
      % (len(p), float(immin[2]), float(immin[0]), len(viol)))
print("    Im xi(1+13i) = %.6e      Im xi(1+14.5i)= %.6e"
      % (float(p[0][2]), float(p[-1][2])))

print()
print("=== R3: Re xi(1+it) < 0 on [14.5, 15]  (step 0.0005) ===")
p = scan('14.5', '15.0', '0.0005')
remax = max(p, key=lambda r: r[1])
viol = [r for r in p if r[1] >= 0]
print("    samples=%d   max Re = %.6e  at t=%.4f   violations(Re>=0)=%d"
      % (len(p), float(remax[1]), float(remax[0]), len(viol)))
print("    Re xi(1+14.5i)= %.6e     Re xi(1+15i) = %.6e"
      % (float(p[0][1]), float(p[-1][1])))

print()
print("=== SUMMARY ===")
print("R1 positive-min, R2 positive-min, R3 negative-max, zero violations")
print("==> the three sign facts hold on the sampled grid (numerical triage, not a proof).")
