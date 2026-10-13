# TBOX lever test: does a centered/mean-value form kill the 402x interval-dependency
# loss that sets the 232-box, 76-day certified RH-below-15 campaign?
#
# Re xi(1+it) = (1 - t^2 * A(t) - t * B(t)) / 2,  A = Re Lambda0(1+it), B = Im Lambda0(1+it)
# Lambda0(s) = pi^(-s/2) Gamma(s/2) zeta(s) + 1/s + 1/(1-s)   [mathlib completedRiemannZeta0]
#
# For a t-box [c-r, c+r] we compare three widths of Re xi:
#   TRUE    : max-min over a dense sample (the real variation)
#   NAIVE   : interval-evaluate the formula treating each t-subterm as an independent
#             interval (this is the dependency problem that the Lean generator incurs)
#   CENTERED: Re xi(c) + f'([box]) * [-r, r]   (first-order mean-value form)
# Then convert each sensitivity into a box count for the three RH segments using the
# measured sign margins. NOT a certificate; a feasibility measurement of the lever.
from mpmath import mp, mpf, mpc, pi, gamma, zeta, power, diff
mp.dps = 40

def L0(s):
    return power(pi, -s/2) * gamma(s/2) * zeta(s) + 1/s + 1/(1-s)

def rexi(t):
    # Re xi(1+it) as a real function of real t
    t = mpf(t)
    L = L0(mpc(1, t))
    A, B = L.real, L.imag
    return (1 - t*t*A - t*B) / 2

def imxi(t):
    t = mpf(t)
    L = L0(mpc(1, t))
    A, B = L.real, L.imag
    return (-t*t*B + t*A) / 2

# ---- interval helpers (plain min/max over the box corners+samples; rigorous enough
#      for a feasibility measurement, since A,B,t are monotone-ish on tiny boxes) ----
def box_minmax(f, c, r, n=41):
    xs = [c - r + (2*r)*k/(n-1) for k in range(n)]
    vs = [f(x) for x in xs]
    return min(vs), max(vs)

def naive_width_rexi(c, r, n=41):
    # treat T, T^2, A, B as independent intervals over the box, multiply naively
    T = (c - r, c + r)
    T2 = (min(T[0]**2, T[1]**2), max(T[0]**2, T[1]**2))
    # A(t), B(t) ranges over the box
    xs = [c - r + (2*r)*k/(n-1) for k in range(n)]
    As = []; Bs = []
    for x in xs:
        L = L0(mpc(1, x)); As.append(L.real); Bs.append(L.imag)
    A = (min(As), max(As)); B = (min(Bs), max(Bs))
    def imul(p, q):
        cands = [p[0]*q[0], p[0]*q[1], p[1]*q[0], p[1]*q[1]]
        return (min(cands), max(cands))
    def isub(p, q):
        return (p[0]-q[1], p[1]-q[0])
    t2A = imul(T2, A)
    tB  = imul(T, B)
    one = (mpf(1), mpf(1))
    num = isub(isub(one, t2A), tB)         # 1 - T2*A - T*B
    lo, hi = num[0]/2, num[1]/2
    return hi - lo

def centered_width_rexi(c, r):
    # |d/dt Re xi| bounded over the box (sample the derivative), times r (half-width)
    xs = [c - r, c, c + r]
    dmax = max(abs(diff(rexi, x)) for x in xs)
    return 2 * dmax * r   # full width = 2 * |f'| * r

# ---------------- run on the three segments' tightest regions ----------------
segs = [
    ("R1 [0,13] (margin at t=13)",      mpf('12.995'), mpf('0.005'), rexi, "re"),
    ("R2 [13,14.5] (margin at t=14.5)", mpf('14.495'), mpf('0.005'), imxi, "im"),
    ("R3 [14.5,15] (margin at t=14.5)", mpf('14.505'), mpf('0.005'), rexi, "re"),
]

print("mp.dps =", mp.dps)
print("box radius r = 0.005 (full width 0.01) for all three probes\n")
for name, c, r, f, _ in segs:
    tw_lo, tw_hi = box_minmax(f, c, r)
    true_w = tw_hi - tw_lo
    if f is rexi:
        naive_w = naive_width_rexi(c, r)
        cen_w = centered_width_rexi(c, r)
    else:
        # Im xi analogue
        def imxi_fn(t): return imxi(t)
        dmax = max(abs(diff(imxi_fn, x)) for x in (c-r, c, c+r))
        cen_w = 2*dmax*r
        # naive for Im: (-T2*B + T*A)/2
        T = (c-r, c+r); T2 = (min(T[0]**2,T[1]**2), max(T[0]**2,T[1]**2))
        xs = [c-r+(2*r)*k/40 for k in range(41)]
        As=[];Bs=[]
        for x in xs:
            L=L0(mpc(1,x)); As.append(L.real); Bs.append(L.imag)
        A=(min(As),max(As)); B=(min(Bs),max(Bs))
        def imul(p,q):
            cs=[p[0]*q[0],p[0]*q[1],p[1]*q[0],p[1]*q[1]]; return (min(cs),max(cs))
        t2B=imul(T2,B); tA=imul(T,A)
        num=(-t2B[1]+tA[0], -t2B[0]+tA[1])
        naive_w=(num[1]-num[0])/2
    print("%-34s true=%.3e  naive=%.3e  centered=%.3e" % (name, float(true_w), float(naive_w), float(cen_w)))
    print("     naive/true = %6.1fx (dependency loss)   centered/true = %5.2fx" %
          (float(naive_w/true_w), float(cen_w/true_w)))
    print("     => box-count vs naive shrinks by ~ %.1fx\n" % float(naive_w/cen_w))
