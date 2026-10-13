# Centered / mean-value RH box march with Arb power series (python-flint).
# Mean value: f(t) in f(c) + f'(box)*[-r,r], exact (no 2nd order). We get:
#   f(c)      : evaluate xi(1+ic) at the POINT c (zero-radius ball) -> tight.
#   f'(box)   : the x^1 coefficient of xi(1 + i(t_ball + x)) with t_ball=arb(c,r),
#               an acb_series -> a rigorous ball enclosing f' over the whole box.
# This kills the cancellation/dependency loss that made the DIRECT ball march give
# R2=867 boxes. pi^(-S/2) via exp(-S/2 * log pi) to avoid series '**'.
from flint import ctx, arb, acb, acb_series
ctx.prec = 180
ctx.cap = 2                      # series length: constant + linear (f and f')
PI = arb.pi()

def _xi_series(t_center, t_rad):
    # S = 1 + i*(t_center_ball + x), x the series variable
    tb = arb(t_center, t_rad)
    s0 = acb(arb(1), tb)
    S = acb_series([s0, acb(0, 1)])           # s0 + i*x
    half = S / 2
    logpi = acb_series([acb(PI)]).log()        # constant series log(pi)
    G = (-half * logpi).exp() * half.gamma()   # pi^(-S/2) * Gamma(S/2)
    L0 = G * S.zeta() + 1/S + 1/(1 - S)
    XI = (S * (S - 1) * L0 + 1) / 2
    return XI                                  # XI[0]=xi over box-ball, XI[1]=d/dt xi

def cert(c, r, which, sign):
    # tight value at the center point
    XIc = _xi_series(c, 0.0)
    fc = XIc[0].real if which == 're' else XIc[0].imag
    # derivative enclosure over the whole box
    XIb = _xi_series(c, r)
    fp = XIb[1].real if which == 're' else XIb[1].imag
    M = abs(fp)                                # ball; its upper bound bounds |f'| on box
    span = M * arb(r)                          # first-order variation bound
    if sign > 0:
        return (fc - span) > 0                 # rigorous: whole box f > 0
    else:
        return (fc + span) < 0

def march(a, b, which, sign, label, cap=20000):
    xf = float(a); bf = float(b); boxes = 0; minr = 1e9; maxr = 0.0
    while xf < bf - 1e-12:
        rem = bf - xf
        if cert(xf + rem/2, rem/2, which, sign):
            h = rem
        else:
            lo, hi = 0.0, rem
            for _ in range(48):
                mid = (lo + hi)/2
                if cert(xf + mid/2, mid/2, which, sign): lo = mid
                else: hi = mid
            h = lo
        if h < 1e-9:
            print("  %-10s STUCK at t=%.6f" % (label, xf)); return None
        boxes += 1; r = h/2; minr = min(minr, r); maxr = max(maxr, r); xf += h
        if boxes > cap:
            print("  %-10s exceeded cap" % label); return None
    print("  %-10s %5d certified boxes over [%s,%s]  (radius %.2e .. %.2e)"
          % (label, boxes, a, b, minr, maxr))
    return boxes

print("centered/mean-value Arb march, prec=%d cap=%d" % (ctx.prec, ctx.cap))
# R1 starts at 0.05: [0,0.05] is covered by the proven R1_on_neighborhood theorem,
# and t=0 is the removable 1/(1-s) pole the direct form chokes on.
b1 = march(0.05, 13, 're', +1, "R1 Re>0")
b2 = march(13, 14.5, 'im', +1, "R2 Im>0")
b3 = march(14.5, 15, 're', -1, "R3 Re<0")
if None not in (b1, b2, b3):
    print()
    print("TOTAL centered-form certified boxes = %d  (direct ball march: R2 alone was 867;"
          " naive theta-generator: 232)" % (b1 + b2 + b3))
    print("Rigorous (Arb ball arithmetic). Certifies R1/R2/R3 as a campaign sim; NOT a Lean")
    print("proof and NOT progress on the open Riemann Hypothesis (finite rectangle, known).")
