#!/usr/bin/env python3
"""
smoke_r331b_box0.py — numerical smoke test for r331b box 0 pilot.

Determines whether a proposed u-panel partition of [1, 5] can produce a
finite-integral Route-A enclosure that, after §8 envelope subtraction,
satisfies the locked-in box 0 targets:

    Re Λ₀(σ+15i) ≥ Rlo = 2221/500000 ≈ 4.442·10⁻³   uniformly for σ ∈ [1/2, 9/16]
    |Im Λ₀(σ+15i)| ≤ 10⁻⁴                          uniformly for σ ∈ [1/2, 9/16]

The generator+Lean certification below will only be worth doing if this
smoke test finds a numerically viable partition.

NOT PROOF.  Purely exploratory numerics.

Usage:  python3 smoke_r331b_box0.py
"""
import mpmath as mp
from fractions import Fraction

mp.mp.dps = 60  # 60 decimal digits — ample for smoke test

# Fixed inputs
T15 = mp.mpf(15)
HALF_T15 = mp.mpf(15) / 2
N = 3                # omegaPartial N=3 terms
T = mp.mpf(5)        # tail truncation at u = 5
SIGMA_LO = mp.mpf(1) / 2
SIGMA_HI = mp.mpf(9) / 16

# §8 envelope constants
PI = mp.pi
DELTA_N = mp.exp(-PI * (N + 1)**2) / (1 - mp.exp(-PI))     # exp(-π·16)/(1-exp(-π))
TRUNC_ENVELOPE = 2 * (T - 1) * DELTA_N                       # 2·(T-1)·δ_N
TAIL_ENVELOPE = 2 / PI * mp.exp(-PI * T) / (1 - mp.exp(-PI))  # 2·exp(-πT)/(π·(1-exp(-π)))
ENVELOPE_LAMBDA = TRUNC_ENVELOPE + TAIL_ENVELOPE

def omega_partial(u):
    """omegaPartial 3 u = ∑_{n<3} exp(-π·(n+1)²·u) = e^(-πu) + e^(-4πu) + e^(-9πu)."""
    return sum(mp.exp(-PI * (n + 1)**2 * u) for n in range(N))

def theta_re_integrand(sigma, u):
    """(u^(σ/2-1) + u^((1-σ)/2-1)) · cos((15/2)·log u) · omegaPartial 3 u"""
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    return (mp.power(u, a) + mp.power(u, b)) * mp.cos(HALF_T15 * mp.log(u)) * omega_partial(u)

def theta_im_integrand(sigma, u):
    """(u^(σ/2-1) - u^((1-σ)/2-1)) · sin((15/2)·log u) · omegaPartial 3 u"""
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    return (mp.power(u, a) - mp.power(u, b)) * mp.sin(HALF_T15 * mp.log(u)) * omega_partial(u)

def theta_re_integrand_full(sigma, u):
    """Same but with true omega instead of omegaPartial — for cross-check."""
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    # omega u = ∑_{n≥1} exp(-π·n²·u), truncate at n=20 (huge overkill for smoke test)
    omega = sum(mp.exp(-PI * n**2 * u) for n in range(1, 21))
    return (mp.power(u, a) + mp.power(u, b)) * mp.cos(HALF_T15 * mp.log(u)) * omega

def theta_im_integrand_full(sigma, u):
    a = sigma / 2 - 1
    b = (1 - sigma) / 2 - 1
    omega = sum(mp.exp(-PI * n**2 * u) for n in range(1, 21))
    return (mp.power(u, a) - mp.power(u, b)) * mp.sin(HALF_T15 * mp.log(u)) * omega

# ----------------------------------------------------------------------
# Reference Lambda_0 values via true omega + tail
# ----------------------------------------------------------------------
def re_lambda0_full(sigma):
    """Numerical Re Λ₀(σ+15i) = ∫_{Ioi 1} realTheta with true ω, integrated to u=20."""
    return mp.quad(lambda u: theta_re_integrand_full(sigma, u), [1, 20])

def im_lambda0_full(sigma):
    return mp.quad(lambda u: theta_im_integrand_full(sigma, u), [1, 20])

# ----------------------------------------------------------------------
# Finite integral via truncated omegaPartial on [1, T]
# ----------------------------------------------------------------------
def re_finite_integral(sigma):
    """∫_{Ioc 1 T} realThetaN(σ, 15, u) du."""
    return mp.quad(lambda u: theta_re_integrand(sigma, u), [1, T])

def im_finite_integral(sigma):
    return mp.quad(lambda u: theta_im_integrand(sigma, u), [1, T])

# ----------------------------------------------------------------------
# Route-A panel enclosures at σ-endpoints
# ----------------------------------------------------------------------
def panel_range_re(sigma, u_lo, u_hi, samples=100):
    """Rough numerical min/max of theta_re_integrand(sigma, u) on [u_lo, u_hi]."""
    us = [u_lo + (u_hi - u_lo) * mp.mpf(k) / samples for k in range(samples + 1)]
    vals = [theta_re_integrand(sigma, u) for u in us]
    return min(vals), max(vals)

def panel_range_im(sigma, u_lo, u_hi, samples=100):
    us = [u_lo + (u_hi - u_lo) * mp.mpf(k) / samples for k in range(samples + 1)]
    vals = [theta_im_integrand(sigma, u) for u in us]
    return min(vals), max(vals)

def route_a_re_bound(sigma, panel_edges):
    """Route-A lower/upper bound of ∫_1^T realThetaN via panel min·width, max·width sums."""
    L = mp.mpf(0)
    U = mp.mpf(0)
    for i in range(len(panel_edges) - 1):
        u_lo = panel_edges[i]
        u_hi = panel_edges[i + 1]
        w = u_hi - u_lo
        mn, mx = panel_range_re(sigma, u_lo, u_hi)
        L += mn * w
        U += mx * w
    return L, U

def route_a_im_bound(sigma, panel_edges):
    L = mp.mpf(0)
    U = mp.mpf(0)
    for i in range(len(panel_edges) - 1):
        u_lo = panel_edges[i]
        u_hi = panel_edges[i + 1]
        w = u_hi - u_lo
        mn, mx = panel_range_im(sigma, u_lo, u_hi)
        L += mn * w
        U += mx * w
    return L, U

# ----------------------------------------------------------------------
# Smoke test at multiple panel counts
# ----------------------------------------------------------------------
def uniform_partition(n_panels):
    return [1 + mp.mpf(k) * (T - 1) / n_panels for k in range(n_panels + 1)]

def envelope_report():
    print("=" * 70)
    print("§8 envelope constants (N={}, T={})".format(N, float(T)))
    print("=" * 70)
    print("  delta_N = exp(-π·(N+1)²)/(1-exp(-π)) = {:.3e}".format(float(DELTA_N)))
    print("  truncation env  = 2·(T-1)·delta_N   = {:.3e}".format(float(TRUNC_ENVELOPE)))
    print("  tail env        = 2·exp(-πT)/(π·(1-exp(-π))) = {:.3e}".format(float(TAIL_ENVELOPE)))
    print("  TOTAL Λ₀ env    = {:.3e}".format(float(ENVELOPE_LAMBDA)))
    print()

def reference_report():
    print("=" * 70)
    print("Reference Λ₀ (true omega, high-precision quad)")
    print("=" * 70)
    for sigma in [SIGMA_LO, SIGMA_HI]:
        re_val = re_lambda0_full(sigma)
        im_val = im_lambda0_full(sigma)
        print("  σ = {}".format(sigma))
        print("    Re Λ₀ ≈ {:.12f}".format(float(re_val)))
        print("    Im Λ₀ ≈ {:.12f}".format(float(im_val)))
    print()
    print("  Target Rlo = 2221/500000 = {:.12f}".format(2221/500000))
    print("  Target |I| ≤ 1/10000    = {:.12f}".format(1/10000))
    print()

def finite_integral_report():
    print("=" * 70)
    print("Finite integral ∫_{{Ioc 1 T}} realThetaN at σ endpoints (high-prec quad)")
    print("=" * 70)
    for sigma in [SIGMA_LO, SIGMA_HI]:
        re_val = re_finite_integral(sigma)
        im_val = im_finite_integral(sigma)
        print("  σ = {}".format(sigma))
        print("    ∫ realThetaReN = {:.12f}".format(float(re_val)))
        print("    ∫ realThetaImN = {:.12f}".format(float(im_val)))
        # After §8 envelope subtraction:
        print("    Re Λ₀ ≥ ∫ - env = {:.12f}   (need ≥ {:.6f})".format(
            float(re_val - ENVELOPE_LAMBDA), 2221/500000))
        print("    |Im Λ₀| ≤ |∫| + env = {:.12f}   (need ≤ {:.6f})".format(
            float(abs(im_val) + ENVELOPE_LAMBDA), 1/10000))
    print()

def route_a_report(n_panels):
    edges = uniform_partition(n_panels)
    print("=" * 70)
    print("Route-A panel bound with {} uniform u-panels on [1, {}]"
          .format(n_panels, int(T)))
    print("=" * 70)
    for sigma in [SIGMA_LO, SIGMA_HI]:
        L_re, U_re = route_a_re_bound(sigma, edges)
        L_im, U_im = route_a_im_bound(sigma, edges)
        print("  σ = {}".format(sigma))
        print("    ∫ realThetaReN ∈ [{:.9f}, {:.9f}]  (width {:.3e})".format(
            float(L_re), float(U_re), float(U_re - L_re)))
        print("    ∫ realThetaImN ∈ [{:.9f}, {:.9f}]  (width {:.3e})".format(
            float(L_im), float(U_im), float(U_im - L_im)))
        # After envelope
        re_lo_final = L_re - ENVELOPE_LAMBDA
        re_hi_final = U_re + ENVELOPE_LAMBDA
        im_lo_final = L_im - ENVELOPE_LAMBDA
        im_hi_final = U_im + ENVELOPE_LAMBDA
        print("    Re Λ₀ ∈ [{:.9f}, {:.9f}]   need ≥ {:.6f}"
              .format(float(re_lo_final), float(re_hi_final), 2221/500000))
        pass_re = re_lo_final >= mp.mpf(2221) / 500000
        print("      PASS Re" if pass_re else "      ✗ FAIL Re (margin {:.3e})".format(
            float(mp.mpf(2221)/500000 - re_lo_final)))
        print("    Im Λ₀ ∈ [{:.9f}, {:.9f}]   need |·| ≤ {:.6f}"
              .format(float(im_lo_final), float(im_hi_final), 1/10000))
        pass_im = (im_lo_final >= -mp.mpf(1)/10000 and im_hi_final <= mp.mpf(1)/10000)
        print("      PASS Im" if pass_im else "      ✗ FAIL Im")
    print()

# ----------------------------------------------------------------------
# Midpoint quadrature with post-hoc numerical error estimate.
# The Lean proof will use composite_midpoint_error from XiQuadrature
# (∫ - Σ f(mid)·w ≤ (b-a)³/24 · max|f''|/n²), but here we just
# NUMERICALLY estimate the max|f''| and the resulting error bound.
# ----------------------------------------------------------------------
def midpoint_estimate_re(sigma, panel_edges):
    """Numerical midpoint sum for realThetaReN."""
    total = mp.mpf(0)
    for i in range(len(panel_edges) - 1):
        u_lo = panel_edges[i]
        u_hi = panel_edges[i + 1]
        mid = (u_lo + u_hi) / 2
        total += theta_re_integrand(sigma, mid) * (u_hi - u_lo)
    return total

def midpoint_estimate_im(sigma, panel_edges):
    total = mp.mpf(0)
    for i in range(len(panel_edges) - 1):
        u_lo = panel_edges[i]
        u_hi = panel_edges[i + 1]
        mid = (u_lo + u_hi) / 2
        total += theta_im_integrand(sigma, mid) * (u_hi - u_lo)
    return total

def max_abs_f_dd_re(sigma, n_samples=1000):
    """Numerical max |f''| for realThetaReN(σ, ·) on [1, T]."""
    # Central difference with small h
    h = mp.mpf('1e-5')
    us = [1 + mp.mpf(k)/n_samples * (T - 1) for k in range(n_samples + 1)]
    max_abs = mp.mpf(0)
    for u in us:
        # 5-point stencil
        f_pp = (theta_re_integrand(sigma, u + h) - 2*theta_re_integrand(sigma, u) + theta_re_integrand(sigma, u - h)) / (h*h)
        if abs(f_pp) > max_abs:
            max_abs = abs(f_pp)
    return max_abs

def max_abs_f_dd_im(sigma, n_samples=1000):
    h = mp.mpf('1e-5')
    us = [1 + mp.mpf(k)/n_samples * (T - 1) for k in range(n_samples + 1)]
    max_abs = mp.mpf(0)
    for u in us:
        f_pp = (theta_im_integrand(sigma, u + h) - 2*theta_im_integrand(sigma, u) + theta_im_integrand(sigma, u - h)) / (h*h)
        if abs(f_pp) > max_abs:
            max_abs = abs(f_pp)
    return max_abs

def midpoint_report(n_panels, M_re, M_im):
    """Report midpoint sum + composite midpoint error estimate."""
    edges = uniform_partition(n_panels)
    # composite midpoint error ≤ (b-a)³ · max|f''| / (24·n²)
    err_re = (T - 1)**3 * M_re / (24 * n_panels**2)
    err_im = (T - 1)**3 * M_im / (24 * n_panels**2)
    print("=" * 70)
    print("Midpoint rule with {} uniform u-panels on [1, {}]  (estimated errors)"
          .format(n_panels, int(T)))
    print("  midpoint error bound  ~  (b-a)³·max|f''| / (24·n²)")
    print("    max|f''_Re| ≈ {:.3e} (numerical estimate) → err ≈ {:.3e}"
          .format(float(M_re), float(err_re)))
    print("    max|f''_Im| ≈ {:.3e} → err ≈ {:.3e}"
          .format(float(M_im), float(err_im)))
    print("=" * 70)
    for sigma in [SIGMA_LO, SIGMA_HI]:
        mid_re = midpoint_estimate_re(sigma, edges)
        mid_im = midpoint_estimate_im(sigma, edges)
        # Full enclosure: [mid - err, mid + err], then + §8 envelope for Λ₀
        re_lo_final = mid_re - err_re - ENVELOPE_LAMBDA
        re_hi_final = mid_re + err_re + ENVELOPE_LAMBDA
        im_lo_final = mid_im - err_im - ENVELOPE_LAMBDA
        im_hi_final = mid_im + err_im + ENVELOPE_LAMBDA
        print("  σ = {}".format(sigma))
        print("    midpoint ∫ Re = {:.12f}".format(float(mid_re)))
        print("    midpoint ∫ Im = {:.12f}".format(float(mid_im)))
        print("    Re Λ₀ ∈ [{:.9f}, {:.9f}]   need ≥ {:.6f}"
              .format(float(re_lo_final), float(re_hi_final), 2221/500000))
        pass_re = re_lo_final >= mp.mpf(2221) / 500000
        print("      PASS Re" if pass_re else "      ✗ FAIL Re (margin {:.3e})".format(
            float(mp.mpf(2221)/500000 - re_lo_final)))
        print("    Im Λ₀ ∈ [{:.9f}, {:.9f}]   need |·| ≤ {:.6f}"
              .format(float(im_lo_final), float(im_hi_final), 1/10000))
        pass_im = (im_lo_final >= -mp.mpf(1)/10000 and im_hi_final <= mp.mpf(1)/10000)
        print("      PASS Im" if pass_im else "      ✗ FAIL Im")
    print()

if __name__ == "__main__":
    envelope_report()
    reference_report()
    finite_integral_report()
    print("=" * 70)
    print("PART A — ROUTE A (panel min/max × width)")
    print("=" * 70)
    for n_panels in [32, 64, 128, 256]:
        route_a_report(n_panels)
    print("=" * 70)
    print("PART B — MIDPOINT RULE (needs certified max|f''| bound in Lean)")
    print("=" * 70)
    print("Estimating max|f''| numerically at σ = 1/2 and σ = 9/16 ...")
    M_re = max(max_abs_f_dd_re(SIGMA_LO), max_abs_f_dd_re(SIGMA_HI))
    M_im = max(max_abs_f_dd_im(SIGMA_LO), max_abs_f_dd_im(SIGMA_HI))
    print("  max|f''_Re| (numerical) ≈ {:.3e}".format(float(M_re)))
    print("  max|f''_Im| (numerical) ≈ {:.3e}".format(float(M_im)))
    print()
    for n_panels in [32, 64, 128, 256, 512]:
        midpoint_report(n_panels, M_re, M_im)

    # PART C — Log-adaptive partition (concentrate near u=1 where f'' is large)
    print("=" * 70)
    print("PART C — LOG-ADAPTIVE PARTITION (dense near u=1)")
    print("=" * 70)
    def log_adaptive_partition(n_panels):
        """u_k = 1 + (T-1)·((exp(β·k/n) - 1)/(exp(β) - 1)) with β = 4."""
        beta = mp.mpf(4)
        return [mp.mpf(1) + (T - 1) * (mp.exp(beta * mp.mpf(k) / n_panels) - 1) / (mp.exp(beta) - 1)
                for k in range(n_panels + 1)]

    def midpoint_adaptive_report(n_panels):
        """Midpoint on log-adaptive partition; error estimated per-panel."""
        edges = log_adaptive_partition(n_panels)
        h = mp.mpf('1e-5')
        # per-panel error using per-panel local max|f''|
        def local_max_f_dd_re(u_lo, u_hi, samples=20):
            us = [u_lo + (u_hi - u_lo) * mp.mpf(k)/samples for k in range(samples + 1)]
            return max(abs((theta_re_integrand(SIGMA_LO, u + h) - 2*theta_re_integrand(SIGMA_LO, u) + theta_re_integrand(SIGMA_LO, u - h)) / (h*h)) for u in us)
        def local_max_f_dd_im(u_lo, u_hi, samples=20):
            us = [u_lo + (u_hi - u_lo) * mp.mpf(k)/samples for k in range(samples + 1)]
            return max(abs((theta_im_integrand(SIGMA_HI, u + h) - 2*theta_im_integrand(SIGMA_HI, u) + theta_im_integrand(SIGMA_HI, u - h)) / (h*h)) for u in us)
        err_re = mp.mpf(0)
        err_im = mp.mpf(0)
        for i in range(len(edges) - 1):
            u_lo = edges[i]; u_hi = edges[i + 1]
            w = u_hi - u_lo
            M_re_local = local_max_f_dd_re(u_lo, u_hi)
            M_im_local = local_max_f_dd_im(u_lo, u_hi)
            err_re += w**3 * M_re_local / 24
            err_im += w**3 * M_im_local / 24
        print("=" * 70)
        print("Log-adaptive midpoint, {} panels, sum of per-panel bounds:".format(n_panels))
        print("  err_Re ≈ {:.3e}  (need ≤ ~4·10⁻⁶ for pilot)".format(float(err_re)))
        print("  err_Im ≈ {:.3e}".format(float(err_im)))
        for sigma in [SIGMA_LO, SIGMA_HI]:
            mid_re = midpoint_estimate_re(sigma, edges)
            mid_im = midpoint_estimate_im(sigma, edges)
            re_lo_final = mid_re - err_re - ENVELOPE_LAMBDA
            im_hi_final = mid_im + err_im + ENVELOPE_LAMBDA
            im_lo_final = mid_im - err_im - ENVELOPE_LAMBDA
            print("  σ = {}: midpoint ∫Re = {:.9f}, Λ₀ Re lo = {:.9f}   (need ≥ {:.6f})".format(
                sigma, float(mid_re), float(re_lo_final), 2221/500000))
            pass_re = re_lo_final >= mp.mpf(2221) / 500000
            print("      {}".format("PASS Re" if pass_re else "✗ FAIL Re margin {:.3e}".format(float(mp.mpf(2221)/500000 - re_lo_final))))
            pass_im = (im_lo_final >= -mp.mpf(1)/10000 and im_hi_final <= mp.mpf(1)/10000)
            print("  σ = {}: Im ∈ [{:.9f}, {:.9f}]  {}".format(
                sigma, float(im_lo_final), float(im_hi_final),
                "PASS Im" if pass_im else "✗ FAIL Im"))
        print()
    for n_panels in [128, 256, 512, 1024]:
        midpoint_adaptive_report(n_panels)
