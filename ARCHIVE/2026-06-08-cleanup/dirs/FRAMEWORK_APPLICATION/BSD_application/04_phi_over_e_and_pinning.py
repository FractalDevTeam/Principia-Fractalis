"""
BSD Application — Step 4
Two final probes:

  (A) Where does φ/e plausibly live inside the framework's BSD operator?
      It is *claimed* (Ch 24) to be a 'distinguished eigenvalue'.
      We check whether any natural framework construction at α=3π/4
      lands at φ/e.

  (B) The pinning identity  α_BSD = (π/2)·α_RH = (π/2)(3/2) = 3π/4.
      Does it carry analytic content?  We check whether
        R_f(3π/4, s)  is reducible to / determined by  R_f(3/2, s)
      via the (π/2)·multiplier, by direct numerical comparison.
"""

from mpmath import mp, mpf, mpc, pi, exp, sqrt, log, expj, e1, zeta

mp.dps = 40

ALPHA_BSD = 3*pi/4
ALPHA_RH = mpf(3)/2
PHI = (1 + sqrt(5))/2
E_CONST = exp(1)

def d3(n):
    s = 0
    while n > 0:
        s += n % 3; n //= 3
    return s

def rf(alpha, s, N):
    s = mpc(s); alpha = mpc(alpha)
    total = mpc(0); pia = pi * alpha
    for n in range(1, N+1):
        total += expj(pia * d3(n))/mpc(n)**s
    return total

print("="*70)
print("(A) Where does φ/e live in the framework at α = 3π/4?")
print("="*70)

phi_over_e = PHI / E_CONST
print(f"φ/e = {phi_over_e}")
print(f"λ_0(H_{{3π/4}}) = π/(10·3π/4) = 2/15 = {pi/(10*ALPHA_BSD)}")

print("\nCandidate framework quantities to compare against φ/e:")
candidates = {
    "λ_0 = 2/15":                 pi/(10*ALPHA_BSD),
    "φ":                          PHI,
    "1/e":                        1/E_CONST,
    "φ/e (target)":               phi_over_e,
    "π/10 · α_BSD = 3π²/40":      pi*ALPHA_BSD/10,
    "α_BSD/π · e^{-1}":           ALPHA_BSD/pi/E_CONST,
    "1/α_BSD":                    1/ALPHA_BSD,
    "1/(2·α_BSD)":                1/(2*ALPHA_BSD),
    "1/(α_BSD·e)":                1/(ALPHA_BSD*E_CONST),
    "1/(π·e/(α_BSD))":            ALPHA_BSD/(pi*E_CONST),
    "2/(π·e)":                    2/(pi*E_CONST),
    "sin(α_BSD·φ)":               mp.sin(ALPHA_BSD*PHI),
    "cos(α_BSD)/e":               mp.cos(ALPHA_BSD)/E_CONST,
    "tan(1/α_BSD)":               mp.tan(1/ALPHA_BSD),
}
print(f"{'name':40} {'value':>40}   ratio to φ/e")
print("-"*105)
for name, v in candidates.items():
    v = mp.re(mpc(v))
    print(f"{name:40} {mp.nstr(v,16):>40}   {mp.nstr(v/phi_over_e, 8)}")

print("\nObservation: none of these is φ/e.  The 'φ/e distinguished eigenvalue'")
print("does not arise from any simple combination of the BSD α-value and the")
print("framework's universal coupling.  It must come from operator-theoretic")
print("structure that has NOT YET been formalised (and which the previous")
print("spectral-route closure on May 23 found to be absent on the four standard")
print("substrates we tested).")

print("\n" + "="*70)
print("(B) Pinning  α_BSD = (π/2)·α_RH  : does it transfer analytic content?")
print("="*70)
print(f"\n  α_RH = 3/2,    α_BSD = (π/2)·(3/2) = 3π/4")
print(f"  numerical pinning check: (π/2)·3/2 - 3π/4 = "
      f"{pi/2 * mpf(3)/2 - ALPHA_BSD}   (==0 by definition)")

# Compare R_f(3π/4, s) and R_f(3/2, s) at s=1
print("\nComparison of R_f at the two α-values for s = 1:")
rf_rh   = rf(ALPHA_RH, 1, 300_000)
rf_bsd  = rf(ALPHA_BSD, 1, 300_000)
print(f"  R_f(3/2,  1) ≈ {rf_rh}")
print(f"  R_f(3π/4, 1) ≈ {rf_bsd}")
print(f"  ratio        = {rf_bsd / rf_rh}")
print(f"  |ratio|      = {abs(rf_bsd / rf_rh)}")
# Try the trivial 'scaling' guess R_f(α',s) = (something) · R_f(α,s)
print(f"\n  (π/2) factor explicit:")
print(f"    (π/2) = {pi/2}")
print(f"    abs ratio / (π/2) = {abs(rf_bsd/rf_rh) / (pi/2)}")
print(f"    ratio · 2/π       = {rf_bsd / rf_rh * 2 / pi}")

# A more honest test: regress R_f(3π/4, s) against R_f(3/2, s) over multiple s
print("\nSweep across several s values: are the two R_f values linearly related?")
print(f"{'s':>10} {'R_f(3/2,s)':>50} {'R_f(3π/4,s)':>50}    ratio mag/arg")
for s_val in [mpf('1.5'), mpf('1.25'), mpf('1.1'), mpf('1.05'),
              mpf('1.0'), mpf('0.9'), mpf('0.5')]:
    rrh = rf(ALPHA_RH, s_val, 200_000)
    rbsd = rf(ALPHA_BSD, s_val, 200_000)
    ratio = rbsd/rrh
    print(f"  s={mp.nstr(s_val,4):>6}    "
          f"{mp.nstr(rrh,4):>40}    "
          f"{mp.nstr(rbsd,4):>40}    "
          f"|r|={mp.nstr(abs(ratio),6)}  arg={mp.nstr(mp.arg(ratio),6)}")

print("""
Conclusion (B): the ratio R_f(3π/4,s)/R_f(3/2,s) varies strongly with s
(no constant relationship), so the algebraic pinning α_BSD = (π/2)·α_RH
does NOT induce any simple functional relationship between R_f(3π/4, s)
and R_f(3/2, s).  The two are independent analytic objects that happen
to live at α-values related by a factor of π/2.  A genuine cascade
"RH discharges ⇒ BSD discharges" would require an additional bridge
construction (not present in the current framework machinery).
""")
