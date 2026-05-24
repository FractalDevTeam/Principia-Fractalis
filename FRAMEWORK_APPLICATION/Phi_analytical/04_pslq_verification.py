"""
Phi_analytical/04_pslq_verification.py

The PSLQ in 03 reported "relations" like
   1*sqrt(2) - 1*alpha = 0   for alpha = sqrt(2)
   3*pi - 4*alpha = 0        for alpha = 3*pi/4
which are TRIVIALLY TRUE (alpha IS sqrt(2), alpha IS 3*pi/4). These are not
relations on Phi --- they're saying PSLQ found a relation purely among the
known-equivalent inputs, ignoring Phi.

We need to RUN PSLQ on (|Phi|, basis) WITHOUT including alpha as a separate
variable, OR include alpha but verify the relation also INVOLVES |Phi|.

Re-run PSLQ properly:
   variables = [|Phi(alpha)|, 1, pi, sqrt(2), phi_g, e, log 2, log 3]
   (no alpha, no alpha^2)
"""
from mpmath import mp, mpc, mpf, pi, exp, log, sqrt, cos, sin, nstr, pslq

mp.dps = 60

def d3(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

N_MAX = 200_000
D3 = [0] * (N_MAX + 1)
for n in range(1, N_MAX + 1):
    D3[n] = D3[n // 3] + (n % 3)

def F(alpha, s):
    a = mpf(alpha)
    s_c = mpc(s)
    return mpc(3) ** (-s_c) * exp(mpc(0, pi * a)) * (1 + 2 * cos(pi * a))

def correction(alpha, s, M):
    a = mpf(alpha)
    s_c = mpc(s)
    T1 = exp(mpc(0, pi * a)) + exp(mpc(0, 2 * pi * a)) / mpc(2) ** s_c
    total = T1
    for r in (1, 2):
        phase_r = exp(mpc(0, pi * a * r))
        sub = mpc(0)
        for m in range(1, M + 1):
            phase_m = exp(mpc(0, pi * a * D3[m]))
            diff = mpc(3 * m + r) ** (-s_c) - mpc(3 * m) ** (-s_c)
            sub += phase_m * diff
        total += phase_r * sub
    return total

def Rf_recursion(alpha, s, M):
    Fv = F(alpha, s)
    if abs(1 - Fv) < mpf("1e-30"):
        return None
    return correction(alpha, s, M) / (1 - Fv)

def Li_1(z):
    return -log(1 - z)

sqrt2 = sqrt(2)
phi_g = (1 + sqrt(5)) / 2

# Compute Phi values to high precision via recursion
M_solve = 100_000
print(f"Computing Phi at all 9 instances at M={M_solve}, precision {mp.dps}...", flush=True)
alphas_9 = [
    ("1   (Poincare)", mpf(1)),
    ("3/2 (RH)",        mpf("1.5")),
    ("sqrt(2) (P)",     sqrt2),
    ("phi+1/4 (NP)",    phi_g + mpf("0.25")),
    ("3*pi/4 (BSD)",    3 * pi / 4),
    ("3*pi/2 (NS)",     3 * pi / 2),
    ("phi (Hodge)",     phi_g),
    ("sqrt(2*pi) (QG)", sqrt(2 * pi)),
]

phi_dict = {}
for name, a in alphas_9:
    Rfv = Rf_recursion(a, mpc(1), M_solve)
    z = exp(mpc(0, pi * a))
    Liv = Li_1(z)
    Phi_v = Rfv / Liv
    phi_dict[name] = (a, Phi_v, abs(Phi_v))
    print(f"  {name}: |Phi|={nstr(abs(Phi_v), 30)}", flush=True)

print()
print("=" * 90)
print(" PROPER PSLQ on (|Phi|, basis) -- NO alpha, only universal constants")
print("=" * 90)

# Test basis: {1, pi, phi_g, sqrt(2), e, log 2, log 3, 1/pi, 1/phi_g, sqrt(3)}
basis = {
    "1":         mpf(1),
    "pi":        pi,
    "phi_g":     phi_g,
    "sqrt(2)":   sqrt2,
    "e":         exp(mpf(1)),
    "log2":      log(mpf(2)),
    "log3":      log(mpf(3)),
    "sqrt(3)":   sqrt(mpf(3)),
    "sqrt(5)":   sqrt(mpf(5)),
}
basis_vals = list(basis.values())
basis_labels = list(basis.keys())

for name, (a, Phi_v, abs_phi) in phi_dict.items():
    vec = [abs_phi] + basis_vals
    labels = ["|Phi|"] + basis_labels
    try:
        rel = pslq(vec, tol=mpf("1e-25"), maxcoeff=10**10)
        if rel is None or rel[0] == 0:
            print(f"  {name}: NO RELATION involving |Phi| in basis (true confirmation: |Phi| is structurally not a small-integer combo of these constants).")
        else:
            terms = [f"{c}*{lab}" for c, lab in zip(rel, labels) if c != 0]
            print(f"  {name}: PSLQ: {' + '.join(terms)} = 0")
            # Verify
            check = sum(c * v for c, v in zip(rel, vec))
            print(f"    residual: {nstr(check, 8)}")
    except Exception as e:
        print(f"  {name}: PSLQ error {e}")

print()
print("=" * 90)
print(" Re(Phi) and Im(Phi) separately -- PSLQ search")
print("=" * 90)
print()
for name, (a, Phi_v, abs_phi) in phi_dict.items():
    print(f"  --- {name} ---")
    for component, val in [("Re Phi", Phi_v.real), ("Im Phi", Phi_v.imag)]:
        vec = [val] + basis_vals
        labels = [component] + basis_labels
        try:
            rel = pslq(vec, tol=mpf("1e-25"), maxcoeff=10**10)
            if rel is None or rel[0] == 0:
                print(f"    {component}={nstr(val, 14)}: NO RELATION")
            else:
                terms = [f"{c}*{lab}" for c, lab in zip(rel, labels) if c != 0]
                print(f"    {component}={nstr(val, 14)}: PSLQ: {' + '.join(terms)} = 0")
        except Exception as e:
            print(f"    {component}: PSLQ error {e}")

print()
print("=" * 90)
print(" Test specific candidate: |Phi(alpha)|^2 ?= 1 + alpha or 2 - cos(pi*alpha) etc.")
print("=" * 90)
for name, (a, Phi_v, abs_phi) in phi_dict.items():
    abs_phi_sq = abs_phi * abs_phi
    test1 = mpf(2) - cos(pi * a)
    test2 = mpf(1) + a / (1 + a)
    test3 = mpf(1) / abs(1 - F(a, mpc(1)))
    test4 = abs(1 / (1 - F(a, mpc(1))))
    print(f"  {name}: |Phi|^2 = {nstr(abs_phi_sq, 14)}")
    print(f"    2 - cos(pi*alpha)        = {nstr(test1, 14)}")
    print(f"    1 + alpha/(1+alpha)      = {nstr(test2, 14)}")
    print(f"    1 / |1 - F(alpha,1)|     = {nstr(test4, 14)}")
