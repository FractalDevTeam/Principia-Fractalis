"""
H_P on the language space — N=2 truncation (full manuscript test).

Strings of length <= 2: {epsilon, 0, 1, 00, 01, 10, 11} => M = 7
Languages: subsets => DIM = 128
H_P is a 128x128 complex matrix.

Same construction as hp_language_n1.py with all three E_P proxies, plus
H_NP test using sup-over-witnesses (line 228).

For H_NP we use a 1-bit witness c in {0,1}, W(x,c) = base3_digital_sum(encode(x.c))
and V_L(x,c) = 1 iff (x.c) in L (so the verifier accepts x with certificate c
iff the concatenation is in the language). The sup over c of e^{i*pi*alpha*W}
when at least one certificate succeeds reduces to picking the c with the
largest real-part phase.
"""

import numpy as np

# ------------------------------------------------------------------
N = 2
strings = []
for k in range(N + 1):
    if k == 0:
        strings.append('')
    else:
        for n in range(2 ** k):
            strings.append(format(n, f'0{k}b'))
# strings = ['', '0', '1', '00', '01', '10', '11']
M = len(strings)
DIM = 2 ** M
print(f"Setup: N={N}, M={M} strings, DIM={DIM} languages")

str_index = {s: i for i, s in enumerate(strings)}

def lang_to_vec(L_idx):
    return [(L_idx >> i) & 1 for i in range(M)]

def toggle(L_idx, x):
    return L_idx ^ (1 << str_index[x])

def encode(x):
    return 1 if x == '' else int('1' + x, 2)

def base3_digital_sum(n):
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

def weight(x, alpha):
    L = len(x)
    n = encode(x)
    D = base3_digital_sum(n)
    return (0.5 ** L) * np.exp(1j * np.pi * alpha * D)

# ------------------------------------------------------------------
# E_P proxies
# ------------------------------------------------------------------
def E_trivial(L_idx, x):
    return 1.0

def E_member(L_idx, x):
    return float((L_idx >> str_index[x]) & 1)

def E_prefix(L_idx, x):
    """x is a prefix of some y in L."""
    for s in strings:
        if s.startswith(x) and ((L_idx >> str_index[s]) & 1):
            return 1.0
    return 0.0

E_options = {'trivial': E_trivial,
             'member' : E_member,
             'prefix' : E_prefix}

# ------------------------------------------------------------------
# Build H_P
# ------------------------------------------------------------------
def build_HP(alpha, E_fn):
    H = np.zeros((DIM, DIM), dtype=complex)
    weights = {x: weight(x, alpha) for x in strings}
    for L in range(DIM):
        for x in strings:
            L_new = toggle(L, x)
            coeff = weights[x] * E_fn(L, x)
            if coeff != 0:
                H[L, L_new] += coeff
    return H

# ------------------------------------------------------------------
# H_NP: sup over certificate c in {0,1}, V_L(x,c) = 1 iff x.c in L
# ------------------------------------------------------------------
def W_xc(x, c):
    """Witness function W(x,c) = base-3 digital sum of encode(x||c)."""
    return base3_digital_sum(encode(x + c))

def build_HNP(alpha):
    """
    (H_NP f)(L) = sum_x (1/2^|x|) * sup_{c: V_L(x,c)=1} [exp(i*pi*alpha*W(x,c)) * E_NP]
                                 * f(L XOR {x})
    Restrict x so that x.c fits in our truncation: |x| <= N-1 so |x.c| <= N.
    For x with |x|=N we can't append c (would exceed truncation); skip those.
    sup taken over real-part magnitude (geometric supremum convention).
    """
    H = np.zeros((DIM, DIM), dtype=complex)
    valid_x = [x for x in strings if len(x) < N]  # need room for c
    for L in range(DIM):
        for x in valid_x:
            best = 0.0 + 0j
            best_mag = -1.0
            for c in ['0', '1']:
                target = x + c
                if target not in str_index:
                    continue
                if (L_idx_bit(L, target)) == 0:
                    continue   # V_L(x,c) = 0 means certificate fails
                phase = np.exp(1j * np.pi * alpha * W_xc(x, c))
                # sup by real-part magnitude; if tie take first
                if phase.real > best_mag:
                    best_mag = phase.real
                    best = phase
            if best_mag < 0:
                continue
            coeff = (0.5 ** len(x)) * best
            L_new = toggle(L, x)
            H[L, L_new] += coeff
    return H

def L_idx_bit(L_idx, s):
    return (L_idx >> str_index[s]) & 1

# ------------------------------------------------------------------
# Reporting
# ------------------------------------------------------------------
def report_spectrum(H, label, target, alpha_label):
    sa_err = np.max(np.abs(H - H.conj().T))
    H_herm = 0.5 * (H + H.conj().T)
    w_herm = np.linalg.eigvalsh(H_herm)
    w_full = np.linalg.eigvals(H)
    abs_full = np.sort(np.abs(w_full))
    real_full = np.sort(w_full.real)
    gap_herm = np.min(np.abs(w_herm - target))
    gap_real = np.min(np.abs(real_full - target))
    gap_abs  = np.min(np.abs(abs_full - target))
    nearest_herm = w_herm[np.argmin(np.abs(w_herm - target))]
    print(f"  [{alpha_label}] {label}")
    print(f"    ||H - H*||_inf       = {sa_err:.6e}")
    print(f"    min |w_herm-target|  = {gap_herm:.6e}    nearest = {nearest_herm:.8f}")
    print(f"    min |Re(w_full)-tgt| = {gap_real:.6e}")
    print(f"    min ||w_full|-tgt|   = {gap_abs:.6e}")
    # show 4 smallest positive eigenvalues of Hermitian part
    pos = sorted(w for w in w_herm if w > 1e-10)[:4]
    print(f"    4 smallest +ve w_herm: {[f'{p:.6f}' for p in pos]}")

# ------------------------------------------------------------------
# Main
# ------------------------------------------------------------------
def main():
    print("=" * 72)
    print(f"H_P on language space (manuscript Ch 21), N={N}, M={M}, dim={DIM}")
    print("=" * 72)
    alphas = [
        ('alpha=sqrt(2)', np.sqrt(2), np.pi / (10 * np.sqrt(2))),
        ('alpha=3/2',     1.5,        np.pi / 15),
        ('alpha=2',       2.0,        np.pi / 20),
    ]
    for alpha_label, alpha, target in alphas:
        print(f"\n--- {alpha_label}, target = pi/(10*alpha) = {target:.10f} ---")
        for name, fn in E_options.items():
            H = build_HP(alpha, fn)
            report_spectrum(H, f"H_P (E={name})", target, alpha_label)
        # H_NP at the same alpha (target same form pi/(10*alpha) for comparison)
        HNP = build_HNP(alpha)
        report_spectrum(HNP, "H_NP (sup-c)", target, alpha_label)

    # Special: H_NP at alpha_NP = phi + 1/4
    phi = (1 + np.sqrt(5)) / 2
    a_NP = phi + 0.25
    target_NP = np.pi / (10 * a_NP)
    print(f"\n--- alpha_NP = phi+1/4 = {a_NP:.6f}, target = {target_NP:.10f} ---")
    HNP = build_HNP(a_NP)
    report_spectrum(HNP, "H_NP at alpha_NP", target_NP, 'alpha_NP')

if __name__ == '__main__':
    main()
