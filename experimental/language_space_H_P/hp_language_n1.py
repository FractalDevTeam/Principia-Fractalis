"""
H_P on the language space — N=1 truncation (sanity check).

Strings up to length 1: {epsilon, 0, 1}  => M = 3 strings
Languages: subsets of these 3 strings   => 2^3 = 8 languages
H_P is an 8x8 complex matrix.

Manuscript Ch 21 definition (line 201-203):
  (H_P f)(L) = sum_{x in {0,1}*} (1/2^|x|) * exp(i*pi*alpha_P*D(encode(x)))
                                * E_P(M_L, x) * f(L XOR {x})

We test 3 proxy choices for E_P:
  (A) E_P = 1 always (kernel without computational selection)
  (B) E_P(L, x) = 1 iff x in L
  (C) E_P(L, x) = 1 iff x is a prefix of some y in L (or x in L if L nonempty)

The kernel weight w(x) = (1/2^|x|) * exp(i*pi*alpha*D(encode(x))).
"""

import numpy as np

# ------------------------------------------------------------------
# Setup
# ------------------------------------------------------------------
N = 1
strings = ['', '0', '1']           # all binary strings up to length N
M = len(strings)                   # 3
DIM = 2 ** M                       # 8 languages

# Index of each string in the bit-vector
str_index = {s: i for i, s in enumerate(strings)}

def lang_to_vec(L_idx):
    """Language index (0..DIM-1) -> bit-vector over strings (length M)."""
    return [(L_idx >> i) & 1 for i in range(M)]

def vec_to_lang(v):
    return sum(int(b) << i for i, b in enumerate(v))

def toggle(L_idx, x):
    """Symmetric difference L XOR {x}."""
    bit = 1 << str_index[x]
    return L_idx ^ bit

# ------------------------------------------------------------------
# Encoding and digital sum
# ------------------------------------------------------------------
def encode(x):
    """
    Encode a binary string as a positive integer.
    Convention: encode('') = 1, encode(x) = 1 followed by x (binary).
    This is a standard prefix-free encoding (length |x|+1).
    """
    if x == '':
        return 1
    return int('1' + x, 2)

def base3_digital_sum(n):
    """Sum of base-3 digits of n."""
    s = 0
    while n > 0:
        s += n % 3
        n //= 3
    return s

# Precompute weights w(x) (alpha-dependent factor handled at build)
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
    """x in L."""
    v = lang_to_vec(L_idx)
    return float(v[str_index[x]])

def E_nonempty(L_idx, x):
    """L is nonempty (witnesses some computational signal)."""
    return 1.0 if L_idx != 0 else 0.0

E_options = {'trivial': E_trivial,
             'member' : E_member,
             'nonempty': E_nonempty}

# ------------------------------------------------------------------
# Build H_P
# ------------------------------------------------------------------
def build_HP(alpha, E_fn, X_set=None):
    """X_set: list of strings to sum over (default = all strings up to N)."""
    if X_set is None:
        X_set = strings
    H = np.zeros((DIM, DIM), dtype=complex)
    weights = {x: weight(x, alpha) for x in X_set}
    for L in range(DIM):
        for x in X_set:
            L_new = toggle(L, x)
            coeff = weights[x] * E_fn(L, x)
            # (H_P f)(L) gets contribution from f(L_new) => row L, col L_new
            H[L, L_new] += coeff
    return H

# ------------------------------------------------------------------
# Diagnostics
# ------------------------------------------------------------------
def report_spectrum(H, label, target):
    sa_err = np.max(np.abs(H - H.conj().T))
    # Hermitian part eigenvalues
    H_herm = 0.5 * (H + H.conj().T)
    w_herm = np.linalg.eigvalsh(H_herm)
    # Full operator eigenvalues
    w_full = np.linalg.eigvals(H)
    abs_full = np.sort(np.abs(w_full))
    real_full = np.sort(w_full.real)
    # Closest eigenvalue to target (compare both real-spectrum and |eigs|)
    gap_herm = np.min(np.abs(w_herm - target))
    gap_real = np.min(np.abs(real_full - target))
    gap_abs  = np.min(np.abs(abs_full - target))
    print(f"  {label}")
    print(f"    self-adjointness err = ||H - H*||_inf = {sa_err:.6e}")
    print(f"    Hermitian-part eigvals (sorted): {np.array2string(w_herm, precision=5)}")
    print(f"    min |w_herm - target|             = {gap_herm:.6e}")
    print(f"    min |Re(w_full) - target|         = {gap_real:.6e}")
    print(f"    min ||w_full| - target|           = {gap_abs:.6e}")

# ------------------------------------------------------------------
# Main
# ------------------------------------------------------------------
def main():
    print("=" * 70)
    print(f"H_P on language space, N={N}, M={M}, dim={DIM}")
    print("=" * 70)
    for alpha_name, alpha, target in [
        ('alpha = sqrt(2)', np.sqrt(2), np.pi / (10 * np.sqrt(2))),
        ('alpha = 3/2',     1.5,        np.pi / 15),
        ('alpha = 2',       2.0,        np.pi / 20),
    ]:
        print(f"\n--- {alpha_name} (target lambda_0 = pi/(10*alpha) = {target:.8f}) ---")
        for name, fn in E_options.items():
            H = build_HP(alpha, fn)
            report_spectrum(H, f"E_P = {name}", target)

if __name__ == '__main__':
    main()
