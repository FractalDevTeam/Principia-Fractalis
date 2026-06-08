"""
H_P on the language space — N=3 (M=15, DIM=32768).

A full 32768x32768 complex matrix would be ~17 GB; instead we use the
Toggle-group symmetry: H_P commutes with the toggle operators (each x is
an involution), so H_P factors via Walsh-Hadamard / character decomposition
when E_P = trivial.

When E_P = trivial: weights w(x) are L-independent, so H_P = sum_x w(x) * T_x
where T_x toggles bit x. The T_x mutually commute (each is a Pauli-X on bit x),
so H_P is jointly diagonalizable. Eigenvalues:
   lambda(s) = sum_x w(x) * (-1)^{s_x},     s in {0,1}^M

That gives the FULL spectrum for E=trivial with closed form -- no diagonalization needed.

For E_P = member (the interesting case), no such reduction; use sparse construction
on a restricted subspace (random projection) and Lanczos. We'll only do N=3 for
E=trivial since member/prefix are 32768x32768 dense and beyond local memory.
"""

import numpy as np

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

def all_strings_upto(N):
    out = ['']
    for k in range(1, N + 1):
        for n in range(2 ** k):
            out.append(format(n, f'0{k}b'))
    return out

def trivial_spectrum(alpha, N):
    """
    For E_P = trivial:
        H_P = sum_x w(x) * sigma_x^{(string index of x)}
    Eigenvalues indexed by s in {0,1}^M:
        lambda(s) = sum_x w(x) * (-1)^{s_x}
    All 2^M eigenvalues.
    """
    strings = all_strings_upto(N)
    M = len(strings)
    weights = np.array([weight(x, alpha) for x in strings], dtype=complex)
    # Build all sign patterns; 2^M can be huge -- only feasible up to M ~ 20.
    eigs = np.zeros(2 ** M, dtype=complex)
    for s_idx in range(2 ** M):
        signs = np.array([1 - 2 * ((s_idx >> i) & 1) for i in range(M)], dtype=float)
        eigs[s_idx] = np.sum(weights * signs)
    return eigs

def trivial_spectrum_ranges(alpha, N):
    """
    Faster: extremes via |sum w(x) * eps_x| over eps_x in {+-1}.
    The full spectrum is a sum-set; we just want closeness to target.
    For complex weights, we enumerate (still 2^M total but compact).
    """
    return trivial_spectrum(alpha, N)

if __name__ == '__main__':
    for N in [1, 2, 3, 4]:
        strings = all_strings_upto(N)
        M = len(strings)
        if 2 ** M > 2_000_000:
            print(f"N={N}, M={M}: 2^M={2**M} too large, skipping enumeration.")
            continue
        for alpha_name, alpha, target in [
            ('sqrt(2)', np.sqrt(2), np.pi / (10 * np.sqrt(2))),
            ('3/2',     1.5,        np.pi / 15),
            ('2',       2.0,        np.pi / 20),
        ]:
            eigs = trivial_spectrum(alpha, N)
            # H_P is the SUM of commuting Pauli-X's weighted by complex w(x).
            # Hermitian part eigenvalues:
            herm_part_eigs = 0.5 * (eigs + np.conj(eigs))  # = Re(eigs)
            herm_part_eigs = np.real(herm_part_eigs)
            gap_re = np.min(np.abs(np.real(eigs) - target))
            gap_abs = np.min(np.abs(np.abs(eigs) - target))
            gap_herm = np.min(np.abs(herm_part_eigs - target))
            nearest = eigs[np.argmin(np.abs(np.real(eigs) - target))]
            n_within_001 = int(np.sum(np.abs(np.real(eigs) - target) < 0.01))
            density = n_within_001 / 2 ** M
            print(f"  N={N} M={M} alpha={alpha_name:7s} target={target:.6f}: "
                  f"min|Re-tgt|={gap_re:.6e}  nearest={nearest.real:+.6f}{nearest.imag:+.6f}i  "
                  f"hits<0.01: {n_within_001}/{2**M} ({density*100:.3f}%)")
