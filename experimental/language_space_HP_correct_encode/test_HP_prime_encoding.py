"""
CORRECTED LANGUAGE-SPACE H_P TEST WITH FRAMEWORK'S ACTUAL ENCODING
====================================================================
Tests the manuscript Ch 21 H_P operator using the PRIME-PRODUCT encoding
from PF/TuringEncoding/Basic.lean, not the prior agent's prefix-free encoding.

encode(x) for binary string x of length L (state=0, head=0):
    encode(x) = Π_{j=0}^{L-1} p_{j+2}^{x[j]+1}
where p_0=2, p_1=3, p_2=5, p_3=7, p_4=11, p_5=13, p_6=17,...

D_3(n) = digital sum of n in base 3.

H_P on language-vector space:
    H_P = Σ_x (1/2^|x|) · e^{iπα·D_3(encode(x))} · F_x
where F_x flips the bit corresponding to string x in language indicator.

All F_x commute (each toggles independent bit) — H_P is diagonal in Hadamard
basis with eigenvalues:
    λ_S = Σ_x (1/2^|x|) · e^{iπα·D_3(encode(x))} · χ_S(x),  χ_S(x) = (-1)^[x∈S]

Author: Scientific Computing Specialist (Pabs's Principia Fractalis line)
Date: 2026-05-23
"""
import numpy as np
from sympy import isprime, nextprime, Integer

# ----------------------------------------------------------------------------
# 1. PRIME-PRODUCT ENCODING
# ----------------------------------------------------------------------------

def nth_prime(k):
    """0-indexed nth prime: nth_prime(0)=2, nth_prime(1)=3, nth_prime(2)=5,..."""
    p = 2
    for _ in range(k):
        p = nextprime(p)
    return p

# Pre-compute primes we'll need (indices 2..10 is plenty for tape len <= 10)
PRIMES = [nth_prime(k) for k in range(12)]
# PRIMES[0]=2, PRIMES[1]=3, PRIMES[2]=5, PRIMES[3]=7, PRIMES[4]=11, ...

def encode_string(x):
    """
    Framework's encoding (binary string -> Nat) with state=0, head=0.

    encode(x) = Π_{j=0}^{|x|-1} p_{j+2}^{x[j]+1}

    Parameters
    ----------
    x : str of '0'/'1' (possibly empty)

    Returns
    -------
    sympy Integer
    """
    result = Integer(1)
    for j, ch in enumerate(x):
        bit = int(ch)
        p = PRIMES[j + 2]   # tape cell j uses prime p_{j+2}
        result *= Integer(p) ** (bit + 1)
    return result

def digital_sum_base(n, b=3):
    """D_b(n): sum of digits of n in base b."""
    n = int(n)
    if n == 0:
        return 0
    s = 0
    while n > 0:
        s += n % b
        n //= b
    return s

def D3_encode(x):
    return digital_sum_base(encode_string(x), 3)

# ----------------------------------------------------------------------------
# 2. SPOT-CHECK against problem statement
# ----------------------------------------------------------------------------

def verify_encoding():
    expected = {
        ""  : (1, 0),       # empty product = 1, D_3(1) = 1  (problem says empty -> 1; D_3(1)=1, not 0; recompute)
        "0" : (5, 3),
        "1" : (25, 5),
        "00": (35, 5),
        "01": (245, 3),
        "10": (175, 5),
        "11": (1225, 6),
    }
    print("=" * 72)
    print("Encoding spot-check (vs problem statement)")
    print("=" * 72)
    print(f"{'x':>4} | {'encode(x)':>10} | {'D_3':>4} | expected enc | expected D_3")
    print("-" * 72)
    for x, (enc_exp, d_exp) in expected.items():
        enc = int(encode_string(x))
        d   = D3_encode(x)
        ok  = (enc == enc_exp) and (d == d_exp)
        flag = "OK" if ok else "MISMATCH"
        # For empty string, D_3(1) = 1 not 0; problem statement gave "empty: encode=1, D_3=?"
        # I'll just report.
        print(f"{x!r:>4} | {enc:>10} | {d:>4} | {enc_exp:>12} | {d_exp:>12}  [{flag}]")
    print()

# ----------------------------------------------------------------------------
# 3. ENUMERATE STRINGS UP TO LENGTH N
# ----------------------------------------------------------------------------

def enumerate_strings(N):
    """All binary strings of length 0..N, in lex order within each length."""
    out = [""]
    for L in range(1, N + 1):
        for k in range(2 ** L):
            out.append(format(k, f"0{L}b"))
    return out

# ----------------------------------------------------------------------------
# 4. SPECTRUM OF H_P
# ----------------------------------------------------------------------------

def coeff(x, alpha):
    """c_x(α) = (1/2^|x|) · e^{iπα · D_3(encode(x))}"""
    L = len(x)
    d = D3_encode(x)
    return (0.5 ** L) * np.exp(1j * np.pi * alpha * d)

def hadamard_eigenvalues(strings, alpha):
    """
    H_P = Σ_x c_x · F_x where F_x toggles bit-index of x in {0,1}^|strings|.
    F_x mutually commute; common eigenbasis = Hadamard basis of {0,1}^M (M=|strings|).
    Eigenvalues:  λ_S = Σ_x c_x · (-1)^{S_x}  for each S ⊆ strings.
    """
    M = len(strings)
    cx = np.array([coeff(x, alpha) for x in strings], dtype=complex)   # shape (M,)
    # S iterates over 2^M subsets, represented as integers
    nS = 2 ** M
    # For each S, λ_S = Σ_x c_x · (-1)^bit_x(S)
    # Build (-1)^bits matrix in vectorized way
    bits = np.array([[ (S >> i) & 1 for i in range(M)] for S in range(nS)], dtype=np.int8)
    signs = 1 - 2 * bits   # +1 if bit=0, -1 if bit=1
    eigs = signs @ cx
    return eigs

# ----------------------------------------------------------------------------
# 5. DIRECT H_P MATRIX (verification) on 2^M-dim space
# ----------------------------------------------------------------------------

def build_HP_matrix(strings, alpha):
    """
    Build full H_P on language vector space C^{2^M}.
    Row L1, col L2:  (H_P)_{L1,L2} = c_x  iff  L1 XOR L2 = {x} for some x in strings;
                                       0   otherwise.
    """
    M = len(strings)
    dim = 2 ** M
    H = np.zeros((dim, dim), dtype=complex)
    cx = [coeff(x, alpha) for x in strings]
    for L1 in range(dim):
        for i, x in enumerate(strings):
            L2 = L1 ^ (1 << i)
            H[L1, L2] += cx[i]
    return H

# ----------------------------------------------------------------------------
# 6. PHASE-SUM CONDITION (line 282)
# ----------------------------------------------------------------------------

def phase_sum_imag(strings_by_level, alpha):
    """
    Returns a dict {level n -> Σ_{|x|=n} (1/2^n) · sin(πα · D_3(encode(x)))}.
    Self-adjointness (per manuscript line 282) requires this = 0 each level.
    """
    out = {}
    for L, xs in strings_by_level.items():
        s = 0.0
        for x in xs:
            d = D3_encode(x)
            s += (0.5 ** L) * np.sin(np.pi * alpha * d)
        out[L] = s
    return out

# ----------------------------------------------------------------------------
# 7. MAIN
# ----------------------------------------------------------------------------

def main():
    verify_encoding()

    # Print D_3(encode(x)) for |x| <= 4
    print("=" * 72)
    print("D_3(encode(x)) for all binary strings |x| <= 4")
    print("=" * 72)
    all_strings = enumerate_strings(4)
    by_level = {}
    for x in all_strings:
        by_level.setdefault(len(x), []).append(x)
    for L in sorted(by_level):
        print(f"\n--- length {L}  ({len(by_level[L])} strings) ---")
        for x in by_level[L]:
            enc = encode_string(x)
            d = D3_encode(x)
            print(f"  x={x!r:>6}  encode={int(enc):>20}  D_3={d:>4}")

    # ----- Build H_P with N=2 (7 strings, 128 languages) -----
    N = 2
    strings_N = [x for x in enumerate_strings(N)]
    M = len(strings_N)
    dim = 2 ** M
    print()
    print("=" * 72)
    print(f"H_P spectrum: N={N},  strings={strings_N},  M={M},  dim=2^M={dim}")
    print("=" * 72)

    alpha_sqrt2 = np.sqrt(2.0)
    target = np.pi / (10.0 * alpha_sqrt2)
    print(f"Target eigenvalue (manuscript π/(10√2)): {target:.10f}")

    # Eigenvalues via Hadamard diagonalization
    eigs_had = hadamard_eigenvalues(strings_N, alpha_sqrt2)

    # Cross-check via direct matrix diagonalization
    H = build_HP_matrix(strings_N, alpha_sqrt2)
    eigs_dir = np.linalg.eigvals(H)

    # Sort and compare
    eigs_had_sorted = np.sort_complex(eigs_had)
    eigs_dir_sorted = np.sort_complex(eigs_dir)
    diff = np.max(np.abs(eigs_had_sorted - eigs_dir_sorted))
    print(f"\nCross-check |Hadamard eigs - direct eigs|_max = {diff:.3e}")
    assert diff < 1e-9, "Hadamard formula disagrees with direct diag!"
    print("Hadamard diagonalization VERIFIED.")

    # Top 10 closest to target (compare on real part; also report imag part)
    print(f"\nTop 10 eigenvalues closest to π/(10√2) ≈ {target:.6f}  (by |Re(λ) - target|):")
    distances_real = np.abs(np.real(eigs_had) - target)
    order = np.argsort(distances_real)[:10]
    print(f"  {'rank':>4} | {'Re(λ)':>14} | {'Im(λ)':>14} | {'|Re-target|':>14}")
    for r, idx in enumerate(order):
        e = eigs_had[idx]
        print(f"  {r+1:>4} | {e.real:>14.8f} | {e.imag:>14.8f} | {distances_real[idx]:>14.6e}")

    # Also: closest by FULL complex distance to (target, 0)
    print(f"\nTop 10 eigenvalues closest to π/(10√2) (full complex distance to target+0i):")
    distances_full = np.abs(eigs_had - target)
    order2 = np.argsort(distances_full)[:10]
    print(f"  {'rank':>4} | {'Re(λ)':>14} | {'Im(λ)':>14} | {'|λ - target|':>14}")
    for r, idx in enumerate(order2):
        e = eigs_had[idx]
        print(f"  {r+1:>4} | {e.real:>14.8f} | {e.imag:>14.8f} | {distances_full[idx]:>14.6e}")

    # Spectrum imaginary-part stats (Hermiticity)
    print(f"\nImaginary part stats: max|Im|={np.max(np.abs(eigs_had.imag)):.6e}  "
          f"mean|Im|={np.mean(np.abs(eigs_had.imag)):.6e}")

    # ----- Self-adjointness across α -----
    print()
    print("=" * 72)
    print("Self-adjointness test:  ||H_P - H_P^†||_F  vs α")
    print("=" * 72)
    phi = (1 + np.sqrt(5.0)) / 2.0
    alphas = [
        ("1",          1.0),
        ("√2",         np.sqrt(2.0)),
        ("3/2",        1.5),
        ("φ+1/4",      phi + 0.25),
        ("2",          2.0),
        ("3",          3.0),
        ("e",          np.e),
        ("π",          np.pi),
    ]
    print(f"  {'α':>8} | {'value':>14} | {'||H - H†||_F':>14} | {'||H||_F':>14} | {'ratio':>10}")
    for name, a in alphas:
        H = build_HP_matrix(strings_N, a)
        antiH = H - H.conj().T
        nF = np.linalg.norm(antiH, 'fro')
        nH = np.linalg.norm(H, 'fro')
        print(f"  {name:>8} | {a:>14.10f} | {nF:>14.6e} | {nH:>14.6e} | {nF/nH:>10.4f}")

    # ----- Phase-sum condition per level -----
    print()
    print("=" * 72)
    print("Phase-sum self-adjointness condition (line 282):")
    print("  Σ_{|x|=n} (1/2^n) sin(πα · D_3(encode(x))) = 0   for each level n?")
    print("=" * 72)

    # Use ALL strings up to N=4 (so we can probe level 0..4)
    by_level_for_phase = {L: [x for x in all_strings if len(x) == L] for L in range(0, 5)}
    print(f"\nAt α = √2 = {alpha_sqrt2:.10f}:")
    ps = phase_sum_imag(by_level_for_phase, alpha_sqrt2)
    for L in sorted(ps):
        print(f"  level {L} ({len(by_level_for_phase[L])} strings): phase_sum = {ps[L]:+.10e}")

    print(f"\nAt α = φ + 1/4 = {phi + 0.25:.10f}:")
    ps = phase_sum_imag(by_level_for_phase, phi + 0.25)
    for L in sorted(ps):
        print(f"  level {L} ({len(by_level_for_phase[L])} strings): phase_sum = {ps[L]:+.10e}")

    print(f"\nAt α = 2 (rational integer):")
    ps = phase_sum_imag(by_level_for_phase, 2.0)
    for L in sorted(ps):
        print(f"  level {L} ({len(by_level_for_phase[L])} strings): phase_sum = {ps[L]:+.10e}")

    # ----- α-scan for ground-state real part vs target -----
    print()
    print("=" * 72)
    print("α-scan: real spectrum closest to target  π/(10·α)  (manuscript form)")
    print("=" * 72)
    print(f"  {'α':>10} | {'π/(10α)':>10} | {'min|Re(λ) - tgt|':>16} | {'best Re(λ)':>14}")
    for name, a in alphas:
        eigs = hadamard_eigenvalues(strings_N, a)
        tgt = np.pi / (10.0 * a)
        d = np.abs(eigs.real - tgt)
        i = np.argmin(d)
        print(f"  {name:>10} | {tgt:>10.6f} | {d[i]:>16.6e} | {eigs[i].real:>14.8f}")

    print()
    print("=" * 72)
    print("DONE.")
    print("=" * 72)


if __name__ == "__main__":
    main()
