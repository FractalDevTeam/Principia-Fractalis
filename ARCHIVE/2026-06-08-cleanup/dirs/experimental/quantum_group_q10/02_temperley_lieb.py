"""
Temperley-Lieb TL_n at q = e^(i*pi/10).
Generators e_1,...,e_{n-1}, relations:
  e_i^2 = delta * e_i,  delta = [2]_q = 2 cos(pi/10) ~= 1.9021
  e_i e_{i+/-1} e_i = e_i
  e_i e_j = e_j e_i   for |i-j| >= 2

We construct the diagrammatic representation on standard tableaux of shape
(n - k, k) for 2k <= n (link patterns) and diagonalize H = sum_i e_i.
We look for pi/(10*sqrt(2)) ~= 0.2221 in the spectrum.

This is the "XXZ-chain at Delta = -cos(pi/10)" Hamiltonian (up to constants).
"""

import numpy as np
from mpmath import mp, mpf, mpc, sin as msin, cos as mcos, pi as mpi, sqrt as msqrt
mp.dps = 30

DELTA = float(2 * mcos(mpi / 10))   # 1.9021130325903071
print(f"delta = [2]_q at q=e^(i*pi/10) = {DELTA:.15f}")
print(f"target pi/(10*sqrt(2))         = {float(mpi/(10*msqrt(2))):.15f}")
print()

# ---------- enumerate link patterns / standard tableaux of (n-k, k) ----------
def link_patterns(n, k):
    """All non-crossing matchings of 2k of the n sites (the other n-2k are 'defects').
    For TL_n, the standard cell module W_{n,k} is spanned by these patterns.
    Returns list of patterns; each pattern is a frozenset of pairs (i,j)."""
    # Standard tableaux of shape (n-k, k): equivalent to ballot sequences with
    # n-k zeros and k ones such that #0 >= #1 in every prefix. We use the
    # parenthesisation encoding.
    results = []
    def rec(seq, opens, closes, stack):
        if len(seq) == n:
            if not stack:
                # all matched but we have k pairs; the (n-2k) unmatched were "defects".
                pass
            # Convert seq encoding to pairs
            pairs = []
            st = []
            for i, c in enumerate(seq):
                if c == 1:
                    st.append(i)
                elif c == -1:
                    pairs.append((st.pop(), i))
            results.append(frozenset(pairs))
            return
        # try '(' = 1
        if opens < k:
            rec(seq + [1], opens + 1, closes, stack + ['('])
        # try ')' = -1
        if closes < opens:
            rec(seq + [-1], opens, closes + 1, stack[:-1] if stack else stack)
        # try defect = 0 (only if defects remain; we have n-2k defects total)
        if (len(seq) - opens - closes) < (n - 2 * k):
            rec(seq + [0], opens, closes, stack)
    rec([], 0, 0, [])
    # Deduplicate (pair-set ignores defect positions inside the same pattern;
    # but for TL_n cell module, position matters for defects too). Keep all.
    # Instead: return raw sequences which are the actual basis.
    return None

def basis_sequences(n, k):
    """Sequences of length n with k '(' and k ')' forming valid (possibly with
    defects '.') and bounded such that '(' has matching ')' to its right; in
    addition no unmatched ')' allowed. Defect count = n - 2k."""
    results = []
    def rec(seq, opens, closes):
        if len(seq) == n:
            if opens == k and closes == k:
                results.append(tuple(seq))
            return
        # try '('
        if opens < k:
            rec(seq + ['('], opens + 1, closes)
        # try ')'
        if closes < opens:
            rec(seq + [')'], opens, closes + 1)
        # try defect '.'
        if (n - len(seq) - 1) >= 2 * (k - opens) + (opens - closes):
            # i.e. there's still room to finish opens/closes
            rec(seq + ['.'], opens, closes)
    rec([], 0, 0)
    return results

def seq_to_pairs(seq):
    """Convert paren sequence to dict: position -> partner (or None for defect)."""
    pairs = {i: None for i in range(len(seq))}
    st = []
    for i, c in enumerate(seq):
        if c == '(':
            st.append(i)
        elif c == ')':
            j = st.pop()
            pairs[i] = j
            pairs[j] = i
    return pairs

def apply_e(seq, i, delta):
    """
    Apply TL generator e_i (i in 0..n-2) to a link-pattern basis element.
    e_i caps strands at positions i and i+1.
    Returns dict basis_seq -> coefficient.
    """
    n = len(seq)
    pairs = seq_to_pairs(seq)
    a, b = i, i + 1
    pa, pb = pairs[a], pairs[b]

    # Case A: a and b already paired with each other -> e_i acts as delta * id (on that link)
    if pa == b:
        return {seq: delta}

    # Build new pairing:
    # Remove edges incident to a or b, then add edge (a,b), and connect their
    # former partners pa <-> pb (if both exist).
    new_pairs = dict(pairs)
    # remove old
    for x in (a, b):
        if new_pairs[x] is not None:
            y = new_pairs[x]
            new_pairs[y] = None
        new_pairs[x] = None
    # add cap
    new_pairs[a] = b
    new_pairs[b] = a
    # connect former partners
    if pa is not None and pb is not None and pa != b and pb != a:
        new_pairs[pa] = pb
        new_pairs[pb] = pa
    # If one was defect and the other had a partner, that partner becomes defect.
    # That's handled because new_pairs[partner] was set to None above.

    # Check whether the result is still a valid non-crossing pattern with the
    # SAME number of defects (i.e. doesn't change k). TL_n preserves cell modules
    # only when the number of through-strings doesn't decrease, but on cell
    # modules with the "small" through-strands convention, generators can act
    # as zero when they would reduce defect count below k.
    # Defects = positions with partner None.
    defects = sum(1 for v in new_pairs.values() if v is None)
    seq_defects = sum(1 for c in seq if c == '.')
    if defects != seq_defects:
        return {}  # Acting on cell module: kill

    # Convert back to sequence form (well-formed nested parens with defects).
    new_seq = []
    for x in range(n):
        if new_pairs[x] is None:
            new_seq.append('.')
        elif new_pairs[x] > x:
            new_seq.append('(')
        else:
            new_seq.append(')')
    new_seq = tuple(new_seq)
    return {new_seq: 1.0}


def build_H(n, k, delta):
    basis = basis_sequences(n, k)
    idx = {b: i for i, b in enumerate(basis)}
    d = len(basis)
    H = np.zeros((d, d))
    for j, b in enumerate(basis):
        for i in range(n - 1):
            res = apply_e(b, i, delta)
            for b2, c in res.items():
                if b2 in idx:
                    H[idx[b2], j] += c
    return H, basis


print("Spectrum of H = sum_i e_i on cell module W_{n,k} of TL_n")
print(f"q = e^(i*pi/10), delta = {DELTA:.6f}\n")

target = float(mpi / (10 * msqrt(2)))
hits = []
for n in range(2, 9):
    for k in range(0, n // 2 + 1):
        H, basis = build_H(n, k, DELTA)
        if H.shape[0] == 0:
            continue
        eigs = np.sort(np.linalg.eigvalsh((H + H.T)/2))   # symmetrize for stability
        # Also try the raw eigenvalues (may be complex if H is non-symmetric)
        eigs_raw = np.linalg.eigvals(H)
        all_eigs = np.concatenate([eigs, np.real(eigs_raw)])
        print(f"  n={n}, k={k}, dim={H.shape[0]}: lowest 4 eigs = {sorted(eigs)[:4]}")
        for e in eigs:
            for scale in [1.0, 1/n, 1/(n-1), 1/(2*n), 1/n**2]:
                v = e * scale
                if abs(abs(v) - target) < 0.01:
                    hits.append((n, k, e, scale, v))

print()
print("HITS within 0.01 of pi/(10*sqrt(2)) ~= 0.22214:")
for h in hits:
    print(f"  n={h[0]} k={h[1]} eig={h[2]:.6f} scaled by {h[3]} -> {h[4]:.6f}")
if not hits:
    print("  (none)")
