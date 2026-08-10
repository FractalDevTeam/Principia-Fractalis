#!/usr/bin/env python3
"""
Diagnostic for the -lambda partner anomaly in the Gamma_0(9) transfer operator.

Context.  codex/rh_gamma09.py, Phase 1c: the 8-dimensional "level-9-new" block
of P.L (trivial character) emits an exact -lambda for every +lambda, so there
is one spurious opposite-parity zero at every certified spectral parameter.
Absent at level 3 (codex/rh_gamma03_m2.py).  Logged as unexplained.

This script does NOT modify rh_gamma09.py; it imports it.

STEP 1  odd-power traces on each invariant block.  If the spectrum of a block
        is symmetric under lambda -> -lambda then tr(X^k) = 0 for odd k.  That
        is far cheaper than eigenvalues.  Controls: the level-1 (1-dim) and
        level-3-new (3-dim) sub-blocks of the 4-dim old block, and the whole
        Gamma_0(3) operator from M2.

STEP 2  the grading operator G, found constructively, then verified:
        G^2 = 1 and G (P L) G = -(P L) on the new block.

STEP 3  identification.  Gamma_0(9) is NORMAL in Gamma_0(3) -- the map
            phi(a b; c d) = (c/3) * d^{-1}  mod 3
        is a homomorphism Gamma_0(3) -> Z/3 with kernel Gamma_0(9).  So
        X_0(9) -> X_0(3) is a Z/3 Galois cover and Gamma_0(3) sits inside the
        normalizer of Gamma_0(9) in PSL(2,R).  This is the h = 3 phenomenon
        (h = largest divisor of 24 with h^2 | N; N = 9 -> h = 3, N = 3 -> h = 1),
        i.e. exactly the "larger normalizer" hypothesis on record.
        Left multiplication by gamma_0 = (1 0; 3 1) is well defined on
        Gamma_0(9)\\PSL(2,Z) because Gamma_0(9) is normal in Gamma_0(3), and it
        commutes with the right action, hence with rho.  Call it U, U^3 = 1.
        The 12-dim permutation rep splits into U-isotypic pieces 4 + 4 + 4:
            U = 1   -> Ind_{Gamma_0(3)} 1          (the "old" 4-dim block)
            U = w   -> Ind_{Gamma_0(3)} psi        }  together the 8-dim
            U = w^2 -> Ind_{Gamma_0(3)} psi-bar    }  "level-9-new" block
        j = diag(1,-1) sends phi -> -phi, so P swaps the w and w^2 pieces while
        L preserves each.  Hence P.L is block-OFF-DIAGONAL [[0,A],[B,0]] on the
        new block and
            G = (U - U^2)/(w - w^2)   ( = +1 on the w piece, -1 on w^2, 0 else )
        satisfies G^2 = 1 there and G (P L) G = -(P L).  Both listed candidate
        explanations -- "V (+) V* with P.L off-diagonal" and "the normalizer of
        Gamma_0(p^2) is larger" -- are the same fact.

STEP 4  does it contaminate Phase 2 (the 29/29)?  The chi-twisted operator is
        the one Phase 2 uses.  chi(d) is NOT invariant under Gamma_0(3)-
        conjugation (conjugating by gamma_0 sends d -> d - 3b), so U does not
        act on Ind(chi) at all and the grading cannot exist there.  Measured
        three ways: U-commutator for chi, odd traces of the full chi operator,
        and the +-1 spectrum of P.L^chi at four of the 29 targets.

Usage:  rh_gamma09_anomaly.py [--all]
Output: codex/rh_gamma09_anomaly_results.txt  (APPENDED)
"""
import os
import sys
import time

import numpy as np
import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rh_gamma09 as g9                     # noqa: E402  (imported, never edited)

OUTPATH = os.path.join(HERE, "rh_gamma09_anomaly_results.txt")
_OUT = None


def log(msg=""):
    global _OUT
    if _OUT is None:
        _OUT = open(OUTPATH, "a")
    print(msg, flush=True)
    _OUT.write(msg + "\n")
    _OUT.flush()


W = np.exp(2j*np.pi/3)
DIM = g9.DIM                                 # 12
GAM0 = (1, 0, 3, 1)                          # in Gamma_0(3), phi = 1

# certified Gamma_0(3) spectral parameters, copied from rh_gamma09.GAMMA03
GAMMA03 = g9.GAMMA03


# ============================ group theory ===================================
def phi3(g):
    """phi(a b; c d) = (c/3)*d^{-1} mod 3 on Gamma_0(3); kernel = Gamma_0(9)."""
    a, b, c, d = g
    assert c % 3 == 0
    return ((c//3) * pow(d % 3, -1, 3)) % 3


def check_normal_subgroup():
    log("STEP 3a  Gamma_0(9) normal in Gamma_0(3): phi is a homomorphism onto Z/3")
    els = []
    for a in range(-6, 7):
        for b in range(-6, 7):
            for c in range(-4, 5):
                for d in range(-6, 7):
                    if a*d - b*(3*c) == 1:
                        els.append((a, b, 3*c, d))
    bad = 0
    for g in els[:400]:
        for h in els[:400]:
            gh = g9.mul(g, h)
            if (phi3(gh) - phi3(g) - phi3(h)) % 3 != 0:
                bad += 1
    log(f"  homomorphism test on 400x400 pairs of Gamma_0(3): {bad} failures")
    img = sorted({phi3(g) for g in els})
    log(f"  image of phi: {img}   kernel = {{c = 0 mod 9}} = Gamma_0(9)")
    log(f"  gamma_0 = (1 0; 3 1): phi = {phi3(GAM0)}   (a generator)")
    # j = diag(1,-1) conjugation flips phi
    flips = all((phi3(g9.sigma(g)) + phi3(g)) % 3 == 0 for g in els[:600])
    log(f"  phi(j g j^-1) = -phi(g) on 600 elements: {flips}")
    log("")
    return bad == 0 and flips


def deck_perm():
    """The permutation of the 12 cosets induced by LEFT multiplication by
    gamma_0.  Well defined because Gamma_0(9) is normal in Gamma_0(3)."""
    return [g9.coset(g9.mul(GAM0, g9.REPS[i])) for i in range(DIM)]


def deck_matrix(perm):
    U = np.zeros((DIM, DIM), dtype=complex)
    for i in range(DIM):
        U[perm[i], i] = 1.0
    return U


def isotypic_basis(perm):
    """Unitary 12x12 B whose columns are U-eigenvectors, grouped
    [4 with eigenvalue 1 | 4 with w | 4 with w^2].  Within a size-3 orbit
    (i, perm(i), perm^2(i)) the vector with weights w^{-k m} has U-eigenvalue
    w^k."""
    orbits, seen = [], set()
    for i in range(DIM):
        if i in seen:
            continue
        o = [i, perm[i], perm[perm[i]]]
        assert perm[o[2]] == i, "deck permutation is not of order 3"
        seen.update(o)
        orbits.append(o)
    cols = []
    for k in (0, 1, 2):
        for o in orbits:
            v = np.zeros(DIM, dtype=complex)
            for m, idx in enumerate(o):
                v[idx] = W**(-k*m)
            cols.append(v/np.sqrt(3.0))
    return np.array(cols).T, orbits


def refine_old_basis(B):
    """Rotate the first four columns (U-invariant block) so that column 0 is
    the constant function (the level-1 line) and columns 1..3 span the
    level-3-new part."""
    B = B.copy()
    seed = np.zeros((4, 4), dtype=complex)
    seed[:, 0] = 0.5
    seed[:, 1:] = np.eye(4)[:, :3]
    Q, _ = np.linalg.qr(seed)
    Q = Q * (np.abs(np.diag(Q))/np.diag(Q))      # fix phases
    B[:, :4] = B[:, :4] @ Q
    return B


def grading(U):
    return (U - U @ U)/(W - W**2)


# ============================ block machinery ================================
def compress(Xfull, B, N):
    Bk = np.kron(B, np.eye(N))
    return Bk.conj().T @ Xfull @ Bk


BLOCKS = [("level-1     (1-dim)", 0, 1),
          ("level-3-new (3-dim)", 1, 4),
          ("level-9-new (8-dim)", 4, 12)]


def block_report(Xb, N, label, s):
    log(f"  {label}   s = {mp.nstr(s, 12)}   N = {N}")
    log("    | block | dim | |tr X| | |tr X^2| | |tr X^3| | |tr X^5| | "
        "sum|lam| | sum|lam|^3 | odd/scale |")
    log("    |---|---|---|---|---|---|---|---|---|")
    for name, a, b in BLOCKS:
        sub = Xb[a*N:b*N, a*N:b*N]
        ev = np.linalg.eigvals(sub)
        t1 = abs(np.trace(sub))
        p2 = sub @ sub
        t2 = abs(np.trace(p2))
        p3 = p2 @ sub
        t3 = abs(np.trace(p3))
        t5 = abs(np.trace(p3 @ p2))
        s1 = float(np.sum(np.abs(ev)))
        s3 = float(np.sum(np.abs(ev)**3))
        log(f"    | {name} | {(b-a)*N} | {t1:.3e} | {t2:.3e} | {t3:.3e} | "
            f"{t5:.3e} | {s1:.3e} | {s3:.3e} | {max(t1/s1, t3/s3):.2e} |")


def leakage(Xb, N):
    """How invariant are the three blocks under X?"""
    tot = np.linalg.norm(Xb)
    out = []
    for name, a, b in (("old 4-dim", 0, 4), ("new 8-dim", 4, 12)):
        M = np.zeros_like(Xb)
        M[a*N:b*N, :] = Xb[a*N:b*N, :]
        M[a*N:b*N, a*N:b*N] = 0
        out.append((name, np.linalg.norm(M)/tot))
    return out


# ============================ STEP 1 =========================================
def step1(rep, name, spoints, N):
    log("=" * 74)
    log(f"STEP 1 -- odd-power traces per invariant block, operator: {name}")
    log("=" * 74)
    log("If a block's spectrum is symmetric under lambda -> -lambda then every")
    log("ODD power trace vanishes identically.  sum|lam|^k is the no-cancellation")
    log("scale; odd/scale is the cancellation ratio (1 = no symmetry, 0 = exact).")
    log("")
    perm = deck_perm()
    U = deck_matrix(perm)
    B, orbits = isotypic_basis(perm)
    B = refine_old_basis(B)
    log(f"  deck permutation (left mult by gamma_0): {perm}")
    log(f"  orbits (= fibres of P^1(Z/9) -> P^1(Z/3)): {orbits}")
    log(f"  U^3 - 1: {np.linalg.norm(U @ U @ U - np.eye(DIM)):.2e}")
    rS, rT = g9.to_np(rep.rS), g9.to_np(rep.rT)
    log(f"  || U rho(S) - rho(S) U || = {np.linalg.norm(U@rS - rS@U):.3e}")
    log(f"  || U rho(T) - rho(T) U || = {np.linalg.norm(U@rT - rT@U):.3e}")
    Pn = rep.P_np
    log(f"  || P U P^-1 - U^-1 ||     = "
        f"{np.linalg.norm(Pn@U@np.linalg.inv(Pn) - np.linalg.inv(U)):.3e}")
    log("")
    for s in spoints:
        X = g9.PL_matrix(s, N, rep)
        Xb = compress(X, B, N)
        for nm, v in leakage(Xb, N):
            log(f"    block leakage out of the {nm} block: {v:.2e} (relative Frobenius)")
        block_report(Xb, N, "P.L", s)
        log("")
    return B, U


# ============================ STEP 2 =========================================
def step2(rep, name, spoints, N, B, U):
    log("=" * 74)
    log(f"STEP 2 -- the grading operator G, operator: {name}")
    log("=" * 74)
    G = grading(U)
    Pi_new = (2*np.eye(DIM) - U - U@U)/3.0
    log("  G = (U - U^2)/(w - w^2),  w = exp(2 pi i/3).")
    log(f"  || G^2 - Pi_new ||   = {np.linalg.norm(G@G - Pi_new):.3e}"
        "   (Pi_new = projector onto the 8-dim new block)")
    log(f"  || G - G^dagger ||   = {np.linalg.norm(G - G.conj().T):.3e}")
    log(f"  || G P + P G ||      = {np.linalg.norm(G@rep.P_np + rep.P_np@G):.3e}"
        "   (P anticommutes with G)")
    rS, rT = g9.to_np(rep.rS), g9.to_np(rep.rT)
    log(f"  || G rho(S) - rho(S) G || = {np.linalg.norm(G@rS - rS@G):.3e}")
    log(f"  || G rho(T) - rho(T) G || = {np.linalg.norm(G@rT - rT@G):.3e}")
    log("")
    log("  G written on the 12 coset basis (rows = cosets, real and imag parts")
    log("  of a Hermitian matrix supported on the 4 fibres):")
    for i in range(DIM):
        row = "  ".join(f"{G[i,j].real:+.3f}{G[i,j].imag:+.3f}j" if abs(G[i, j]) > 1e-12
                        else "     .      " for j in range(DIM))
        log(f"    {g9.PTS[i]}  {row}")
    log("")
    Gk = None
    for s in spoints:
        N_ = N
        X = g9.PL_matrix(s, N_, rep)
        Gk = np.kron(G, np.eye(N_))
        Pk = np.kron(Pi_new, np.eye(N_))
        Xn = Pk @ X @ Pk
        resid = np.linalg.norm(Gk @ X @ Gk + Xn)/np.linalg.norm(Xn)
        # off-diagonal form in the isotypic basis
        Xb = compress(X, B, N_)
        wblk = Xb[4*N_:8*N_, 4*N_:8*N_]
        w2blk = Xb[8*N_:, 8*N_:]
        offA = Xb[4*N_:8*N_, 8*N_:]
        offB = Xb[8*N_:, 4*N_:8*N_]
        sc = np.linalg.norm(Xb[4*N_:, 4*N_:])
        log(f"  s = {mp.nstr(s, 12)}, N = {N_}")
        log(f"    || G (P L) G + (P L)|new || / || (P L)|new || = {resid:.3e}")
        log(f"    new block in the (w, w^2) basis: ||diag w|| = "
            f"{np.linalg.norm(wblk)/sc:.3e}, ||diag w^2|| = "
            f"{np.linalg.norm(w2blk)/sc:.3e}, ||A|| = {np.linalg.norm(offA)/sc:.3e},"
            f" ||B|| = {np.linalg.norm(offB)/sc:.3e}")
        log("    -> P.L is [[0, A], [B, 0]] on the new block")
    log("")
    return G


# ============================ level-3 control ================================
def level3_control(N=24, tvals=("4.38805356322", "5.09874190873")):
    log("=" * 74)
    log("CONTROL -- the same trace test on M2's Gamma_0(3) operator")
    log("=" * 74)
    try:
        import rh_gamma03_m2 as m2
    except Exception as e:                                     # pragma: no cover
        log(f"  could not import rh_gamma03_m2: {e}")
        return
    m2.R = mp.mpf(3)/2
    Q = m2.split_basis()
    Ptw = m2.twist_P()
    reps = m2.rep_matrices(+1)
    log("  Gamma_0(3) is NOT normal in PSL(2,Z) (index 4, no homomorphism onto")
    log("  Z/2 or Z/4 with that kernel), so there is no deck grading to find.")
    log("  | s | dim | |tr X| | |tr X^2| | |tr X^3| | |tr X^5| | sum|lam| | odd/scale |")
    log("  |---|---|---|---|---|---|---|---|")
    for tv in tvals:
        s = mp.mpc(mp.mpf('0.5'), mp.mpf(tv))
        Lm = m2.twisted_op(s, N, Q, reps, Ptw)
        X = np.array([[complex(Lm[a, b]) for b in range(3*N)]
                      for a in range(3*N)], dtype=complex)
        ev = np.linalg.eigvals(X)
        t1 = abs(np.trace(X)); p2 = X@X; t2 = abs(np.trace(p2))
        p3 = p2@X; t3 = abs(np.trace(p3)); t5 = abs(np.trace(p3@p2))
        s1 = float(np.sum(np.abs(ev))); s3 = float(np.sum(np.abs(ev)**3))
        log(f"  | 0.5+{tv}i | {3*N} (rho3, level-3 new) | {t1:.3e} | {t2:.3e} |"
            f" {t3:.3e} | {t5:.3e} | {s1:.3e} | {max(t1/s1, t3/s3):.2e} |")
    log("")


# ============================ STEP 4 =========================================
def read_targets():
    return g9.read_targets()


def commutant_dim(rep, tol=1e-9):
    """dim {X : X rho(g) = rho(g) X}.  1 <=> irreducible; otherwise the sum of
    the squares of the multiplicities of the irreducible summands.
    vec(X M - M X) = (M^T (x) I - I (x) M) vec(X)."""
    A = []
    for M in (g9.to_np(rep.rS), g9.to_np(rep.rT)):
        A.append(np.kron(M.T, np.eye(DIM)) - np.kron(np.eye(DIM), M))
    sv = np.linalg.svd(np.vstack(A), compute_uv=False)
    return int(np.sum(sv < tol*max(sv)))


def chi_symmetry_probe(rep, name, N, spoints):
    log("=" * 74)
    log(f"STEP 4a -- can the grading exist for {name}?")
    log("=" * 74)
    perm = deck_perm()
    U = deck_matrix(perm)
    rS, rT = g9.to_np(rep.rS), g9.to_np(rep.rT)
    log(f"  || U rho(S) - rho(S) U || = {np.linalg.norm(U@rS - rS@U):.3e}"
        f"   (scale ||rho(S)|| = {np.linalg.norm(rS):.3f})")
    log(f"  || U rho(T) - rho(T) U || = {np.linalg.norm(U@rT - rT@U):.3e}")
    # is chi invariant under Gamma_0(3)-conjugation?
    log("  chi(d) under conjugation by gamma_0 = (1 0; 3 1):  d -> d - 3b")
    bad = []
    for gam in ((1, 1, 9, 10), (1, 2, 9, 19), (4, 1, 27, 7), (5, 3, 18, 11),
                (10, 1, 9, 1), (7, 3, 9, 4)):
        assert gam[0]*gam[3] - gam[1]*gam[2] == 1
        cg = g9.mul(g9.inv(GAM0), g9.mul(gam, GAM0))
        bad.append((gam, complex(rep.chi(gam[3])), complex(rep.chi(cg[3]))))
    log("    | gamma in Gamma_0(9) | chi(gamma) | chi(gamma_0^-1 gamma gamma_0) | equal |")
    log("    |---|---|---|---|")
    ninv = 0
    for gam, c1, c2 in bad:
        eq = abs(c1 - c2) < 1e-12
        ninv += eq
        log(f"    | {gam} | {c1.real:+.4f}{c1.imag:+.4f}j | "
            f"{c2.real:+.4f}{c2.imag:+.4f}j | {eq} |")
    log(f"  chi conjugation-invariant on {ninv}/{len(bad)} test elements")
    log("")
    log(f"  commutant of <rho(S), rho(T)>, {name}: dimension {commutant_dim(rep)}"
        "   (1 = irreducible; sum of squares of multiplicities otherwise)")
    log(f"  commutant for the trivial character, same method: "
        f"{commutant_dim(g9.Rep(0))}   (= 1+3+4+4, four inequivalent summands)")
    log("")
    log("  Full-operator odd-power traces (no block structure assumed):")
    log("  | s | N | |tr X| | |tr X^2| | |tr X^3| | |tr X^5| | sum|lam| | sum|lam|^3 |"
        " odd/scale |")
    log("  |---|---|---|---|---|---|---|---|---|")
    for s in spoints:
        X = g9.PL_matrix(s, N, rep)
        ev = np.linalg.eigvals(X)
        t1 = abs(np.trace(X)); p2 = X@X; t2 = abs(np.trace(p2))
        p3 = p2@X; t3 = abs(np.trace(p3)); t5 = abs(np.trace(p3@p2))
        s1 = float(np.sum(np.abs(ev))); s3 = float(np.sum(np.abs(ev)**3))
        log(f"  | {mp.nstr(s, 12)} | {DIM*N} | {t1:.3e} | {t2:.3e} | {t3:.3e} |"
            f" {t5:.3e} | {s1:.3e} | {s3:.3e} | {max(t1/s1, t3/s3):.2e} |")
    log("")


def pairing_defect(X, k=18, tol=1e-8):
    """For the k eigenvalues of largest modulus, how close is -lambda to being
    in the spectrum?  Returns (n_paired, max_defect) with defect measured
    relatively, min_j |lambda_i + lambda_j| / |lambda_i|."""
    full = np.linalg.eigvals(X)
    ev = full[np.argsort(-np.abs(full))][:k]
    d = [float(np.min(np.abs(full + z)))/abs(z) for z in ev]
    return int(sum(x < tol for x in d)), max(d), k


def step4_targets(reps, N, ntarg=4):
    log("=" * 74)
    log("STEP 4b -- the 29/29: spectrum of P.L at the Phase-2 targets")
    log("=" * 74)
    tg = read_targets()
    # pick a spread of targets: strongest, weakest and two middling from the run
    picks = [mp.mpf('-9.884965957990'), mp.mpf('4.810386426624'),
             mp.mpf('-1.722046577574'), mp.mpf('7.562965053847')]
    picks = picks[:ntarg]
    log(f"  {len(tg)} targets in the file; probing {len(picks)}:")
    log("  det(1 - P L) = 0  <->  an eigenvalue of P.L at +1")
    log("  det(1 + P L) = 0  <->  an eigenvalue of P.L at -1")
    log("")
    for name, rep in reps:
        log(f"  --- operator: {name}, N = {N} ---")
        log("  | t | dist of nearest eig to +1 | to -1 | #eig within 1e-4 of +1 |"
            " of -1 | -lam partners among top 18 | worst rel. defect |")
        log("  |---|---|---|---|---|---|---|")
        for t in picks:
            s = mp.mpc(mp.mpf('0.25'), t)
            X = g9.PL_matrix(s, N, rep)
            ev = np.linalg.eigvals(X)
            dp = float(np.min(np.abs(ev - 1.0)))
            dm = float(np.min(np.abs(ev + 1.0)))
            np_ = int(np.sum(np.abs(ev - 1.0) < 1e-4))
            nm_ = int(np.sum(np.abs(ev + 1.0) < 1e-4))
            npair, worst, k = pairing_defect(X)
            log(f"  | {mp.nstr(t, 12)} | {dp:.3e} | {dm:.3e} | {np_} | {nm_} |"
                f" {npair}/{k} | {worst:.3e} |")
        log("")


def step4_localize(rep, name, N, B):
    """Where does the +1 eigenvector of P.L^chi live relative to the U-isotypic
    splitting?  The splitting is not rho^chi-invariant, so this is a coordinate
    statement, not a decomposition -- reported as such."""
    log("=" * 74)
    log(f"STEP 4c -- localization of the +1 eigenvector, operator: {name}")
    log("=" * 74)
    log("  The U-isotypic splitting 4+4+4 is NOT invariant for chi (measured in")
    log("  4a), so 'which block carries the hit' has no invariant meaning there.")
    log("  What can be measured is the mass of the +1 eigenvector in each")
    log("  U-isotypic coordinate patch, and the coset-fibre profile.")
    log("  | t | |eig-1| | mass in U=1 | mass in U=w | mass in U=w^2 |")
    log("  |---|---|---|---|---|")
    Bk = np.kron(B, np.eye(N))
    for t in (mp.mpf('-9.884965957990'), mp.mpf('4.810386426624'),
              mp.mpf('-1.722046577574'), mp.mpf('7.562965053847')):
        s = mp.mpc(mp.mpf('0.25'), t)
        X = g9.PL_matrix(s, N, rep)
        ev, V = np.linalg.eig(X)
        j = int(np.argmin(np.abs(ev - 1.0)))
        v = V[:, j]/np.linalg.norm(V[:, j])
        vb = Bk.conj().T @ v
        m = [float(np.linalg.norm(vb[a*N:b*N])**2) for a, b in ((0, 4), (4, 8), (8, 12))]
        log(f"  | {mp.nstr(t, 12)} | {abs(ev[j]-1.0):.3e} | {m[0]:.4f} | "
            f"{m[1]:.4f} | {m[2]:.4f} |")
    log("")


def step4_dets(reps, N, delta=0.30):
    """Direct determinant re-run of four Phase-2 targets, both factors."""
    log("=" * 74)
    log(f"STEP 4d -- determinant re-run of four Phase-2 targets, N = {N}")
    log("=" * 74)
    picks = [mp.mpf('-9.884965957990'), mp.mpf('4.810386426624'),
             mp.mpf('-1.722046577574'), mp.mpf('7.562965053847')]
    log("  | operator | t | factor | |det| at t | ctrl(t-0.3) | ctrl(t+0.3) | ratio |")
    log("  |---|---|---|---|---|---|---|")
    for name, rep in reps:
        for t in picks:
            at = g9.dets(mp.mpc(mp.mpf('0.25'), t), N, rep)
            cm = g9.dets(mp.mpc(mp.mpf('0.25'), t - delta), N, rep)
            cp = g9.dets(mp.mpc(mp.mpf('0.25'), t + delta), N, rep)
            for k, nm in ((0, "det(1-PL)"), (1, "det(1+PL)")):
                v = abs(at[k]); a = abs(cm[k]); b = abs(cp[k])
                log(f"  | {name} | {mp.nstr(t, 12)} | {nm} | {v:.4e} | {a:.3e} |"
                    f" {b:.3e} | {v/((a*b)**0.5):.3e} |")
    log("")


def step4_zeta_multiplicity(rep, N):
    """What the pairing does to Z = det(1-PL) det(1+PL) at a level-3 parameter:
    on the new block det(1 - (PL)^2) = det(1-AB) det(1-BA) = det(1-AB)^2, so the
    new block contributes a PERFECT SQUARE."""
    log("=" * 74)
    log("STEP 4e -- consequence for the Selberg-zeta multiplicity (Phase 1 side)")
    log("=" * 74)
    perm = deck_perm()
    B = refine_old_basis(isotypic_basis(perm)[0])
    log("  On the new block P.L = [[0,A],[B,0]], so")
    log("     det(1 - P L) det(1 + P L) |_new = det(1 - AB) det(1 - BA) = det(1-AB)^2")
    log("  i.e. the new block enters the Selberg zeta as a perfect SQUARE.")
    log("  | t | ||det(1-AB) - det(1-BA)||/|det(1-AB)| | det(1-PL)det(1+PL)|_new vs det(1-AB)^2 |")
    log("  |---|---|---|")
    for rstr, par, kind in GAMMA03[:4]:
        s = mp.mpc(mp.mpf('0.5'), mp.mpf(rstr))
        X = g9.PL_matrix(s, N, rep)
        Xb = compress(X, B, N)
        A = Xb[4*N:8*N, 8*N:]
        Bm = Xb[8*N:, 4*N:8*N]
        I4 = np.eye(4*N)
        dab = np.linalg.det(I4 - A@Bm)
        dba = np.linalg.det(I4 - Bm@A)
        Xn = Xb[4*N:, 4*N:]
        I8 = np.eye(8*N)
        prod = np.linalg.det(I8 - Xn)*np.linalg.det(I8 + Xn)
        log(f"  | {rstr} | {abs(dab-dba)/abs(dab):.3e} | "
            f"{abs(prod - dab*dab)/abs(dab*dab):.3e} |")
    log("")


# ============================ main ===========================================
if __name__ == "__main__":
    t_start = time.time()
    log("\n" + "#"*74)
    log(f"# ANOMALY RUN {time.strftime('%Y-%m-%d %H:%M:%S')}   "
        f"args={' '.join(sys.argv[1:])}")
    log("#"*74)

    NTR = 28          # trace/eigenvalue work: 12*28 = 336, seconds not minutes
    NDET = 64         # determinant re-run: matches Phase 2

    rep0 = g9.Rep(0)          # trivial character  (Phase 1 operator)
    rep1 = g9.Rep(1)          # chi                (Phase 2 operator)

    check_normal_subgroup()

    sp1 = [mp.mpc(mp.mpf('0.5'), mp.mpf('4.38805356322')),
           mp.mpc(mp.mpf('0.5'), mp.mpf('5.09874190873')),
           mp.mpc(mp.mpf('0.5'), mp.mpf('7.1'))]
    B, U = step1(rep0, "trivial character (Phase 1)", sp1, NTR)
    step2(rep0, "trivial character (Phase 1)", sp1[:2], NTR, B, U)
    level3_control()

    sp2 = [mp.mpc(mp.mpf('0.25'), mp.mpf('4.810386426624')),
           mp.mpc(mp.mpf('0.25'), mp.mpf('-1.722046577574')),
           mp.mpc(mp.mpf('0.25'), mp.mpf('7.1'))]
    chi_symmetry_probe(rep1, "chi (Phase 2)", NTR, sp2)
    step4_targets([("chi", rep1), ("trivial", rep0)], NTR)
    step4_localize(rep1, "chi (Phase 2)", NTR, B)
    step4_zeta_multiplicity(rep0, NTR)
    step4_dets([("chi", rep1)], NDET)

    log(f"# total wall time {time.time()-t_start:.1f}s")
    if _OUT:
        _OUT.close()
