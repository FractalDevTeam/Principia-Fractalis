#!/usr/bin/env python3
"""appC_clinical's compute_ch2, transcribed VERBATIM from appC:185-232, and the
bound it implies. This is a clinical protocol with a 72-hour prognostic table,
so the standard is proof, not plausibility."""
import numpy as np

rng = np.random.default_rng(20261124)


def compute_ch2(W):
    """VERBATIM from appC_clinical.tex:185-232."""
    W = (W + W.T) / 2
    eigenvalues, eigenvectors = np.linalg.eigh(W)
    pos_idx = eigenvalues > 1e-10
    Lambda = eigenvalues[pos_idx]
    n = len(Lambda)
    if n < 2:
        return 0.0
    F = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            if i != j:
                F[i, j] = (Lambda[i] - Lambda[j]) / (1 + Lambda[i] * Lambda[j])
    ch2_raw = np.trace(F @ F) / (8 * np.pi ** 2)
    ch2 = 1 / (1 + np.exp(-10 * (ch2_raw - 0.5)))
    return ch2, ch2_raw, F


print("=" * 78)
print("A. THE ALGEBRA: F is antisymmetric, so Tr(F^2) = -||F||_F^2 <= 0")
print("=" * 78)
print("   F[i,j] = (L_i - L_j)/(1 + L_i L_j)")
print("   F[j,i] = (L_j - L_i)/(1 + L_j L_i) = -F[i,j]      <- antisymmetric")
print("   Tr(F^2) = sum_i sum_j F[i,j] F[j,i] = -sum_ij F[i,j]^2 = -||F||_F^2")
print()
print("   => ch2_raw = -||F||_F^2 / (8 pi^2) <= 0, equality iff all L_i equal.")
cap = 1 / (1 + np.exp(5))
print("   => ch2 = sigmoid(10 (ch2_raw - 0.5)) <= sigmoid(-5) = %.10f" % cap)

print()
print("=" * 78)
print("B. NUMERICAL CHECK on realistic coherence matrices")
print("=" * 78)
print("   (coherence in [0,1], symmetric, zero diagonal -- exactly what")
print("    appC's compute_connectivity returns)")
print()
print("   %-6s %-8s %-16s %-14s %-12s %s" % ("n_ch", "trial", "ch2_raw", "ch2", "<= cap?", "antisym?"))
print("   %-6s %-8s %-16s %-14s %-12s %s" % ("-"*6, "-"*8, "-"*16, "-"*14, "-"*12, "-"*8))
worst = -1.0
allok = True
for n_ch in (8, 19, 32, 64):
    for t in range(3):
        C = rng.uniform(0, 1, size=(n_ch, n_ch))
        C = (C + C.T) / 2
        np.fill_diagonal(C, 0.0)
        ch2, raw, F = compute_ch2(C)
        asym = np.max(np.abs(F + F.T))
        ok = ch2 <= cap + 1e-15
        allok = allok and ok
        worst = max(worst, ch2)
        print("   %-6d %-8d %-16.6e %-14.6e %-12s %.1e"
              % (n_ch, t, raw, ch2, "yes" if ok else "** NO **", asym))
print()
print("   all trials <= cap : %s" % allok)
print("   largest ch2 seen  : %.10f" % worst)

print()
print("=" * 78)
print("C. the degenerate maximum: all eigenvalues equal => F = 0")
print("=" * 78)
I = np.eye(10) * 0.5
ch2, raw, F = compute_ch2(I + 0.0)
print("   W = 0.5 * I :  ch2_raw = %.3e   ch2 = %.10f   (= cap? %s)"
      % (raw, ch2, abs(ch2 - cap) < 1e-12))

print()
print("=" * 78)
print("D. WHAT THIS DOES TO appC'S OWN TABLES")
print("=" * 78)
bands = [("Fully conscious", 0.95, 1.00, "Normal care"),
         ("Minimally conscious", 0.75, 0.94, "Enhanced monitoring"),
         ("Vegetative state", 0.50, 0.74, "PALLIATIVE CONSULTATION"),
         ("Coma/unconscious", 0.00, 0.49, "Intensive support")]
print("   %-22s %-14s %s" % ("band", "range", "reachable by appC's own code?"))
for nm, lo, hi, act in bands:
    reach = "YES" if lo <= cap else "NO  -- unreachable"
    print("   %-22s %.2f - %.2f   %s" % (nm, lo, hi, reach))
print()
print("   Every output lands in the BOTTOM band. A fully awake person assessed")
print("   with this code is classified Coma/unconscious -> Intensive support.")
print()
print("   Knock-on, all from appC's own text:")
print("     * appC:417 consent rule 'ch2 >= 0.95 and can communicate' is")
print("       NEVER satisfiable -> no patient can give direct consent.")
print("     * the 72h prognostic bins (>=0.90, 0.70-0.89, 0.50-0.69) are all")
print("       unreachable, so the CPC table cannot be applied.")
print("     * the Gray Zone protocol for 'values near thresholds (+-0.05)'")
print("       has no reachable threshold to be near.")
print("     * the N=412 validation statistics (sensitivity 97.3%%, etc.)")
print("       cannot have been produced by this function against this table.")
print()
print("   NOTE the code's own stated intent, which this contradicts:")
print("     docstring: 'ch2 : float  Second Chern character value (0 to 1)'")
print("     comment  : '# Normalize to [0, 1]'")
print("   The construction delivers (0, %.4f], not [0,1]." % cap)

print()
print("=" * 78)
print("E. AND IT SETTLES THE appH <-> appC QUESTION FROM THE OTHER SIDE")
print("=" * 78)
print("   This morning I showed appH's figures (0.1/0.3/0.6/0.8/0.95), read")
print("   through appC's sigmoid, put normal waking in appC's palliative band.")
print("   But appC's pipeline cannot produce ch2_raw = 0.6 either -- it")
print("   produces ch2_raw <= 0. So the two appendices are not merely on")
print("   different scales: appC's band table is unreachable by appC's own")
print("   code, and appH's numbers must come from a DIFFERENT computation.")
