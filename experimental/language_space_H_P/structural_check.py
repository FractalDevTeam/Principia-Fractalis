"""
Structural check: at N=3 alpha=sqrt(2) E=trivial, which sign-pattern s gives
the closest eigenvalue to pi/(10*sqrt(2))? Is it special?

Also: does the *imaginary part* of that eigenvalue go to zero? If H_P is supposed
to be self-adjoint at alpha=sqrt(2), the close-hit eigenvalue should have Im=0.
"""
import numpy as np
from hp_language_n3 import trivial_spectrum, all_strings_upto, weight, base3_digital_sum, encode

N = 3
alpha = np.sqrt(2)
target = np.pi / (10 * np.sqrt(2))
strings = all_strings_upto(N)
M = len(strings)
weights = np.array([weight(x, alpha) for x in strings], dtype=complex)

print(f"alpha = sqrt(2), target = pi/(10*sqrt(2)) = {target:.10f}")
print(f"N={N}, M={M}, 2^M = {2**M}")
print()
print("Per-string weights w(x) = (1/2^|x|) * exp(i*pi*sqrt(2)*D(encode(x))):")
for x, w in zip(strings, weights):
    n = encode(x)
    D = base3_digital_sum(n)
    print(f"  x={x!r:>8s}  |x|={len(x)}  encode={n:>3d}  D(b3)={D:>2d}  w={w.real:+.6f}{w.imag:+.6f}i")

# Top 10 closest eigenvalues by |Re - target|
eigs = trivial_spectrum(alpha, N)
order = np.argsort(np.abs(np.real(eigs) - target))
print(f"\nTop 10 closest |Re(eig) - target|:")
for k in order[:10]:
    signs = [(1 - 2 * ((k >> i) & 1)) for i in range(M)]
    print(f"  s_idx={k:>5d}  eig = {eigs[k].real:+.8f}{eigs[k].imag:+.8f}i  |Im|={abs(eigs[k].imag):.4f}  "
          f"signs={signs}")

# Check: does any eigenvalue have Im~0 AND Re~target?
near_real = np.abs(np.imag(eigs)) < 0.01
near_target_re = np.abs(np.real(eigs) - target) < 0.01
both = near_real & near_target_re
print(f"\nEigenvalues with |Im|<0.01 AND |Re-target|<0.01: {int(np.sum(both))} / {2**M}")
if np.any(both):
    for k in np.where(both)[0][:5]:
        print(f"  {eigs[k]}")
else:
    print("  NONE. The 'close hits' all have substantial imaginary parts.")
    # Show median |Im| among close hits
    close_re = np.abs(np.real(eigs) - target) < 0.01
    print(f"  Median |Im(eig)| among close-Re hits: {np.median(np.abs(np.imag(eigs[close_re]))):.4f}")
    print(f"  Min     |Im(eig)| among close-Re hits: {np.min(np.abs(np.imag(eigs[close_re]))):.4e}")
