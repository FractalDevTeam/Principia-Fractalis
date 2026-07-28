# Independent numerical test of ch24's spectral rank mechanism (2026-07-28)

Test: discretized 𝒯_E (grid 240, primes < 1500, α = 3π/4, linear
interpolation for f(x/p), a_p by character sums) on four curves whose
ranks are now KERNEL-VERIFIED lower bounds in the corpus (11a1 r=0 control,
37a1 r=1, 389a1 r=2, 5077a1 r=3).

## Finding 1 — the Rank Formula as stated shows NO signal
Multiplicity of eigenvalues within 0.05 of φ/e ≈ 0.59524 (Hermitian part):
r=0 → 3, r=1 → 11, r=2 → 3, r=3 → 10. No correspondence with rank under
this natural discretization. (Not a continuum refutation, but the claimed
"100% success, conductor < 1000" is not reproduced by this test.)

## Finding 2 — the operator DOES carry a rank signal, elsewhere
Largest |eigenvalue| of the complex operator:
  r=0: 0.3188   r=1: 2.5747   r=2: 4.4835   r=3: 6.4893
Monotone in rank, increment ≈ 2 per rank (fit ≈ 2.05·rank + 0.4) across
all four curves. This matches the CLASSICAL Mestre–Nagao phenomenon:
a_p-biased sums weighted by 1/p encode rank (conditionally on BSD/GRH).
So ch24's core intuition — rank is spectrally readable from a_p/p data —
has a genuine numerical footprint; the specific φ/e-multiplicity
formulation does not, in this test. The dominant-eigenvalue signal is
the version worth developing (robustness in PMAX/grid untested — do that
first; expected slow drift per the classical heuristic).

Script inline in the session transcript; rerun-able in ~40 lines
(sympy primerange + numpy eigvals).
