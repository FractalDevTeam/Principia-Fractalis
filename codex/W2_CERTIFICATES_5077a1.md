# W2 certificates — 5077a1 quasi-parallelogram Bézout ground truth

Computed and verified 2026-07-30 (sympy, `expand()==0` on every identity, plus
exact-rational group-law checks on 10 distinct point pairs built from
`P = (-2, 3)`). Pure computation, no Lean. This is the 5077a1 analogue of
`codex/W2_CERTIFICATES_389a1.md`; the rank-3 target needs it because r156 gave
5077a1 a canonical height but no parallelogram law.

## 1. Setup (all verified)

Curve 5077a1: `y^2 + y = x^3 - 7x + 6`, `(a1,a2,a3,a4,a6) = (0,0,1,-7,6)`.
With `x1 = a1/b1`, `x2 = a2/b2` reduced, `x3 = x(P1+P2)` and `x4 = x(P1-P2)`
are the two roots of `DD*T^2 - S*T + P = 0`, where (bihomogeneous, bidegree
(2,2) in the pairs `(a1,b1)`, `(a2,b2)`):

```
DD = a1**2*b2**2 - 2*a1*a2*b1*b2 + a2**2*b1**2
S  = 2*a1**2*a2*b2 + 2*a1*a2**2*b1 - 14*a1*b1*b2**2 - 14*a2*b1**2*b2 + 25*b1**2*b2**2
P  = a1**2*a2**2 + 14*a1*a2*b1*b2 - 25*a1*b1*b2**2 - 25*a2*b1**2*b2 + 49*b1**2*b2**2
```

Affine forms: `s(x1,x2) = 2*x1^2*x2 + 2*x1*x2^2 - 14*x1 - 14*x2 + 25`,
`p(x1,x2) = x1^2*x2^2 + 14*x1*x2 - 25*x1 - 25*x2 + 49`.

Derivation used (`s = x3+x4`, `p = x3*x4`, `dd = (x1-x2)^2`), with `a1 = a2 = 0`
so `x(P+Q) = lam^2 - x1 - x2`, and `negY x y = -y - 1` since `a3 = 1`:

- `lam_+ * lam_- = ((y1^2+y1) - (y2^2+y2))/dd = (x1^3-x2^3-7(x1-x2))/dd
   = (x1^2+x1*x2+x2^2-7)/(x1-x2)`
- `lam_+^2 + lam_-^2 = (2*x1^3+2*x2^3-14*x1-14*x2+25)/dd`
- hence `s*dd = T - 2*(x1+x2)*dd` and `p*dd = Q^2 - (x1+x2)*T + (x1+x2)^2*dd`
  with `Q = x1^2+x1*x2+x2^2-7`, `T = 2*x1^3+2*x2^3-14*x1-14*x2+25`.

Verified facts:

- V1-V3: `b1^2*b2^2 * {s,p,(x1-x2)^2}(a1/b1, a2/b2)` equal `S`, `P`, `DD`.
- V4-V5 (diagonal, affine): `s(x,x) = g(x) = 4x^3-28x+25` and
  `p(x,x) = f(x) = x^4+14x^2-50x+49`, EXACTLY the r144 duplication pair.
  (This is why the diagonal degeneration is what drives the gcd bound.)
- V6: `Res(f,g) = 5077^2 = 25775929` (nonzero, so certificates exist).
  Same shape as 389a1, where `Res(f,g) = 389^2`.
- V7-V8 (diagonal, homogeneous): `S(a,b,a,b) = b*G3(a,b)` and
  `P(a,b,a,b) = F(a,b)` with the r144 forms
  `F(a,b) = a^4+14a^2b^2-50ab^3+49b^4`, `G3(a,b) = 4a^3-28ab^2+25b^3`.
- V9: `DD`, `S`, `P` are each invariant under swapping `(a1,b1) <-> (a2,b2)`.
- V10 (group-law sanity): for the 10 distinct pairs drawn from
  `{P, 2P, 3P, 4P, 5P}`, `P = (-2,3)`, the actual `x(P1+P2)` and `x(P1-P2)`
  from the Weierstrass group law satisfy `x3+x4 = S/DD` and `x3*x4 = P/DD` in
  exact rational arithmetic. Sign conventions confirmed.

## 2. Level-1 certificates: eliminating (a1,b1), minimal exponent m = 2

The 3x3 matrix `M` of `(a1^2, a1*b1, b1^2)`-coefficients of `(DD, S, P)`
(entries in `ZZ[a2,b2]`):

```
M = [[    b2^2,          -2*a2*b2,              a2^2        ],
     [ 2*a2*b2,      2*a2^2 - 14*b2^2,   -14*a2*b2 + 25*b2^2 ],
     [    a2^2,   14*a2*b2 - 25*b2^2,    -25*a2*b2 + 49*b2^2 ]]
```

`det M = -R6(a2,b2)` where

```
R6(a,b) = 2*a**6 - 70*a**4*b**2 + 250*a**3*b**3 - 490*a**2*b**4 + 350*a*b**5 + 61*b**6
```

`R6` is irreducible over `QQ` and has content 1 (sympy `factor_list`).
Compare 389a1's `R6 = 2a^6+4a^5b-20a^4b^2+10a^3b^3-30a^2b^4-8ab^5+11b^6` —
same degree, same leading coefficient 2, also irreducible.

Cramer cofactors, with `u,v,w` in `ZZ[a2,b2]` of degree 4. **Both identities
verified `expand()==0`:**

**cert_b1**: `u*DD + v*S + w*P = R6(a2,b2) * b1^2`
```
u =  2*a2**4 - 42*a2**2*b2**2 + 50*a2*b2**3
v =  2*a2**3*b2 + 14*a2*b2**3 - 25*b2**4
w = -6*a2**2*b2**2 + 14*b2**4
```
**cert_a1**: `u*DD + v*S + w*P = R6(a2,b2) * a1^2`
```
u =  50*a2**3*b2 - 294*a2**2*b2**2 + 350*a2*b2**3 + 61*b2**4
v = -14*a2**3*b2 + 75*a2**2*b2**2 - 98*a2*b2**3
w =  2*a2**4 - 42*a2**2*b2**2 + 50*a2*b2**3
```

Note `w` of `cert_a1` equals `u` of `cert_b1` (both are the `(1,1)`-cofactor).

`m = 2` is optimal: `m = 1` would force a common projective zero of the three
quadratic forms. Since both right-hand sides carry the SAME form `R6`, for
coprime `(a1,b1)` any common divisor of `DD, S, P` divides `R6(a2,b2)`
directly (combine `gcd(a1^2, b1^2) = 1`). By V9 it also divides `R6(a1,b1)`.

**These cofactors are far smaller than 389a1's** (degree 4 with coefficients
<= 350, against degree 7 with coefficients ~10^6 there), because the level-1
step here needs no pairwise resultant route.

## 3. Level-2 resultants (control of R6 at coprime (a2,b2))

Dehomogenizing by `b2` and taking resultants in `ZZ[t]`:

| pair | resultant | factorization |
|---|---|---|
| `(F, G3)`  | `25775929`      | `5077^2` |
| `(R6, F)`  | `81790244708125`| `5^4 * 5077^3` |
| `(R6, G3)` | `1046915132264` | `2^3 * 5077^3` |

So the achievable level-2 constants are `5077^3` times a small unit factor
(`5^4` or `2^3`), exactly parallel to 389a1 (`389^3` there, with a factor 2
appearing in one corner). The 5077-power structure is identical; only the
small cofactor differs.

**Content bound to target:** `gcd(DD, S, P) | 5077^3` for coprime pairs,
matching the 389a1 result. As there, the Lean layer may take the cheaper
`5077^4` via the squaring trick rather than assembling the full corner
certificates — the corner cofactors are the expensive object, and a looser
constant costs nothing downstream (it enters only inside a log).

## 4. Size bounds (coefficient absolute sums) — verified

```
|DD| <=   4 * H1^2 * H2^2      coeffs  1, -2, 1
|S|  <=  57 * H1^2 * H2^2      coeffs  2, 2, -14, -14, 25
|P|  <= 114 * H1^2 * H2^2      coeffs  1, 14, -25, -25, 49
```

389a1 for comparison: `4`, `17`, `10`. The `114` here is not a coincidence:
`p(t,t) = f(t)` and `f`'s coefficient sum is `1+14+50+49 = 114`, which is also
r146's upper duplication coefficient. Consistent cross-check.

Consequences for the downstream stones (the r148f/r148g analogues):

- `max(|DD|, |S|, |P|) <= 114 * H1^2 * H2^2`, so by the quadratic-root height
  lemma (r148e, curve-independent, reusable as-is) the product bound is
  `h(x3)*h(x4) <= 2*114 * H1^2*H2^2 = 228 * H1^2 * H2^2`
  (389a1: `34 = 2*17`).
- The free lower bound follows by applying the upper bound to the pair
  `(P1+P2, P1-P2)`, whose sum and difference are `2*P1` and `2*P2` — the same
  trick as r148g, no new certificate needed.

## 5. What is NOT yet done

- No Lean file yet for any of this (r157 onward).
- No secant bridge for 5077a1 (the r148d analogue): the two polynomial
  identities `N3 + N4 - S = 2*E1 + 2*E2` and `N3*N4 - dd*P = c1*E1 + c2*E2`
  need their explicit `c1, c2` computed for this curve.
- No parallelogram law, no pairing, no regulator, no rank-3 statement.
- Torsion-triviality for 5077a1 is NOT available by the r155 route at
  reasonable cost: the height bound there is `kappa^(1/3) = 47` (since
  `47^3 = 103823 <= 105754 < 110592 = 48^3`), against 12 for 389a1, so the
  enumeration is roughly 2800 candidates rather than 183 and the two-doubling
  escape is not known to be as clean. Expect to carry explicit per-point
  non-torsion certificates instead.

Generator: the sympy session is reproduced in the commit message of this file;
every identity above was checked by `expand()==0`, and the group-law facts by
exact `Fraction` arithmetic.
