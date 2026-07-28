# W2 certificates — 389a1 quasi-parallelogram Bezout ground truth

Computed and verified 2026-07-28 (sympy 1.13.3, `expand()==0` on every identity,
plus 50-random-integer-point numeric checks). Pure computation, no Lean.
Stone W2 of the rank-2 independence arc
(`codex/RANK2_INDEPENDENCE_ARC_PLAN_2026-07-28.md`).

## 1. Setup (all verified)

Curve 389a1: `y^2 + y = x^3 + x^2 - 2x`. With `x1 = a1/b1`, `x2 = a2/b2` reduced,
`x3 = x(P1+P2)` and `x4 = x(P1-P2)` are the two roots of `DD*T^2 - S*T + P = 0`, where
(bihomogeneous, bidegree (2,2) in the pairs `(a1,b1)`, `(a2,b2)`):

```
DD = a1**2*b2**2 - 2*a1*a2*b1*b2 + a2**2*b1**2
S  = 2*a1**2*a2*b2 + 2*a1*a2**2*b1 + 4*a1*a2*b1*b2 - 4*a1*b1*b2**2 - 4*a2*b1**2*b2 + b1**2*b2**2
P  = a1**2*a2**2 + 4*a1*a2*b1*b2 - a1*b1*b2**2 - a2*b1**2*b2 + 3*b1**2*b2**2
```

Verified facts:

- V1-V3: `b1^2*b2^2 * {s,p,(x1-x2)^2}(a1/b1, a2/b2)` equal `S`, `P`, `DD` (the stated
  homogenizations are correct).
- V4-V5 (diagonal, affine): `S(x,1,x,1) = g(x) = 4x^3+4x^2-8x+1`, `P(x,1,x,1) = f(x) = x^4+4x^2-2x+3`.
- V6: `Res(f,g) = 389^2 = 151321` (nonzero, so certificates exist).
- V7-V8 (diagonal, homogeneous): `S(a,b,a,b) = b*G3(a,b)`, `P(a,b,a,b) = F(a,b)` with the
  r143 forms `F(a,b) = a^4+4a^2b^2-2ab^3+3b^4`, `G3(a,b) = 4a^3+4a^2b-8ab^2+b^3`.
- V9: `DD`, `S`, `P` are each invariant under swapping `(a1,b1) <-> (a2,b2)`.
- V10 (group-law sanity): for 4 exact rational point pairs built from P=(0,0), Q=(1,0)
  (namely (P,Q), (2P,Q), (P+Q,P), (2P,P+Q)), the actual `x(P1+P2)` and `x(P1-P2)` computed
  from the Weierstrass group law are roots of `DD*T^2 - S*T + P` — sign conventions confirmed.

## 2. Level-1 certificates: eliminating (a1,b1)

### 2a. Minimal exponent m = 2 (best possible; cofactors free of (a1,b1))

The 3x3 matrix M of `(a1^2, a1*b1, b1^2)`-coefficients of `(DD, S, P)` (entries in `ZZ[a2,b2]`)
has determinant `-R6` where

```
R6(a,b) = 2*a**6 + 4*a**5*b - 20*a**4*b**2 + 10*a**3*b**3 - 30*a**2*b**4 - 8*a*b**5 + 11*b**6
```

`R6` is irreducible over `QQ` (sympy factor). Cramer cofactors give, with `u,v,w` in `ZZ[a2,b2]`:

**cert1**: `u*DD + v*S + w*P = R6(a2,b2) * b1^2`
```
u = 2*a2**4 + 4*a2**3*b2 - 12*a2**2*b2**2 + 2*a2*b2**3
v = 2*a2**3*b2 + 4*a2*b2**3 - b2**4
w = -6*a2**2*b2**2 - 4*a2*b2**3 + 4*b2**4
```
**cert2**: `u'*DD + v'*S + w'*P = R6(a2,b2) * a1^2`
```
u' = 2*a2**3*b2 - 18*a2**2*b2**2 - 8*a2*b2**3 + 11*b2**4
v' = -4*a2**3*b2 + 3*a2**2*b2**2 - 6*a2*b2**3
w' = 2*a2**4 + 4*a2**3*b2 - 12*a2**2*b2**2 + 2*a2*b2**3
```

m = 2 is optimal: m = 1 would force a common projective zero of the three quadratic forms.
Note both sides produce the SAME form `R6`, so for coprime `(a1,b1)`:
`gcd(DD,S,P)(pt) | R6(a2,b2)` directly.

### 2b. Pairwise m = 3 certificates — the rho's are squares of the r143 forms

Resultant-route certificates `U*DD + V*X = rho * (b1|a1)^3`, `X in {S, P}`, cofactors of
bidegree (1,4):

**cert B-S**: `U*DD + V*S = rho_BS * b1^3`,  `rho_BS = (4*a2**3 + 4*a2**2*b2 - 8*a2*b2**2 + b2**3)**2`
```
U = 12*a1*a2**3*b2 + 8*a1*a2**2*b2**2 - 8*a1*a2*b2**3 + 16*a2**4*b1 + 32*a2**3*b1*b2 - 8*a2**2*b1*b2**2 - 34*a2*b1*b2**3 + 16*b1*b2**4
V = -6*a1*a2**2*b2**2 - 4*a1*a2*b2**3 + 4*a1*b2**4 + 10*a2**3*b1*b2 + 8*a2**2*b1*b2**2 - 12*a2*b1*b2**3 + b1*b2**4
```
**cert B-P**: `U*DD + V*P = rho_BP * b1^3`,  `rho_BP = (a2**4 + 4*a2**2*b2**2 - 2*a2*b2**3 + 3*b2**4)**2`
```
U = 2*a1*a2**5*b2 + 4*a1*a2**3*b2**3 - a1*a2**2*b2**4 + a2**6*b1 + 8*a2**4*b1*b2**2 - a2**3*b1*b2**3 + 13*a2**2*b1*b2**4 - 8*a2*b1*b2**5 + b1*b2**6
V = -2*a1*a2**3*b2**3 - 4*a1*a2*b2**5 + a1*b2**6 + 3*a2**4*b1*b2**2 + 8*a2**2*b1*b2**4 - 3*a2*b1*b2**5 + 3*b1*b2**6
```
**cert A-S**: `U*DD + V*S = rho_AS * a1^3`,  `rho_AS = b2**2*(4*a2**3 + 4*a2**2*b2 - 8*a2*b2**2 + b2**3)**2`
```
U = 4*a1*a2**6 + 16*a1*a2**5*b2 - 8*a1*a2**4*b2**2 - 62*a1*a2**3*b2**3 + 72*a1*a2**2*b2**4 - 16*a1*a2*b2**5 + a1*b2**6 - 8*a2**5*b1*b2 - 14*a2**4*b1*b2**2 + 52*a2**3*b1*b2**3 - 20*a2**2*b1*b2**4 + 2*a2*b1*b2**5
V = 6*a1*a2**5*b2 + 8*a1*a2**4*b2**2 - 20*a1*a2**3*b2**3 + 3*a1*a2**2*b2**4 - 2*a2**6*b1 - 4*a2**5*b1*b2 + 12*a2**4*b1*b2**2 - 2*a2**3*b1*b2**3
```
**cert A-P**: `U*DD + V*P = rho_AP * a1^3`,  `rho_AP = (a2**4 + 4*a2**2*b2**2 - 2*a2*b2**3 + 3*b2**4)**2`
```
U = a1*a2**5*b2 + 13*a1*a2**4*b2**2 - 16*a1*a2**3*b2**3 + 28*a1*a2**2*b2**4 - 12*a1*a2*b2**5 + 9*a1*b2**6 - 4*a2**4*b1*b2**2 + 15*a2**3*b1*b2**3 - 15*a2**2*b1*b2**4 + 18*a2*b1*b2**5
V = a1*a2**6 + 8*a1*a2**4*b2**2 - 5*a1*a2**3*b2**3 + 9*a1*a2**2*b2**4 - 4*a2**5*b1*b2 + 3*a2**4*b1*b2**2 - 6*a2**3*b1*b2**3
```

**rho structure (requirement 2):**

| certificate | rho | factorization |
|---|---|---|
| B-S | `rho_BS` | `G3(a2,b2)^2` |
| B-P | `rho_BP` | `F(a2,b2)^2` |
| A-S | `rho_AS` | `b2^2 * G3(a2,b2)^2` |
| A-P | `rho_AP` | `F(a2,b2)^2` |
| m=2 (both sides) | `R6` | irreducible sextic (new form) |

**The pairwise rho's are exactly (squares of) the r143 forms `F`, `G3` — the existing
r131/r143 certificates control them.** Specifically, r143's identity1/identity2 for 389a1
(`alpha*F + beta*G3 = 389*b^6`, `gamma*F + delta*(b*G3) = 389*a^7`) give
`gcd(F(a,b), G3(a,b)) | 389` at coprime points, hence `gcd(rho values) | 389^2`.

## 3. Level-2 certificates (control of the rho's at coprime (a2,b2))

Self-contained Bezout data in `(a2,b2)`; all verified `expand()==0`:

**L2 G3sq_Fsq[b2]**: `alpha*G3^2 + beta*F^2 = 58863869 * b2^13`  (58863869 = {389: 3})
```
alpha = -213248*a2**7 - 87440*a2**6*b2 - 1664288*a2**5*b2**2 + 208048*a2**4*b2**3 - 3974568*a2**3*b2**4 + 1776600*a2**2*b2**5 - 3611440*a2*b2**6 + 646397*b2**7
beta  = 3411968*a2**5 + 8222976*a2**4*b2 - 8104960*a2**3*b2**2 - 18346496*a2**2*b2**3 + 10175232*a2*b2**4 + 6468608*b2**5
```
**L2 G3sq_Fsq[a2]**: `alpha*G3^2 + beta*F^2 = 58863869 * a2^13`  (58863869 = {389: 3})
```
alpha = 2364492*a2**7 - 4291364*a2**6*b2 + 7644559*a2**5*b2**2 - 13259344*a2**4*b2**3 + 13436000*a2**3*b2**4 - 14569276*a2**2*b2**5 + 7076478*a2*b2**6 - 3820536*b2**7
beta  = 21031997*a2**5 - 7001920*a2**4*b2 - 39749656*a2**3*b2**2 + 34093044*a2**2*b2**3 - 7012334*a2*b2**4 + 424504*b2**5
```
**L2 R6_F[b2]**: `alpha*R6 + beta*F = 151321 * b2^9`  (151321 = {389: 2})
```
alpha = 378*a2**3 + 1768*a2**2*b2 + 2660*a2*b2**2 + 5303*b2**3
beta  = -756*a2**5 - 5048*a2**4*b2 - 1808*a2**3*b2**2 + 29014*a2**2*b2**3 + 25052*a2*b2**4 + 30996*b2**5
```
**L2 R6_F[a2]**: `alpha*R6 + beta*F = 151321 * a2^9`  (151321 = {389: 2})
```
alpha = 25516*a2**3 - 2896*a2**2*b2 + 7547*a2*b2**2 + 13506*b2**3
beta  = 100289*a2**5 - 96272*a2**4*b2 + 105654*a2**3*b2**2 + 215386*a2**2*b2**3 - 24671*a2*b2**4 - 49522*b2**5
```
**L2 R6_G3[b2]**: `alpha*R6 + beta*G3 = 151321 * b2^8`  (151321 = {389: 2})
```
alpha = -12544*a2**2 - 16352*a2*b2 + 18568*b2**2
beta  = 6272*a2**5 + 14448*a2**4*b2 - 57556*a2**3*b2**2 + 15916*a2**2*b2**3 - 95000*a2*b2**4 - 52927*b2**5
```
**L2 R6_G3[a2]**: `alpha*R6 + beta*G3 = 302642 * a2^8`  (302642 = {2: 1, 389: 2})
```
alpha = -29531*a2**2 + 23126*a2*b2 - 2590*b2**2
beta  = 90426*a2**5 - 72458*a2**4*b2 + 83824*a2**3*b2**2 - 59299*a2**2*b2**3 - 47186*a2*b2**4 + 28490*b2**5
```
**L2 rhoAS_rhoAP[b2]**: `alpha*rho_AS + beta*rho_AP = 58863869 * b2^15`  (58863869 = {389: 3})
```
alpha = -213248*a2**7 - 87440*a2**6*b2 - 1664288*a2**5*b2**2 + 208048*a2**4*b2**3 - 3974568*a2**3*b2**4 + 1776600*a2**2*b2**5 - 3611440*a2*b2**6 + 646397*b2**7
beta  = 3411968*a2**5*b2**2 + 8222976*a2**4*b2**3 - 8104960*a2**3*b2**4 - 18346496*a2**2*b2**5 + 10175232*a2*b2**6 + 6468608*b2**7
```
**L2 rhoAS_rhoAP[a2]**: `alpha*rho_AS + beta*rho_AP = 58863869 * a2^15`  (58863869 = {389: 3})
```
alpha = -11271377*a2**7 + 30529536*a2**6*b2 - 55748280*a2**5*b2**2 + 117672604*a2**4*b2**3 - 127791122*a2**3*b2**4 + 144711560*a2**2*b2**5 - 72776796*a2*b2**6 + 38622276*b2**7
beta  = 58863869*a2**7 - 290568920*a2**5*b2**2 + 107666964*a2**4*b2**3 + 403547474*a2**3*b2**4 - 346385576*a2**2*b2**5 + 71026316*a2*b2**6 - 4291364*b2**7
```

**Minimality (proved by integer-lattice HNF, i.e. exhaustive over all integer cofactors up
to the stated degree bounds, stable under raising the bound):**

- `(G3^2, F^2)`: minimal constant `389^3 = 58863869` (bounds 13/16/20 all give 389^3).
- `(G3, F)`: minimal constant `389` — confirms r143's identity1 is optimal.
- `(R6, F)`: minimal constant `389^2 = 151321`.

Mod-389 structure explaining the constants: `gcd(f, g) mod 389 = a^2 + 180a - 69` (an
irreducible quadratic over GF(389)), and the same quadratic divides `R6 mod 389`. Any
integer combination of the pairs above must therefore vanish mod 389 in its constant part.

## 4. Assembled corner certificates and the content bound

Composing level-1 x level-2 (`u = alpha*u1 + beta*u2`, `v = alpha*v1`, `w = beta*w2`) gives
four fully expanded, verified certificates `u*DD + v*S + w*P = D * (b1|a1)^3 * (b2|a2)^N`:

| corner | D | N | kappa(u) | kappa(v) | kappa(w) |
|---|---|---|---|---|---|
| `b1^3 * b2^13` | 389^3 | 13 | 1093696934 | 280559401 | 528888320 |
| `b1^3 * a2^13` | 389^3 | 13 | 2980085295 | 1184992589 | 1699169880 |
| `a1^3 * b2^15` | 389^3 | 15 | 2214049995 | 510784373 | 849419264 |
| `a1^3 * a2^15` | 389^3 | 15 | 90038635266 | 24962367151 | 29337064538 |

**Content bound (the W2 payoff):** for `gcd(a1,b1) = gcd(a2,b2) = 1`,
`gcd(DD, S, P)(a1,b1,a2,b2)` divides all four right-hand sides, hence divides
`389^3 = 58863869`. (Combine the two b1^3-corners to drop the `(b2|a2)^N`, the two
a1^3-corners likewise, then the pair to drop `b1^3, a1^3`.)
The expanded corner cofactors are reproducible from the L1/L2 blocks above by the stated
composition (a `ring`-checkable definition in Lean); their full expansions are in
`codex/W2_corner_cofactors_389a1.txt`, and the generating/verifying script is
`codex/w2_certificates_389a1_gen.py` (run with `/home/xluxx/ai-env/bin/python`).

## 5. kappa constants (coefficient sums, requirement 3)

| object | kappa |
|---|---|
| DD, S, P | 4, 17, 10 |
| m=2 cert1 (u, v, w) | 20, 7, 14 |
| m=2 cert2 (u', v', w') | 39, 13, 20 |
| R6 | 85 |
| cert B-S (U, V, rho) | 134, 45, 241 |
| cert B-P (U, V, rho) | 39, 24, 100 |
| cert A-S (U, V, rho) | 275, 57, 241 |
| cert A-P (U, V, rho) | 131, 36, 100 |
| L2 G3sq_Fsq[b2] (alpha, beta) | 12182029, 54730240 |
| L2 G3sq_Fsq[a2] (alpha, beta) | 66462049, 109313455 |
| L2 R6_F[b2] (alpha, beta) | 10109, 92674 |
| L2 R6_F[a2] (alpha, beta) | 49465, 591794 |
| L2 R6_G3[b2] (alpha, beta) | 47464, 242119 |
| L2 R6_G3[a2] (alpha, beta) | 55247, 381683 |
| L2 rhoAS_rhoAP[b2] (alpha, beta) | 12182029, 54730240 |
| L2 rhoAS_rhoAP[a2] (alpha, beta) | 599123551, 1282350483 |

## 6. Symmetry (requirement 4)

`DD`, `S`, `P` are invariant under the pair swap `(a1,b1) <-> (a2,b2)` (verified, V9).
Therefore every `(a2,b2)`-elimination certificate is the literal swap image of the
corresponding `(a1,b1)` one — same cofactor polynomials with variables swapped, same rho
forms now in `(a1,b1)`, same constants and kappas. Verified explicitly for the swap of
cert1: `u_s*DD + v_s*S + w_s*P = R6(a1,b1) * b2^2` passes `expand()==0`.

## 7. Sanity (requirement 5)

All 19 certificates evaluated at 50 random integer points in `[-40,40]^4`
(seed 20260728): every residual is exactly 0.

## 8. Obstructions

None. Everything requested was obtained in full:
- minimal-exponent (m=2) three-form certificates on both sides, with a single new
  irreducible sextic `R6` (controlled against F and G3 at level 2 with constant `389^2`);
- pairwise m=3 certificates whose rho's are exactly `G3^2`, `F^2`, `b2^2*G3^2`, `F^2` —
  i.e. controlled by the existing r131/r143 machinery;
- optimal level-2 constants (`389^3` for the square pair, proved minimal);
- the four-corner content bound `gcd(DD,S,P) | 389^3` at fully coprime points.

One caution for the Lean phase: the expanded corner cofactors have kappa ~ 10^9-10^10;
prefer composing the L1 and L2 identities as two separate `ring` lemmas over inlining the
expanded corners.

Generated and verified by `codex/w2_certificates_389a1_gen.py` (42 PASS assertions).
A compact machine-readable copy of all certificates was appended to the session
cohort_data_pack.txt (W2 389a1 block).

## SECANT BRIDGE certificates (computed 2026-07-28, remainder 0 both)

For 389a1, P₁=(x₁,y₁), P₂=(x₂,y₂) on-curve, x₁ ≠ x₂. With
  N3 := (y₁−y₂)² − (1+x₁+x₂)(x₁−x₂)²      [= dd·x(P₁+P₂)]
  N4 := (y₁+y₂+1)² − (1+x₁+x₂)(x₁−x₂)²    [= dd·x(P₁−P₂)]
  dd := (x₁−x₂)²,  E₁ := y₁²+y₁−x₁³−x₁²+2x₁,  E₂ likewise:

**SUM (trivial!):**  N3 + N4 − Sfnum = 2·E₁ + 2·E₂
  where Sfnum = 2x₁²x₂ + 2x₁x₂² + 4x₁x₂ − 4x₁ − 4x₂ + 1
  ⟹ Lean: `linear_combination 2*hE₁ + 2*hE₂`

**PRODUCT:**  N3·N4 − dd·Prnum = cP1·E₁ + cP2·E₂
  where Prnum = x₁²x₂² + 4x₁x₂ − x₁ − x₂ + 3 and
  cP1 = −x₁³ + 2x₁²x₂ − x₁² + 2x₁x₂² + 4x₁x₂ − 2x₁ − 2x₂³ − 2x₂² + y₁² + y₁ − 2y₂² − 2y₂
  cP2 = −4x₁³ + 2x₁²x₂ − 4x₁² + 2x₁x₂² + 4x₁x₂ + 4x₁ − x₂³ − x₂² − 2x₂ + y₂² + y₂
  ⟹ Lean: `linear_combination (cP1)*hE₁ + (cP2)*hE₂`

Both remainders are exactly 0 (sympy polynomial division). These are the
r148d inputs: they turn mathlib's `addX`/`slope` secant data into the
homogenizable Sf/Pf forms of r148a.
