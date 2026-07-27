# The α-Web as a System — Degrees of Freedom, Rank, and What Is Actually Pinned

**Date:** 2026-07-26
**Scope:** exact symbolic algebra over ℚ(π), plus a machine-checked Lean formalisation.
No claim retracted, no file deleted, no git commit.
**Companion artifacts:**
`codex/alpha_web_system.py` (sympy, reproducible) and
`PF_Lean4_Code/PF/AlphaWebDegreesOfFreedom_r124.lean` (builds; no `sorry`; kernel axioms only).
**Prior audit this builds on:** `codex/ALPHA_NP_DERIVABILITY_2026-07-25.md`.

---

## 0. VERDICT

> **Rank 8. Nine unknowns. One free dimension.**
>
> Treated as a system of simultaneous equations, the eleven cross-Millennium
> invariants of conjunct `C8` have a **one-dimensional** solution variety over
> ℚ(π). Exactly **8 of the 11 are independent**; three are strictly redundant.
>
> Seven of the nine α's are genuinely forced. **`α_BSD` is not constrained at
> all** — the eleven invariants are satisfied for *every* positive value of it,
> and `α_NS` follows it as `2·α_BSD`. The framework's `α_BSD = 3π/4` is an
> input the web does not supply, and the `3π/2` for `α_NS` is that same input.
>
> **The `1/4` is a free parameter, provably.** `α_NP` occurs in exactly one of
> the eleven invariants. Replacing `1/4` by an unknown `c` leaves the
> elimination ideal in `c` equal to `{0}`: no combination of the other ten
> invariants constrains it. Invariant 10 does not derive the offset — it
> inserts it.
>
> **The one genuine, non-circular pin in the whole web is `α_Hodge = φ`,**
> forced by `α_Hodge² = α_Hodge + 1` together with positivity. That equation is
> self-closing: it contains no imported constant.
>
> **How many independent assumptions does the framework actually make?**
> Counting numeric inputs rather than invariants: **three**, plus one genuine
> derivation.
> 1. `α_YM = 2` — spelled *five* different ways (as `9/4`, as `2π`, as the
>    factor `2`, as `3`, and as `α_Poincaré + 1` with the Perelman anchor).
>    Given the constant-free structural core, all five are the same assumption.
> 2. the offset `c = 1/4` in invariant 10.
> 3. the scale `α_BSD = 3π/4` — which is *outside* the web entirely.
> Plus: `α_Hodge = φ` (derived, not assumed).
>
> "Rigidity" is the wrong word. The accurate statement is
> **"consistent, and pinning seven of nine up to one free scale."**
> That is a weaker claim than the corpus makes — and, unlike the current claim,
> it is true and machine-checked.

---

## 1. THE SYSTEM

Source: `PF_Lean4_Code/PF/Referee/PrincipiaFractalisSubstrateTheorem.lean`
conjunct `C8` (lines 193–222), matching the capstone in
`PF_Lean4_Code/PF/CrossMillenniumSharedInvariants.lean:208–242`.

Nine unknowns: `α_Poincaré, α_P, α_RH, α_YM, α_Hodge, α_NP, α_NS, α_BSD, α_QG`.
`π` is carried as a transcendental constant; the coefficient field is ℚ(π)
(modelled in sympy as the rational function field `QQ(p)`, which is the correct
model — no nonzero polynomial over ℚ vanishes at π).

| # | invariant | polynomial form |
|---|---|---|
| I1 | `α_P² = α_YM` | `α_P² − α_YM` |
| I2 | `α_RH² = 9/4` | `α_RH² − 9/4` |
| I3 | `α_QG² = 2π` | `α_QG² − 2π` |
| I4 | `α_Hodge² = α_Hodge + 1` | `α_Hodge² − α_Hodge − 1` |
| I5 | `α_NS = 2·α_BSD` | `α_NS − 2α_BSD` |
| I6 | `α_NS = α_YM·α_BSD` | `α_NS − α_YM α_BSD` |
| I7 | `α_YM = α_Poincaré + 1` | `α_YM − α_Poincaré − 1` |
| I8 | `α_RH·α_NS = α_NS + α_BSD` | `α_RH α_NS − α_NS − α_BSD` |
| I9 | `α_RH·α_YM = 3` | `α_RH α_YM − 3` |
| I10 | `α_NP − α_Hodge = 1/4` | `α_NP − α_Hodge − 1/4` |
| I11 | `α_QG² = α_YM·π` | `α_QG² − α_YM π` |

Consistency is not in question — all eleven hold exactly at the framework's
9-tuple (verified symbolically, §2 of the script). The question is what they
determine.

---

## 2. RANK AND DEGREES OF FREEDOM

### 2.1 Gröbner basis

Reduced Gröbner basis of `I = ⟨I1,…,I11⟩` over ℚ(π), grevlex, **8 elements**:

```
a_P**2 - 2
a_NP**2 - 3*a_NP/2 - 11/16
a_QG**2 - 2*p
a_Poi - 1
a_RH - 3/2
a_YM - 2
a_Ho - a_NP + 1/4
-2*a_BSD + a_NS
```

Two things are immediately visible.

* **Only one variable, `a_BSD`, fails to appear in any leading monomial.**
* The basis spontaneously produces `a_NP² − (3/2)a_NP − 11/16 = 0`, i.e.
  **`16 α_NP² − 24 α_NP − 11 = 0`** — the corpus's "NP self-adjointness
  quadratic". Its provenance in the web is now explicit: it is I4 and I10
  composed, i.e. `(α_NP − 1/4)² = (α_NP − 1/4) + 1`. It contains exactly the
  information already in I4 + I10 and no more. This independently confirms
  §1.3 of the 2026-07-25 audit by a route that does not go through any Lean
  proof.

### 2.2 Dimension

Using the standard combinatorial criterion (Cox–Little–O'Shea Ch. 9, Thm 8):
`dim V(I)` is the largest cardinality of a variable subset `U` such that no
leading monomial of the Gröbner basis lies in `k[U]`.

```
dim V(I) = 1
maximal independent variable sets: [['a_BSD']]      (unique)
codim = 8
```

**Rank of the system = 8. Degrees of freedom = 1.**

The elimination ideal is explicitly empty in that variable:

```
I ∩ QQ(pi)[a_BSD] = {0}
```

Nothing in the web says anything whatsoever about `α_BSD`.

### 2.3 Which invariants are independent?

Ideal-membership test (reduce each `I_k` against a Gröbner basis of the other
ten):

| redundant | independent |
|---|---|
| **I2, I5, I6, I8** | I1, I3, I4, I7, I9, I10, I11 |

Exhaustive search over all 8-element subsets: **exactly three** of the 165
subsets generate the same ideal:

```
{1,3,4,5,7, 9,10,11}   (drops I2, I6, I8)
{1,3,4,6,7, 9,10,11}   (drops I2, I5, I8)
{1,3,4,7,8, 9,10,11}   (drops I2, I5, I6)
```

Reading: **I2 is unconditionally redundant**, and of `{I5, I6, I8}` exactly one
must be kept — any one of the three implies the other two given the rest. No
7-element subset can suffice (codim 8 forces ≥ 8 generators by the Krull height
theorem), so:

> **The eleven invariants contain exactly 8 independent constraints and 3
> redundancies. The system is a codimension-8 complete intersection.**

The corpus presents "eleven simultaneous invariants" as evidence of
over-determination. It is not over-determined; it is *under*-determined by one
dimension, with three of the eleven statements being restatements.

---

## 3. FREE VS DETERMINED — ALL NINE α's

Given the eleven invariants plus the positivity hypotheses the corpus itself
uses (`0 < α_P`, `0 < α_Hodge`, `0 < α_QG`, `0 < α_BSD`):

| α | status | forced by | honest label |
|---|---|---|---|
| `α_YM` | **UNIQUE** = 2 | I3 + I11 and π ≠ 0 | forced *by the system*, but the "2" is the system's single rational input (§4) |
| `α_Poincaré` | **UNIQUE** = 1 | I7 + `α_YM = 2` | forced, downstream of the same input |
| `α_RH` | **UNIQUE** = 3/2 | I9 + `α_YM = 2` | forced, downstream |
| `α_P` | **UNIQUE** = √2 | I1 + `α_P > 0` | forced, downstream (`√α_YM`) |
| `α_QG` | **UNIQUE** = √(2π) | I3 + `α_QG > 0` | forced, downstream (`√(α_YM·π)`) |
| `α_Hodge` | **UNIQUE** = φ | I4 + `α_Hodge > 0` | **GENUINE PIN — the only one** |
| `α_NP` | **UNIQUE** = φ + 1/4 | I10 + `α_Hodge = φ` | forced *only once the offset is given*; the offset is free (§5) |
| `α_NS` | **FREE** (= 2·α_BSD) | I5 relative to `α_BSD` | ratio pinned, scale free |
| `α_BSD` | **FREE** | nothing | **completely unconstrained** |

The general positive solution, verified to satisfy all eleven identically:

```
α_Poincaré = 1        α_P    = √2        α_RH  = 3/2
α_YM       = 2        α_Hodge = φ        α_NP  = φ + 1/4
α_QG       = √(2π)    α_NS   = 2t        α_BSD = t          for any t > 0
```

`t = 3π/4` gives the framework. `t = 1` is equally admissible. So is `t = e`,
`t = 10^100`, or `t = π/1000`.

### 3.1 The dependency chain

```
                          [I4]  self-closing, no imported constant
                            │
                            ▼
                        α_Hodge = φ         ← THE ONLY GENUINE DERIVATION
                            │
                            │ + offset c := 1/4   ← FREE INPUT (§5)
                            ▼
                        α_NP = φ + 1/4

  [I3 vs I11], π ≠ 0  ──►  α_YM = 2   ← the single rational input, five spellings (§4)
                            ├── I7 ──►  α_Poincaré = 1
                            ├── I9 ──►  α_RH = 3/2
                            ├── I1 ──►  α_P = √2
                            └── I3 ──►  α_QG = √(2π)

  [I5 / I6 / I8]      ──►  α_NS = 2·α_BSD      (ratio only)
                            │
                            │ + scale α_BSD := 3π/4   ← FREE INPUT, EXTERNAL TO THE WEB
                            ▼
                        α_NS = 3π/2,  α_BSD = 3π/4
```

### 3.2 Where the corpus's own "9 of 9" theorem gets `α_BSD`

`PF/CrossMillenniumDerivedConsequences.lean:278–285`, the theorem labelled
**"★★★ FULL RIGIDITY THEOREM — 9 of 9 α-values forced ★★★"**, is correctly
proved — but its hypothesis structure `ExtendedAbstractAlphaSystem` carries a
field the eleven invariants do not contain:

```lean
-- CrossMillenniumDerivedConsequences.lean, ExtendedAbstractAlphaSystem
inv_QG_sq_eq_eight_thirds_BSD : αQG ^ 2 = (8/3) * αBSD
```

That is a **twelfth** invariant. It is not in conjunct `C8`; it appears only in
`CrossMillenniumSharedInvariants.lean:196` (`α_QG_sq_eq_eight_thirds_α_BSD`),
proved by `unfold α_BSD; linarith` from `α_BSD := 3π/4`. It is the *only* thing
in the corpus that pins `α_BSD`, and it is exactly the definitional circle
described in §2.1 of the 2026-07-25 audit.

So the "9 of 9" claim is not false as a Lean theorem — but the ninth value is
obtained from a hypothesis that is a restatement of the value, and that
hypothesis is not one of the eleven the paper cites. **Under the eleven
invariants as actually stated, the theorem is 7 of 9, plus one ratio.**

---

## 4. HOW MANY INDEPENDENT ASSUMPTIONS? — THE CONSTANT-GENERICISATION

This is the sharpest form of the question. Replace every bare constant by a
symbol and ask which of them the system determines:

```
I1 : α_P²   = α_YM              (constant-free)
I2 : α_RH²  = a                 a = 9/4
I3 : α_QG²  = b                 b = 2π
I4 : α_Hodge² = α_Hodge + 1     (constant-free, self-closing)
I5 : α_NS   = d·α_BSD           d = 2
I6 : α_NS   = α_YM·α_BSD        (constant-free)
I7 : α_YM   = α_Poincaré + e    e = 1
I8 : α_RH·α_NS = α_NS + α_BSD   (constant-free)
I9 : α_RH·α_YM = f              f = 3
I10: α_NP − α_Hodge = c         c = 1/4
I11: α_QG²  = α_YM·π            (constant-free apart from π)
```

The **constant-free structural core is {I1, I4, I6, I8, I11}**. On that core,
with `α_BSD ≠ 0`:

| from | consequence |
|---|---|
| I5 & I6 | `α_YM = d` |
| I5 & I8 | `α_RH = (d + 1)/d` |
| then I2 | `a = α_RH² = (d+1)²/d²` → at `d = 2`, **`a = 9/4`** |
| then I9 | `f = α_RH·α_YM = d + 1` → at `d = 2`, **`f = 3`** |
| I3 & I11 | `b = α_YM·π = d·π` → at `d = 2`, **`b = 2π`** |
| then I1 | `α_P = √d` → at `d = 2`, **`α_P = √2`** |
| then I7 | `α_Poincaré = d − e` → at `d = 2, e = 1`, **`α_Poincaré = 1`** |

Verified by Gröbner reduction (script §9): given the structural core and
`α_BSD ≠ 0`, each of **I3, I5, I9 individually implies `α_YM = 2`**; I2 implies
`(α_YM − 2)(5α_YM + 2) = 0`, and positivity of `α_RH` removes the spurious
branch `α_YM = −2/5`. So:

> **The constants `9/4`, `3`, `2π`, and (with the unit increment) `1` are not
> four independent facts. They are four spellings of the single choice
> `α_YM = 2`, translated through the constant-free core.**

What remains genuinely independent:

| assumption | where it enters | can the web derive it? |
|---|---|---|
| **A1. `α_YM = 2`** (equivalently `d = 2`, equivalently the Perelman anchor `α_Poincaré = 1` plus the unit increment in I7) | I2, I3, I5, I7, I9 — five spellings | **no** — every spelling inserts it |
| **A2. `c = 1/4`** | I10 only | **no** — proved free in §5 |
| **A3. `α_BSD = 3π/4`** | nowhere in the eleven | **no** — outside the system |
| A4. `α_Hodge = φ` | I4 | **YES — genuinely derived** |

> ### **The framework makes THREE independent assumptions, not nine.**
>
> And it makes exactly **one** genuine derivation: `α_Hodge = φ`.

This is a dramatically stronger and more honest statement than the current
"eleven invariants force nine values". It is also *more interesting*: the
non-trivial content of the α-table is that five different-looking rational
anchors (`9/4`, `2π`, the factor `2`, `3`, the Perelman `1`) are mutually
consistent, i.e. all encode the same `α_YM = 2` through the structural core.
That coherence is real, it is worth stating, and it is *not* what the corpus
currently claims.

---

## 5. IS THE `1/4` FREE? — YES, PROVED

### 5.1 The occurrence count

`α_NP` occurs in **exactly one** of the eleven invariants (I10). A variable
appearing in one equation of a system cannot be over-determined by that system:
that equation defines it. This alone settles the question, but it can be made
formal in two independent ways.

### 5.2 Elimination

Replace `1/4` by an indeterminate `c`, adjoin `c` to the variable list, and
compute a lexicographic Gröbner basis:

```
Groebner basis elements involving c but no alpha
(i.e. constraints on c alone):  NONE
```

The elimination ideal `⟨I1,…,I9, I10(c), I11⟩ ∩ ℚ(π)[c]` is `{0}`.

### 5.3 Constructive witness

For a **symbolic** `c`, set `α_NP := φ + c` and leave the other eight α's at
the framework's own values. All eleven residuals are identically zero in `c`:

```
I1 = 0   I2 = 0   I3 = 0   I4 = 0   I5 = 0   I6 = 0
I7 = 0   I8 = 0   I9 = 0   I10 = 0  I11 = 0
```

### 5.4 The Lean statement

`PF/AlphaWebDegreesOfFreedom_r124.lean`:

```lean
theorem alpha_offset_is_free :
    ∀ c : ℝ, ∃ W : AlphaWebSansI10, W.αNP - W.αHodge = c

theorem alpha_offset_not_forced :
    ¬ ∃ q : ℝ, ∀ W : AlphaWebSansI10, W.αNP - W.αHodge = q
```

where `AlphaWebSansI10` carries the nine α's, the corpus's positivity
hypotheses, and the ten invariants of `C8` that do not mention `α_NP`.

> **CITABLE IMPOSSIBILITY RESULT.** The ten `α_NP`-free invariants of conjunct
> `C8` are consistent with `α_NP − α_Hodge = c` for **every** real `c`.
> Therefore no derivation of `1/4` from the α-web exists — not "has not been
> found", but *cannot exist*, because the web is satisfiable with any other
> value.
>
> This upgrades the 2026-07-25 audit's finding (`1/4` "is asserted; no
> derivation exists in the corpus") from a negative search result to a
> **theorem**.

The same argument applies verbatim to `α_BSD`: `alpha_BSD_not_pinned` in the
same file proves `¬ ∃ v, ∀ W : AlphaWeb, W.αBSD = v`.

---

## 6. RIGIDITY / PERTURBATION ANALYSIS

Jacobian of the eleven invariants with respect to the nine unknowns, evaluated
at the framework point (script §7; `p` denotes π):

```
⎡ 0   2√2    0     -1    0   0   0    0      0    ⎤   I1
⎢ 0    0     3      0    0   0   0    0      0    ⎥   I2
⎢ 0    0     0      0    0   0   0    0   2√2·√p  ⎥   I3
⎢ 0    0     0      0   √5   0   0    0      0    ⎥   I4
⎢ 0    0     0      0    0   0   1   -2      0    ⎥   I5
⎢ 0    0     0   -3p/4   0   0   1   -2      0    ⎥   I6
⎢-1    0     0      1    0   0   0    0      0    ⎥   I7
⎢ 0    0   3p/2     0    0   0  1/2  -1      0    ⎥   I8
⎢ 0    0     2     3/2   0   0   0    0      0    ⎥   I9
⎢ 0    0     0      0   -1   1   0    0      0    ⎥   I10
⎣ 0    0     0     -p    0   0   0    0   2√2·√p  ⎦   I11
```

```
rank J = 8
nullspace dimension = 1
tangent direction (α_Poincaré, α_P, α_RH, α_YM, α_Hodge, α_NP, α_NS, α_BSD, α_QG)
    = (0, 0, 0, 0, 0, 0, 2, 1, 0)
```

* The Jacobian rank **8** matches the ideal-theoretic codimension exactly — the
  framework point is a **smooth** point of a 1-dimensional variety.
* There is a nonzero tangent direction, so **the solution is not isolated**.
  The point can be moved along `(α_NS, α_BSD) ↦ (α_NS + 2s, α_BSD + s)`.
* By §3, the motion is not merely first-order: the *exact* solution set
  contains the full ray.

**Consequences for the corpus's language.**

* "Genuine rigidity would mean the solution is isolated." It is not.
  **The word "rigid" should be withdrawn**, or restricted to the seven pinned
  values with an explicit exclusion of the `(α_NS, α_BSD)` sector.
* Perturbing `α_P`, `α_RH`, `α_YM`, `α_Poincaré`, `α_Hodge`, `α_NP` or `α_QG`
  *does* break invariants — that part of the "perturbation breaks the web"
  rhetoric is correct.
  Perturbing `α_BSD` (with `α_NS` following) breaks **nothing**.
* The paper's "coefficient-rigidity certificate" perturbation argument
  (`millennium_problems_2026-07-13.tex:352`) is, on the I2/I4 leg, testing a
  statement against itself — already established in §2.1 of the 2026-07-25
  audit, and reconfirmed here structurally: I2 is one of the three
  *unconditionally redundant* invariants.

---

## 7. THE π-SECTOR — π IS A SCALE, NOT STRUCTURE

Apply the substitution

```
π ↦ λ·π,   α_QG ↦ √λ·α_QG,   α_NS ↦ μ·α_NS,   α_BSD ↦ μ·α_BSD     (λ, μ > 0)
```

Every one of the eleven maps to a **unit multiple of itself** (script §10):

| invariant | scaling factor |
|---|---|
| I1, I2, I4, I7, I9, I10 | 1 |
| I3, I11 | λ |
| I5, I6, I8 | μ |

So the eleven are **homogeneous under two independent rescalings**: one of the
`(π, α_QG)` sector and one of the `(α_NS, α_BSD)` sector.

**Answers to the posed question:**

1. **`α_NS = 3π/2` and `α_BSD = 3π/4` are statements about the ratio `2`, and
   nothing else.** The eleven invariants involve `α_NS` and `α_BSD` only through
   I5, I6, I8 — all homogeneous of degree 1 in the pair. Whether their common
   scale contains `π`, `e`, or nothing at all is invisible to the web. The `3π/4`
   is 100% definitional import.
2. **`α_QG = √(2π)`: π is doing genuine work, but only as a unit.** The web's
   actual statement is I11, `α_QG² = α_YM·π` — i.e. `α_QG` is the geometric mean
   of `α_YM` and π. That is a real relational statement. But I3 (`α_QG² = 2π`)
   adds nothing beyond `α_YM = 2` on top of I11, and under `π ↦ λπ` the pair
   survives intact. π is the unit of the QG sector.
3. **π does not communicate between sectors.** There is no invariant relating
   the π in `α_QG` to the π in `α_NS`/`α_BSD`. The apparent "π appears in three
   α's" pattern is not a fact about the web; it is a fact about three
   independent definitional choices.

This has a positive reading worth keeping: **the QG sector's π-content is
relational** (`α_QG² = α_YM·π`), which is a genuine structural statement. The
NS/BSD sector's π-content is not.

---

## 8. THE LEAN FORMALISATION

`PF_Lean4_Code/PF/AlphaWebDegreesOfFreedom_r124.lean` — **builds clean**,
no `sorry`, no project axiom; `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` for every result. Imported into
`PF.lean` and the full `PF` library target builds green.

| theorem | content |
|---|---|
| `webOf (t) (ht : 0 < t) : AlphaWeb` | explicit solution of all eleven invariants with `α_BSD = t` |
| `alpha_web_admits_every_positive_BSD` | `∀ t > 0, ∃ W : AlphaWeb, W.αBSD = t` |
| `alpha_web_underdetermined` | `∃ W₁ W₂, W₁.αBSD ≠ W₂.αBSD ∧ W₁.αNS ≠ W₂.αNS` |
| `alpha_BSD_not_pinned` | `¬ ∃ v, ∀ W : AlphaWeb, W.αBSD = v` |
| `alpha_web_pins` | the seven genuine pins + `α_NS = 2·α_BSD` |
| **`alpha_offset_is_free`** | `∀ c : ℝ, ∃ W : AlphaWebSansI10, W.αNP − W.αHodge = c` |
| **`alpha_offset_not_forced`** | `¬ ∃ q, ∀ W : AlphaWebSansI10, W.αNP − W.αHodge = q` |
| `invariant_two_is_redundant` | I2 from I3, I9, I11 (no positivity needed) |
| `invariant_six_is_redundant` | I6 from I3, I5, I11 |
| `invariant_eight_is_redundant` | I8 from I3, I5, I9, I11 |
| `rescaleNSBSD` / `rescaleNSBSD_scales` | the μ-rescaling of the NS/BSD sector maps solutions to solutions |
| `alpha_web_degrees_of_freedom_capstone` | all of the above bundled |

The structure is split as `AlphaWebSansI10` (nine α's, positivity, the ten
`α_NP`-free invariants) extended by `AlphaWeb` (adds I10). That split is
precisely what makes the freedom of the offset expressible as a theorem rather
than as an observation.

Positivity hypotheses used are exactly those the corpus's own
`ExtendedAbstractAlphaSystem` uses (`0 < α_P`, `0 < α_Hodge`, `0 < α_QG`), plus
`0 < α_BSD`. Adding `0 < α_BSD` only *strengthens* the negative results: even
restricted to positive `α_BSD` the value is unconstrained.

---

## 9. NUMERICAL CHECKS (verification only — no claim rests on these)

At 60 decimal digits (mpmath), reported to 45:

```
φ            = 1.61803398874989484820458683436563811772030918
φ + 1/4      = 1.86803398874989484820458683436563811772030918
√2           = 1.41421356237309504880168872420969807856967188
√(2π)        = 2.50662827463100050241576528481104525300698674
3π/2         = 4.7123889803846898576939650749192543262957541
3π/4         = 2.35619449019234492884698253745962716314787705

φ² − φ − 1           = 0        (exact, to 60 dps)
3π/2 − 2·(3π/4)      = 0        (exact, to 60 dps)
|φ + 1/4 − 1.868|    = 3.398874989e-5
```

The last line is included only to restate, at verified precision, the point
already made in §4.4 of the 2026-07-25 audit: the IBM CSV row is a 3-decimal
quantity, and the gap to `φ + 1/4` is `3.4 × 10⁻⁵`, not `10⁻¹⁰`.

**No new numerical coincidence is asserted anywhere in this document.**

---

## 10. WHAT SHOULD CHANGE IN THE CORPUS

Ordered by how much rhetorical weight the wrong version is carrying.

1. **Stop calling the α-web "rigid."**
   `CrossMillenniumSharedInvariants.lean:244–258`
   (`cross_millennium_shared_invariants_rigidity_remark`) asserts in its
   docstring: *"the 9 α-values are **not free parameters**: any redefinition
   that breaks one clause forces a cascade of inconsistencies."* This is false
   for `α_BSD` and `α_NS`, which can be freely rescaled together with no
   inconsistency at all. Note also that the "theorem" attached to that
   docstring is `True := trivial` — the docstring carries the whole claim.
   **Replacement text:** *"The eleven invariants form a rank-8 system in nine
   unknowns. Seven of the nine α-values are uniquely forced, given positivity.
   The pair (α_NS, α_BSD) is forced only up to a common positive scale, which
   the invariants do not determine; the values 3π/2 and 3π/4 are inputs."*

2. **Restate the "9 of 9 rigidity" theorem's scope.**
   `CrossMillenniumDerivedConsequences.lean:278–285`. The theorem is correct
   but its hypothesis set contains a twelfth invariant
   (`α_QG² = (8/3)·α_BSD`) that is not among the eleven cited in the paper and
   is proved by unfolding `α_BSD := 3π/4`. Either (a) add that invariant to the
   published list of invariants and mark it as the `α_BSD` anchor, or (b)
   downgrade the theorem's title to "7 of 9, plus the NS/BSD ratio". **(a) is
   the honest option if the anchor is wanted; it makes the input visible.**

3. **Report the redundancy.** Three of the eleven (I2, and two of
   {I5, I6, I8}) are strictly implied by the rest. Presenting eleven where
   eight suffice inflates the apparent over-determination. The reduction to
   eight is easy to state and does not weaken anything real.

4. **Replace "the substrate forces α_NP = φ + 1/4 via (I4) + (I10)"** —
   `millennium_problems_2026-07-13.tex:160, 361, 926` — with the now-proved
   statement:
   > *"I4 forces α_Hodge = φ (the one genuine pin in the web). I10 then
   > determines α_NP once the offset is supplied. The offset is a free
   > parameter of the system: the other ten invariants are consistent with
   > α_NP − α_Hodge = c for every real c
   > (`AlphaWebDegreesOfFreedom_r124.alpha_offset_is_free`). The value 1/4 is an
   > input."*

5. **Withdraw the I2 leg of the coefficient-rigidity certificate**
   (`:352`) — already recommended by the 2026-07-25 audit on
   circularity grounds, and now independently confirmed: I2 is one of the three
   invariants that are *ideal-redundant*, so perturbing it cannot test anything
   the rest does not already fix.

6. **Promote the honest version, which is better content than the claim it
   replaces.** *"Five different rational anchors used across five Millennium
   sectors — 9/4, 2π, the factor 2, 3, and the Perelman 1 — are, given the
   constant-free structural core, five spellings of the single statement
   α_YM = 2, and they are mutually consistent."* That is a real, checkable,
   non-trivial coherence fact about the α-table. It should replace the
   unsupportable "nine forced values".

---

## 11. REPRODUCING THIS

```bash
# exact symbolic algebra
/home/xluxx/lab/bin/python3 /home/xluxx/Principia-Fractalis/codex/alpha_web_system.py
# sympy 1.14.0, mpmath 1.3.0

# Lean
cd /home/xluxx/Principia-Fractalis/PF_Lean4_Code
lake build PF.AlphaWebDegreesOfFreedom_r124
```

The sympy script prints, in order: consistency check; Gröbner basis and
dimension; per-invariant redundancy; the complete list of minimal generating
subsets; the elimination ideal in `α_BSD`; the one-parameter positive solution
family; the Jacobian and its nullspace; the `c`-genericisation; the full
constant-genericisation; the π-homogeneity table; two explicit distinct
solutions; and 60-digit numerical checks.

---

## 12. SUMMARY TABLE

| question | answer |
|---|---|
| rank of the eleven invariants | **8** |
| dimension of the solution variety over ℚ(π) | **1** |
| unique maximal independent variable set | **{α_BSD}** |
| redundant invariants | **3** — I2 always, plus two of {I5, I6, I8} |
| minimal generating subsets of size 8 | exactly 3 |
| α's uniquely forced | **7** (Poincaré, P, RH, YM, Hodge, NP, QG) |
| α's forced only up to a scale | **2** (NS, BSD — ratio 2 pinned, scale free) |
| genuinely derived, non-circular pins | **1** — `α_Hodge = φ` from I4 + positivity |
| is `α_BSD = 3π/4` in the web? | **no** — the elimination ideal in α_BSD is {0} |
| is the `1/4` a free parameter? | **YES — proved**, symbolically and in Lean |
| is the system over-determined? | **no** — under-determined by one dimension |
| is the framework point isolated? | **no** — Jacobian nullspace is 1-dimensional |
| is π structural? | **no** — pure scale; two independent homogeneity symmetries |
| independent numeric assumptions the framework makes | **3** (`α_YM = 2`; `c = 1/4`; `α_BSD = 3π/4`) |
| is the corpus's Lean unsound? | **no** — every theorem cited is true; the issue is scope of the prose |

---

*Analysis performed 2026-07-26. All file paths absolute or relative to
`/home/xluxx/Principia-Fractalis`; Lean paths relative to `PF_Lean4_Code/`.
No git commit made.*
