# BSD scoping: Heegner/Kolyvagin is BLOCKED — but the lane has 16 genuine rank theorems, not one, and the real missing half is the UPPER bound.

**Date:** 2026-10-17 (Legion, audit on Acer). Scoping. No Lean.
Labels FACT / MEASURED / JUDGEMENT / OPEN.

**Two corrections to the brief's premise, both material:**

1. **`curveA_rank_ge_one` is the ALGEBRAIC (Mordell–Weil) rank, not the analytic
   rank.** The theorem is `1 ≤ Module.rank ℤ curveA.toAffine.Point`, proved from
   a non-torsion point certificate. Analytic rank is `ord_{s=1} L(E,s)`, and
   mathlib has **no `L(E,s)`** at the pin. The distinction is the whole BSD
   conjecture, so it matters here more than anywhere.
2. **"What stands: `curveA_rank_ge_one`" understates the lane by a factor of 16.**
   There are **16 genuine `Module.rank` theorems** already proved in-tree,
   including rank ≥ 2 and **rank ≥ 3**, plus a universal pipeline.

**VERDICT: Heegner/Kolyvagin is a BLOCKER. The lane is not blocked.** The next
real theorem is a rank **upper** bound, which is L-function-free; and there are
two cheap deliverables available first.

---

## 1. The Heegner files are Prop-level mirrors — and they prove their own vacuity. MEASURED

`BSD_HeegnerRank1Proof.lean` (586 lines, 17 theorems, no `sorry`). The two
load-bearing hypotheses of Gross–Zagier–Kolyvagin:

```lean
def HeegnerHypothesisSatisfied (_E : WeierstrassCurve ℚ) : Prop := True
def LDerivativeAtOneNonZero    (_E : WeierstrassCurve ℚ) : Prop := True
```

Both `True`, both **ignoring the curve argument** (`_E`). The second's docstring
even quotes the number it is not proving: *"`L'(E_{37.a1}, 1) ≈ 0.30599977... ≠ 0`"*.

The headline:

```lean
theorem bsd_rank_one_E37a1_via_heegner_and_GZ_K
    (hGZ : GrossZagier1986HeegnerPointNonTorsion)
    (hK  : Kolyvagin1990HeegnerToRankOne)
    (hLp : LDerivativeAtOneNonZero E_rank_one)
    (hHH : HeegnerHypothesisSatisfied E_rank_one) :
    ∃ cert : RankCertificateTyped E_rank_one, cert.r = 1
```

The conclusion is **a record with an `r` field equal to 1** — not
`Module.rank ℤ E.Point = 1`.

**And the file states its own vacuity as theorems**, which is why no kill is
needed here:

* `heegner_pair_both_iff_True` (579) — both hypotheses are equivalent to `True`
* `heegnerHypothesisSatisfied_iff_LDerivativeAtOneNonZero` (574)
* `kolyvagin1990HeegnerToRankOne_holds_at_True_placeholder` (381)
* `bsd_rank_one_E37a1_discharged_at_placeholder` (462)
* `bsd_rank_one_E37a1_honest_scope` (492)

**JUDGEMENT: the naming discipline here is as good as it gets** — a reader
cannot be misled by a theorem called `..._at_True_placeholder`. The defect is
that these files exist alongside genuine theorems for the same curves (§5) and
make the lane look weaker than it is.

**Genuine content does survive in them**, and it is the useful part:
`heegnerPoint_E37a1_on_curve` (182), `duplicateHeegnerPoint_E37a1_on_curve`
(214), `duplicateHeegnerPoint_y_ne_zero` (223) — explicit point arithmetic, the
same shape that carries the real rank theorems.

`BSD_Kolyvagin1990Formalization.lean` (683 lines, 10 theorems): **no real
`sorry`** — the single grep hit is line 159, the header *asserting* "Zero
`axiom`, zero `sorry`, zero `admit`". `BSD_GrossZagier1986Formalization.lean`
(674 lines) carries 1 `:= True`. Same pattern: structural Props standing in for
the two published theorems.

## 2. What mathlib has for this path: nothing. MEASURED

Searched the pinned tree (sanity check first: `EllipticCurve` = 18 files, so the
search works):

| concept | files |
|---|---|
| **Heegner points** | **0** (the 1 hit is a *comment* in `Analysis/Real/Pi/Chudnovsky.lean` about Heegner **numbers** — class-number-1 fields, for the π formula) |
| **Kolyvagin** | **0** |
| **Gross–Zagier** | **0** |
| **`L(E,s)`** | **0** |
| **Selmer group of `E`** | **0** (the 2 hits are Selmer *polynomials* `Xⁿ−X−1` and Dedekind-domain Selmer groups) |
| **Tate–Shafarevich / Ш** | **0** (word-boundary `\bSha\b`) |
| **Mordell–Weil (as a theorem)** | **0** |

**Present:** `EllipticCurve`/`WeierstrassCurve` and the affine point group law —
which is exactly what the existing rank theorems use.

> **The Heegner/Kolyvagin path is blocked at the first step, and more deeply
> than Yang-Mills was.** Gross–Zagier relates `L'(E,1)` to the height of a
> Heegner point; without `L(E,s)` it cannot be *stated*, let alone proved. The
> `:= True` placeholders in §1 are not laziness — they are the only way to write
> those hypotheses at this pin.

## 3. The lane's actual inventory — 16 genuine rank theorems. MEASURED

`grep "Module.rank"` across `PF/` gives, all of the form
`n ≤ Module.rank ℤ E.toAffine.Point`:

| curve | theorems |
|---|---|
| curveA (`y² = x³−2`) | `curveA_rank_ge_one` |
| 37a1, 43a1, 53a1, 61a1, 79a1, 83a1, 89a1, 101a1, 106a1 | `rank_ge_one` ×9 |
| **389a1** | `rank_ge_one`, **`rank_ge_two`**, `rank_ge_two_universal` |
| **5077a1** | `rank_ge_one`, **`rank_ge_three`**, `rank_ge_three_universal` |

And the supporting layers are **already universal, not per-curve**:

* **`DuplicationBezoutUniversal_r174.lean`** — `Φ = X⁴ − X²Y²b₄ − 2XY³b₆ − Y⁴b₈`,
  `Ψ = 4X³Y + X²Y²b₂ + 2XY³b₄ + Y⁴b₆`, with universal witnesses `F1,G1,F2,G2`
  and `bezout_X` taking the Weierstrass relation `4b₈ = b₂b₆ − b₄²` as a
  hypothesis. **Parametric in the curve.**
* **`DuplicationHeightUniversal_r176.lean`**, `DuplicationLogWindow_r177/r179`.
* **`RankPipelineUniversal_r202.lean`** — `rank_ge_universal {n}`,
  `gram_det_fin_two`, `rank_ge_two_universal`, `gram_det_fin_three`, instantiated
  at 389a1 and 5077a1 with their `b₂,b₄,b₆,b₈` computed.
* `MordellWeilRankLowerBound_r129`, `GramRankGeneral_r170`,
  `RegulatorIndependence389a1_r152`.

The generator behind it, `codex/duplication_bezout_gen.py` (2026-07-31), states
the design intent exactly: the universal identities force
`gcd(Φ(a,b), Ψ(a,b)) | R` *"**uniformly in the curve, replacing the whole
per-curve content layer**"*.

**JUDGEMENT: this is the healthiest machinery in the whole Millennium inventory**
— genuine theorems, a universal parametric layer, and a script that generates the
per-curve certificates. My own curve-A work was an instantiation of it and I did
not realise at the time that the universal layer already existed.

## 4. Two cheap deliverables, then the real gap

### 4a. Eight Heegner mirrors are redundant — the same curve already has a genuine theorem. MEASURED

| Heegner mirror files (12 curves) | genuine `Module.rank` theorem exists? |
|---|---|
| **43a1, 53a1, 61a1, 79a1, 83a1, 89a1, 101a1, 106a1** | **YES — 8 of 12 are redundant** |
| **91a1, 102a1, 131a1, 141a1** | **no — these 4 are the gap** |

So eight `BSD_HeegnerRank1ProofE*.lean` files assert `∃ cert, cert.r = 1` for
curves that have a *stronger, genuine* `1 ≤ Module.rank` theorem elsewhere in the
tree. **Repoint or retire them.** Cost: near zero. Benefit: the lane stops
looking Prop-level when it is not.

### 4b. Four curves are one mechanical instantiation away

**E91a1, E102a1, E131a1, E141a1** have Prop-mirrors but no genuine theorem, and
every dependency exists: universal Bézout (r174), universal height (r176), the
universal pipeline (r202), and the per-curve certificate generator
(`duplication_bezout_gen.py`). Per curve the work is: an explicit non-torsion
point, `R` and the height constant evaluated at that curve's invariants, then
instantiate. **That is the cheapest genuine next build on this axis.**

### 4c. The real gap: there is no rank UPPER bound for any curve

**Every one of the 16 theorems is a lower bound.** Nothing in the tree bounds any
rank from above. Consequences, stated plainly:

* **"rank exactly 1" is unreachable today** — for curve A, for E37a1, for all of
  them.
* **Therefore no BSD rank statement is reachable**, independently of the
  L-function gap. Even if `L(E,s)` landed in mathlib tomorrow, the algebraic side
  would still only have `≥`.
* Lower bounds are *certificates* (exhibit a point, show it has infinite order).
  Upper bounds are *finiteness* statements and need descent.

**The nearest provable upper bound: 2-descent.** It is L-function-free and
elementary, and it is what memory already names as the reachable complement
("rank lower bounds (done) + 2-descent upper bounds for the same curves").

**Dependency chain for a first upper bound — JUDGEMENT on the route, FACT on the
mathlib status:**

1. The descent map `E(ℚ)/2E(ℚ) → ℚ*/(ℚ*)²` (× two copies, for a curve with
   rational 2-torsion). **Not in mathlib** — `[Dd]escent`'s 18 files are
   categorical/AG descent, unrelated.
2. Local solubility at each bad prime and at ∞ — elementary, needs `ZMod`
   arithmetic and the usual case analysis.
3. Finiteness of the 2-Selmer group ⇒ `rank ≤ dim_{F₂} Sel₂ − dim_{F₂} E(ℚ)[2]`.
4. Combined with an existing lower bound ⇒ **rank exactly**.

**Curve choice matters and the existing family is the wrong one.** Descent via
2-isogeny is elementary only when there is a rational 2-torsion point; the
Heegner/rank-1 family (37a1 = `⟨0,0,1,−1,0⟩`, 43a1, 53a1, …) has trivial
torsion, and curve A (`y² = x³−2`) has none either — I proved `two_not_cube`,
which is exactly the statement that it has no rational 2-torsion. **So the first
upper bound should be attempted on a newly chosen curve with rational 2-torsion
and small conductor, not on any curve currently in the tree.** A rank-0 target
(proving `E(ℚ)` finite) is the cleanest first instance.

## 5. Verdict

**Heegner/Kolyvagin: BLOCKER NAMED.** Zero mathlib support for Heegner points,
Kolyvagin, Gross–Zagier, `L(E,s)`, `Sel(E)` or Ш; and the in-tree files are
self-labelled Prop mirrors whose two hypotheses are provably `True`. **Do not
build on them.** They cannot be repaired at this pin, because Gross–Zagier is
unstateable without `L(E,s)`.

**The lane itself: healthy and open.** Recommended sequence:

| # | step | cost | status |
|---|---|---|---|
| 1 | Retire/repoint the **8 redundant** Heegner mirrors at the genuine theorems | near zero | pure cleanup |
| 2 | Instantiate genuine `rank ≥ 1` for **E91a1, E102a1, E131a1, E141a1** | mechanical | all deps exist (r174/r176/r202 + generator) |
| 3 | **First rank UPPER bound via 2-descent**, on a newly chosen curve with rational 2-torsion | real project, elementary | the only route to "rank exactly" |
| 4 | Combine with an existing lower bound ⇒ **first exact rank in the repo** | follows from 3 | the genuine milestone |

**JUDGEMENT: step 3 is the honest BSD milestone.** Steps 1–2 are tidying and
mechanical extension; step 3 is the first piece of real new mathematics on this
axis, and it is reachable without any L-function.

**Reachability across all five axes now scoped:** **NS first** (carrier change +
one lemma), **YM second** (one mathlib instance, then reflection positivity),
**BSD third** (cleanup + 4 instantiations are free; 2-descent is the real step),
**P/NP fourth** (statement-repair only, question stays open), **Hodge last**
(subject absent). The statistical BSD lane stays closed (`940c15a7`) and the
parked P/NP spectral bridge stays parked.

**OPEN / not done here:** whether `rank_ge_universal` is fully curve-generic or
specialised at use (I read its declarations, not its proofs); the exact
`dim Sel₂` bookkeeping for a chosen descent curve; whether any of the 11
per-curve rank files already contain partial upper-bound material I did not see
(I searched for `Module.rank`, which only finds the stated bounds); and I read
the Heegner/Kolyvagin files by header plus definitions and ~8 spot-checked
theorems, not all ~2,400 lines across the 15 files.

---

## Label summary

* **FACT (quoted from source):** both `:= True` definitions with `_E` ignored and
  the `L'(E,1) ≈ 0.30599977` docstring; the headline's
  `∃ cert : RankCertificateTyped, cert.r = 1`; the five self-vacuity theorem
  names; the Kolyvagin line-159 header text; `DuplicationBezoutUniversal_r174`'s
  `Φ`, `Ψ`, `bezout_X` and the `4b₈ = b₂b₆ − b₄²` hypothesis;
  `RankPipelineUniversal_r202`'s declarations; the generator's "uniformly in the
  curve" sentence.
* **MEASURED (this session):** the 16 genuine `Module.rank` theorem names
  including `rank_ge_two` and `rank_ge_three`; the 12 mirror curves and the
  8-redundant/4-gap split; the seven mathlib zero-counts with the
  `EllipticCurve`=18 sanity check; the Heegner hit being a Chudnovsky comment;
  `\bSha\b` = 0.
* **JUDGEMENT (mine):** that algebraic-vs-analytic rank is the correction that
  matters most; that the Prop-mirrors' naming is exemplary but their existence
  alongside genuine theorems is the defect; that this is the healthiest Millennium
  machinery in the repo; that upper bounds are the real gap and 2-descent the
  route; that the existing family is the wrong curve set for descent and a
  2-torsion curve should be chosen instead; the reachability ordering.
* **NOT established:** full genericity of `rank_ge_universal`; the `Sel₂`
  bookkeeping; absence of partial upper-bound material outside `Module.rank`
  statements; line-by-line reading of all 15 Heegner/Kolyvagin files.
