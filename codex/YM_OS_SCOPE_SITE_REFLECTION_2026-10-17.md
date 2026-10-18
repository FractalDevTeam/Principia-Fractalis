# Yang–Mills full lattice OS: the straddling-plaquette analysis is NOT the next link — for site reflection there are no straddling plaquettes. Measured. The real blocker is that the landed θ is the wrong involution.

**Date:** 2026-10-17 (Legion; audit + build-verify on Acer). Scoping. No Lean
written. Labels **FACT** / **MEASURED** / **JUDGEMENT** / **OPEN**. Every
structural claim is quoted from source or produced by a script named here.

---

## VERDICT

**BUILDABLE, no mathlib blocker. Three corrections first, one of them
load-bearing, and the cost is ~1,000–1,700 lines, not a research programme.**

Three findings reorder the task Rio set:

1. **Rio's framing needs correcting.** `2d506d37` is **not** "reflection
   positivity at the Bochner-integral level." There is no reflection
   positivity in it at any level. What landed is the (genuine, kernel-clean)
   fact that an **L² Gram matrix is PSD**, specialised to the Wilson measure —
   true for *any* measure, *any* test family and *any* map θ, including the
   identity. **The file's own docstring says exactly this**; the relay lost it.
2. **The straddling-plaquette analysis is not required.** For **site**
   reflection the Wilson action splits with **no cross term at all** —
   **measured: 0 straddling plaquettes** at L = 4, 6, 8. The two halves
   communicate *only* through the shared time-zero links, which is precisely
   what makes the proof work. Straddling terms (and with them character
   expansions and the Schur product theorem) appear only for **link**
   reflection, which this target does not need.
3. **The real blocker is the θ that landed: it is the wrong involution, and it
   is wrong in two independent ways.** **Measured:** it does not leave the
   Wilson action invariant. Without `S ∘ θ = S` nothing downstream can work.
   The correct θ is identified and verified below.

---

## 1. What actually landed — audit of the chain. FACT

Four modules, all four built (oleans dated 2026-10-17) and imported into
`PF.lean:1405–1408`:

| module | lines | what it really contains |
|---|---|---|
| `SpecialUnitaryGroupTopology_2026_10_17` | — | `ContinuousMul`, `ContinuousInv`, `IsTopologicalGroup`, **`CompactSpace`** for `Matrix.specialUnitaryGroup (Fin 2) ℂ` |
| `HaarSU2_2026_10_17` | — | `SU2_haar` via mathlib `haarMeasure` on `⊤ : PositiveCompacts SU2`; `IsMulLeftInvariant`, `IsProbabilityMeasure`, `IsHaarMeasure` |
| `WilsonMeasure_2026_10_17` | 149 | `GaugeField`, `plaquetteHolonomy`, `wilsonActionTotal`, `wilsonBaseMeasure = Measure.pi SU2_haar`, `wilsonGibbsMeasure` via `withDensity` |
| `ReflectionPositivityGram_2026_10_17` | 294 | Bochner Gram PSD + the θ definitions |

**This is real work and the previously-named blocker is closed.** My
2026-10-17 04:42 scoping (`codex/YM_SCOPING_LATTICE_ENTRY_2026-10-17.md` §8)
named exactly one gap — *"compact topological group instance on
`specialUnitaryGroup` — ❌ NOT present — the one gap"*. **It is now present.**
The Wilson measure is the genuine object: Haar on SU(2), product over links,
Gibbs density. Credit where it is due.

**Kernel-cleanliness verified independently, not taken on trust** — I
re-elaborated the module rather than believe the header, using the very method
my CI patch proposes (`lake env lean`, which always elaborates and always
emits):

```
'PF.YangMills.gramMatrix_bochner_posSemidef'   depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.YangMills.wilson_gramMatrix_posSemidef'    depends on axioms: [propext, Classical.choice, Quot.sound]
'PF.YangMills.wilson_reflection_gram_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound]
      (9 declarations, all at or below the three-axiom bar; `timeReflectionSite` is [propext] alone)
```

**Side note, and it is the CI finding biting immediately:** all four modules are
imported into `PF.lean`, so under the current `verify.sh` their
`#print axioms` output is swallowed exactly as diagnosed in
`codex/CI_GATE_VACUOUS_2026-10-17.md` — `lake build PF.YangMills.*` is a no-op
on a built tree. **The gate will report PASS over these files without reading
them.** That is the unapplied patch's first real customer.

---

## 2. The correction to Rio's framing. FACT, quoted

The landed headline is `wilson_reflection_gram_posSemidef`:

```lean
    (Matrix.of (fun i j : Fin K =>
        ∫ U, star (F i (timeReflectionGaugeField U))
             * F j (timeReflectionGaugeField U)        -- ← BOTH sides reflected
         ∂(wilsonGibbsMeasure L β))).PosSemidef
```

Both arguments carry θ. That is the L² Gram matrix of the family `F ∘ θ`, so it
is PSD because `⟪Σcᵢgᵢ, Σcⱼgⱼ⟫ = ‖Σcᵢgᵢ‖² ≥ 0` — for **any** measurable map in
place of θ. **The theorem is true and carries zero reflection content.**

**The file says so itself**, and this is the sentence the relay dropped:

> *"Note: the full OS-reflection positivity theorem is `G_ij := ∫ star(F_i(θU))
> · F_j(U) dμ_β(U)` (NOT both reflected), and depends on the Wilson action's
> straddling-plaquette decomposition; the symmetric reflected version here is
> the first-pass measure-level theorem."*

So the honest ledger entry for `2d506d37` is **"Wilson measure constructed;
Bochner Gram PSD shell in place; reflection positivity not yet attempted."**
**JUDGEMENT:** the naming (`…ReflectionPositivityGram…`,
`wilson_reflection_gram_posSemidef`) is what made the relay go wrong — the
docstring is honest while the identifier is not. Same defect class as the
`P_neq_NP : spectral_gap ≠ 0` rename still owed. **No downgrade is implied: the
theorem keeps its content; what changes is the summary of what it buys.**

**Where it lands is better than it looks, though.** §4 shows the correct Gram,
after the decomposition, reduces to an L² Gram over the *time-zero* variables.
`gramMatrix_bochner_posSemidef` is **exactly the final step** of the real proof.
The shell is the last lemma, not a false start.

---

## 3. The load-bearing defect: θ is the wrong involution. MEASURED

`scratchpad/theta_check.py` mirrors the Lean definitions verbatim and compares
`S_W(θU)` with `S_W(U)` on random SU(2) configurations:

| θ | L=4 \|ΔS\| | L=5 \|ΔS\| | involution? | verdict |
|---|---|---|---|---|
| **V1 — as landed** | **2.405** | **15.50** | yes (defect 0) | **NOT INVARIANT** |
| V2 — geometric, with inverse | 2.5e−11 | 2.4e−11 | yes | **INVARIANT** |
| V3 — geometric, no inverse | 28.62 | 10.11 | yes | NOT INVARIANT |

**Two independent errors in `timeReflectionLink`:**

```lean
def timeReflectionLink (ℓ : LatticeLink L) : LatticeLink L :=
  (timeReflectionSite ℓ.1, ℓ.2)        -- base site reflected, direction kept
```

* **Wrong base site for temporal links.** A link `(x, 0)` spans times `x₀` and
  `x₀+1`. Its reflection spans `−x₀` and `−x₀−1`, i.e. it is the link based at
  **`θx − ê₀`**, not at `θx`. Spatial links are fine (θ fixes spatial coords).
* **Missing inverse.** The reflected temporal link is traversed backwards, so
  the transporter inverts: `(θU)(x,0) = U(θx − ê₀, 0)⁻¹`. V3 isolates this —
  correcting the base site but dropping the inverse is still wrong, by 28.62.
  **The inverse is load-bearing, not cosmetic.**

**The correct θ, measured invariant:**

```
(θU)(x, j) = U(θx, j)                    for j ≠ 0   (spatial: unchanged)
(θU)(x, 0) = (U(θx − ê₀, 0))⁻¹           (temporal: shifted base + inverse)
   where θx = Function.update x 0 (-(x 0))   -- unchanged, and correct
```

`timeReflectionSite` is right as it stands; only the link map is wrong. **The
fix is confined to one definition**, but it invalidates nothing already proved —
`wilson_reflection_gram_posSemidef` is true for any θ, so changing θ cannot
break it. **JUDGEMENT: this is why the defect survived. The one theorem that
mentions θ is insensitive to whether θ is correct.** A function defined but
never load-bearing is never tested; the same lesson as the CI gate, one layer up.

---

## 4. Rio Q1 — what the time-slice decomposition requires. MEASURED

**The headline: for site reflection there is no cross term.**
`scratchpad/straddle_check.py` classifies every link and every plaquette.

Link partition on the torus under `t ↦ −t`, L even, fixed slices `{0, L/2}`:
spatial links at `t ∈ {0, L/2}` → `Λ₀`; spatial at `1 ≤ t ≤ L/2−1` → `Λ₊`;
spatial at `L/2+1 ≤ t ≤ L−1` → `Λ₋`; temporal with base `t ≤ L/2−1` → `Λ₊`,
else `Λ₋`.

| L | \|Λ₊\| | \|Λ₀\| | \|Λ₋\| | θ-fixed links | θ(Λ₊)⊆Λ₋ | θ(Λ₀)⊆Λ₀ | **straddling plaquettes** |
|---|---|---|---|---|---|---|---|
| 4 | 320 | 384 | 320 | 384 (= Λ₀ exactly) | ✓ | ✓ | **0** of 3072 |
| 6 | 1944 | 1296 | 1944 | 1296 (= Λ₀) | ✓ | ✓ | **0** of 15552 |
| 8 | 6656 | 3072 | 6656 | 3072 (= Λ₀) | ✓ | ✓ | **0** of 49152 |

and the sector split is exact and θ-conjugate (`scratchpad/decomp_check.py`):

| identity | L=4 | L=6 |
|---|---|---|
| `S₊ + S₀ + S₋ = S_W` | 9.1e−13 | 1.8e−11 |
| `S₋(U) = S₊(θU)` | 2.1e−12 | 3.5e−11 |
| `S₀(U) = S₀(θU)` | **0** | **0** |
| `S₊` unmoved by perturbing any Λ₋ link | **0** (12 links) | **0** (12 links) |
| `S₋` unmoved by perturbing any Λ₊ link | **0** (12 links) | **0** (12 links) |

The last two are **exactly zero**, not small: the sector actions provably never
read the other half's links. So

> **`S_W(U) = S₊(U₊, U₀) + S₀(U₀) + S₋(U₋, U₀)` with `S₋ = S₊ ∘ θ`, no cross
> term.**

That is *weaker* than the `S_cross(U_-, U_0, U_+)` the landed docstring
anticipates, and that is the good news: **the hard machinery is not needed.**

**The proof then runs, in four moves:**

1. split `Measure.pi` over links into `Λ₊ × Λ₀ × Λ₋`;
2. `exp(−βS_W) = exp(−βS₊)·exp(−βS₀)·exp(−βS₋)` by `Real.exp_add`;
3. Fubini: with `Φⱼ(U₀) := ∫_{Λ₊} Fⱼ·e^{−βS₊} dU₊`, θ-invariance of the base
   measure (free: a product of Haar measures is invariant under any relabelling,
   and under the per-link inverse by **`IsHaarMeasure.isInvInvariant_of_regular`**)
   turns the negative factor into `conj Φᵢ`, giving
   `Gᵢⱼ = ∫_{Λ₀} conj(Φᵢ(U₀))·Φⱼ(U₀)·e^{−βS₀(U₀)} dU₀`;
4. that is an L² Gram matrix — **apply the already-landed
   `gramMatrix_bochner_posSemidef`**. Done.

### Two hypotheses the current carrier does not have

* **`L` must be EVEN. MEASURED.** For odd `L`, `t ↦ −t` leaves a *temporal*
  link fixed (base time `(L−1)/2`: L=5 → t=2, L=7 → t=3), mapped to itself
  reversed. A θ-fixed temporal link cannot be placed in `Λ₊` or `Λ₋`, so the
  three-way product split fails and a genuine straddling term appears — that
  is the **link-reflection** case, needing the character expansion. The current
  `WilsonMeasure` has only `[NeZero L]`. **Add `Even L` (or index time by
  `Fin (2*M)`).**
* **Periodic time means two fixed slices, not one** (`{0, L/2}`). `Λ₀` is the
  spatial links of **both**, and `S₀` the plaquettes inside them. Harmless, but
  it must be in the definition; a note written for `ℤ⁴` would say one slice and
  be wrong here.

### Two prerequisites the Acer's file names as missing — and it is right

Quoted from `WilsonMeasure_2026_10_17.lean:27–31`, *"What this file does NOT
prove"*:

> *"`IsFiniteMeasure (wilsonGibbsMeasure L β)` — true on compact (bounded
> density on finite-measure base), but would require packaging continuity of
> the plaquette holonomy map"*

**Both are hard prerequisites for step 3**: Fubini needs `SigmaFinite`, and
every `Integrable` obligation needs boundedness. `Continuous wilsonActionTotal`
and `Measurable`/`StronglyMeasurable` lemmas are **absent from the file
(verified: zero occurrences)**. They are not deep — `ContinuousMul` and
`ContinuousInv` on SU(2) are already built, and `CompactSpace` gives
boundedness — but they are real line-count, and they are on the critical path.

---

## 5. Rio Q2 — which mathlib lemmas carry the reflection structure. FACT

All verified present at the pin (`.lake/packages/mathlib/Mathlib`):

| need | mathlib | location |
|---|---|---|
| split a product measure by a predicate | `measurePreserving_piEquivPiSubtypeProd` | `MeasureTheory/Constructions/Pi.lean:699` |
| split along a sum type (cleaner for a 3-way split) | `measurePreserving_sumPiEquivProdPi_symm` | `Constructions/Pi.lean:758` |
| relabel the index set | `measurePreserving_piCongrLeft` | `Constructions/Pi.lean:716` |
| Fubini for Bochner integrals | `integral_prod`, `integral_integral_swap` | `Integral/Prod.lean:460, 498` |
| transport an integral along θ | `MeasurePreserving.integral_comp'` | `Integral/Bochner/Basic.lean:1119` |
| **θ-invariance of Haar under inverse** | **`IsHaarMeasure.isInvInvariant_of_regular`** (instance, prio 100) | `Measure/Haar/Unique.lean:962` |
| inverse-invariance of a product measure | `pi.isInvInvariant` (instance) | `Constructions/Pi.lean:586` |
| `μ.inv = μ`, `MeasurePreserving Inv.inv` | `inv_eq_self`, `measurePreserving_inv` | `Group/Measure.lean:303, 313` |
| final PSD step | **already in the repo** — `gramMatrix_bochner_posSemidef` | `2d506d37` |

**The dagger in the corrected θ is free.** It was the one thing I expected to
cost: `isInvInvariant_of_regular` is an *instance*, and `pi.isInvInvariant`
lifts it to the product, so `MeasurePreserving θ μ₀ μ₀` should discharge by
instance search plus a relabelling `Equiv`. **That is the single best piece of
news in this scoping.**

### What mathlib does NOT have — and why it does not matter here

* **No Schur product theorem.** `LinearAlgebra/Matrix/Hadamard.lean` has 16
  algebraic identities and **not one PSD statement**; nothing anywhere pairs
  `hadamard` with `PosSemidef`.
* **No `PosSemidef.add`, `.sum`, or `.smul`** — zero hits under any name. A
  genuine and surprising gap.

Either would be needed for **link** reflection (`exp` of a PSD kernel). **Site
reflection needs neither**, because straddling = 0 (§4). **JUDGEMENT: this is
the decisive argument for the site-reflection route**, and it is the one place
where this target is genuinely easier than the external GFF work (§6), which
had to build Schur–Hadamard lifting itself.

---

## 6. Rio Q3 — the literature, and the external Lean prior art

### The theorem to follow. FACT, citations verified

* **M. Lüscher**, *"Construction of a selfadjoint, strictly positive transfer
  matrix for Euclidean lattice gauge theories"*, **Commun. Math. Phys. 54
  (1977) 283–292**, DOI `10.1007/BF01614090`. **This is the theorem to follow**
  — physical positivity for Wilson's lattice gauge theory via the time-slice
  argument, in the temporal gauge, with site reflection. The structure in §4 is
  his.
* **K. Osterwalder & E. Seiler**, *"Gauge field theories on a lattice"*,
  **Ann. Phys. 110 (1978) 440–471**, DOI `10.1016/0003-4916(78)90039-8`. The
  canonical reference; also the source of **link** reflection, the harder
  variant we are avoiding.
* Textbook statement with the explicit plaquette bookkeeping: Montvay &
  Münster, *Quantum Fields on a Lattice*, ch. 3. **OPEN:** section number not
  verified against a copy.

### There is substantial Lean prior art, and it was not in my previous scoping. FACT

| project | what it is | relevance |
|---|---|---|
| **`mrdouglasny/OSforGFF`** | Gaussian Free Field on `S'(ℝᵈ)` via Minlos; **all five OS axioms incl. OS3 reflection positivity**; **"0 sorries, 0 axioms, ~25,500 lines across 52 on-graph files"**, v3.2 general `d ≥ 2`, Aug 2026 | **The serious one.** Scalar field, not gauge. Proves RP via **Schur–Hadamard lifting** — i.e. they built the Schur product theorem mathlib lacks |
| `xiyin137/OSreconstruction` | OS **reconstruction** (Euclidean → Wightman) + von Neumann algebra infrastructure | the step *after* positivity |
| `lluiseriksson/lean-os-positivity` | **definition layer only** — lattice RP interfaces, "0 sorry, 0 project axioms", but unproved content sits in **explicit certificate fields** `WilsonRPCertificate`, `TransferMatrixReflectionCertificate`, `GNSReconstruction`; README: *"not a proof of the Clay Yang-Mills problem"* | nearest in target, **does not prove Wilson RP** |
| Harvard *Formalization of QFT* (2026-05-06); arXiv `2603.15770` | programme incl. OS reconstruction, `P(φ)₂`, **"the Yang-Mills mass gap at strong coupling"** | the field this would be entering |

**Honest reading. JUDGEMENT.**
*Nobody appears to have formalised reflection positivity for the Wilson lattice
gauge measure.* The one repo aiming at it keeps it as a `WilsonRPCertificate` —
an unproved field, honestly labelled. **So the target is genuinely open and not
duplicative.** But `OSforGFF` shows what a serious effort on this axis looks
like (25,500 lines for the free field) and that the people doing it are ahead on
infrastructure. **This should change how the result is framed, never claimed as
first-in-the-world without checking these repos at the time of writing.**

---

## 7. Rio Q4 — estimate, difficulty, blockers

### Build order

| # | step | lines | difficulty | risk |
|---|---|---|---|---|
| 0 | **Fix `timeReflectionLink`** (base `θx − ê₀`, add inverse); keep the old def as `timeReflectionLinkNaive` or delete | 30 | trivial | none |
| 1 | `Continuous plaquetteHolonomy`, `Continuous wilsonActionTotal`, `Measurable` density, **`IsFiniteMeasure (wilsonGibbsMeasure L β)`** | 150–250 | low | `Finset.sum` of continuous functions; `CompactSpace` for boundedness |
| 2 | `Even L` (or `Fin (2*M)`) + `Λ₊/Λ₀/Λ₋` as a decidable classification, and the `Equiv` to `Λ₊ ⊕ Λ₀ ⊕ Λ₋` | 120–200 | low–med | `Fin` modular arithmetic |
| 3 | **`wilsonActionTotal (θ U) = wilsonActionTotal U`** | 250–450 | **medium** | the plaquette bijection + `Re tr` under inverse; `Fin` shifts |
| 4 | **no-straddling ⇒ `S = S₊ + S₀ + S₋`, each reading only its own links** | 300–500 | **HIGH — the core** | case analysis over `(x, μ, ν)` in `Fin L` with wraparound |
| 5 | Fubini reduction to the `Λ₀` integral | 200–300 | medium | every `Integrable` obligation; needs step 1 |
| 6 | apply `gramMatrix_bochner_posSemidef` ⇒ **`wilson_reflection_positivity`** | 40 | trivial | — |

**Total ≈ 1,000–1,700 lines, 2–4 files. JUDGEMENT, and the spread is honest:**
steps 0–2 and 6 I would price confidently; **steps 3–5 I have not elaborated in
Lean, and step 4 is where an estimate like this historically goes wrong** (the
BSD "mechanical, one instantiation each" turned out to be ~830 lines/curve).
Treat 1,700 as the realistic figure, not 1,000.

### Blockers, ranked

1. **No mathlib blocker.** Every lemma needed is present (§5). This is the
   first Millennium axis in this repo where that is true — unlike the
   Clay/Wightman form, where four barriers all sit at zero.
2. **Step 4 is the only genuine risk.** "No plaquette has links in both `Λ₊`
   and `Λ₋`" is *measured* true but must be *proved* for variable `L` with
   wraparound. `decide` cannot help (L is a variable). **Mitigation, if it
   blows up: re-index time as `Fin (2*M+1)` with reflection `t ↦ 2M − t` —
   non-modular subtraction, one fixed slice, plaquettes only where `x₀+1 ≤ 2M`.
   Arithmetic becomes order reasoning in `ℕ`. Costs a carrier rebuild
   (~200 lines) and loses time-periodicity.** JUDGEMENT: start on the torus,
   switch if step 4 exceeds ~500 lines.
3. **Integrability bookkeeping (step 5)** is the usual quiet time sink.
4. **Not a blocker but worth saying plainly:** this proves RP for a *finite*
   lattice. It is **not** the Clay content and not a mass gap. The faithful
   intermediate — the gap uniform in lattice spacing as `a → 0` — remains
   writable-as-a-statement with an open proof, exactly as on the NS axis.

### Priority caveat — HARD RULE 7, stated rather than buried

**This is secondary work by the governing priority order** (mathlib PRs >
substrate preprint > conclusion-gate > finite-rect RH > rest), and the spine
does not run through the Clay list. A finished `wilson_reflection_positivity`
would be the repo's first genuine Yang–Mills theorem and a real result — **it
would not move the spine**. Offered as a fact for the decision, not as an
argument against building it.

**Genuine mathlib-contribution candidates found in passing**, both independent
of this build: the **`CompactSpace`/`IsTopologicalGroup` instances for
`specialUnitaryGroup`** the Acer just built (nothing in mathlib has them), and
**`PosSemidef.add`/`.sum`/`.smul`**, which are absent under any name.

---

## 8. One next action

**Fix `timeReflectionLink` (step 0) and prove `wilsonActionTotal (θ U) =
wilsonActionTotal U` (step 3).** That is the smallest increment that converts a
measured fact into a theorem, it is the identity every later step consumes, and
until it exists the rest of the chain cannot be started. Steps 1–2 are
prerequisites that can ride along in the same file.

---

## Label summary

* **FACT (quoted/verified from source):** the four modules and their
  `PF.lean:1405–1408` imports; the 9-declaration axiom transcript, re-elaborated
  here; `wilson_reflection_gram_posSemidef`'s both-sides-reflected statement and
  its own docstring disclaimer; `WilsonMeasure:27–31`'s "does NOT prove" list;
  the mathlib locations in §5; the absence of a Schur product theorem and of any
  `PosSemidef` closure lemma; the Lüscher and Osterwalder–Seiler citations; the
  four external Lean projects and `lean-os-positivity`'s certificate fields.
* **MEASURED (scripts named, reproducible):** the landed θ does not preserve the
  Wilson action (|ΔS| = 2.405 at L=4, 15.50 at L=5); the corrected θ does
  (2.5e−11); dropping the inverse breaks it (28.62); **0 straddling plaquettes**
  at L = 4, 6, 8; `|Λ₊| = |Λ₋|`, θ-fixed links = `Λ₀` exactly; the three
  decomposition identities, two of them exactly zero; a θ-fixed *temporal* link
  exists for every odd L tested (5, 7).
* **JUDGEMENT (mine):** that the identifier/docstring mismatch is what misled the
  relay; that θ survived because the only theorem mentioning it is insensitive
  to it; that site reflection is the right route *because* straddling = 0 makes
  the Schur product theorem unnecessary; the line estimates, with step 4 as the
  risk; the `Fin (2*M+1)` fallback; that the target is open and not duplicative.
* **OPEN / NOT established:** the Montvay–Münster section number; whether the
  `Equiv` to `Λ₊ ⊕ Λ₀ ⊕ Λ₋` composes with `Measure.pi` as smoothly as §5
  assumes (not elaborated); the step 3–5 costs (not elaborated in Lean); whether
  `OSforGFF`'s Schur–Hadamard work is reusable at this pin (different mathlib
  commit, not checked); and the four external repos were read at README level
  only, not audited.

**Unchanged and still owed from the previous YM scoping, both Pablo-gated
(public text):** the glossary's *"Yang-Mills … Solved here: Δ_YM = 420.43 MeV"*,
refuted by ch23's own `ω_c` ledger; and ch23's `thm:area-law` label, which is
quark confinement and the same defect class as the two the 2026-10-05 inline
note already flags.
