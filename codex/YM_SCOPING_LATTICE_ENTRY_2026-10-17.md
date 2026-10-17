# Yang-Mills scoping: the Clay/Wightman form is BLOCKED at mathlib, but a real entry point exists one level down — lattice reflection positivity, one missing instance away.

**Date:** 2026-10-17 (Legion, audit on Acer). Scoping. No Lean. Labels
FACT / JUDGEMENT / OPEN. Every structural claim below is quoted from source.

**VERDICT, two parts:**

* **Clay/Wightman form: BLOCKER NAMED.** mathlib at the pin has **zero** of
  Wightman, Osterwalder, reflection positivity, NuclearSpace, Bochner–Minlos.
  The Clay statement is not writable, and the existing Lean does not approach
  it — it rides on a **self-certifying encoding whose axiom predicate is a free
  field**, over content that is a 2×2 matrix.
* **ENTRY POINT FOUND: the lattice form.** Haar measure and finite product
  measures are present; `specialUnitaryGroup` exists. The first genuine theorem
  is **reflection positivity of the Wilson measure on a finite lattice**, which
  upgrades the repo's existing rank-K Gram-PSD toys from algebra to measure
  theory. **Exactly one mathlib gap stands in the way** (§8).

---

## 1–4. The file audit — real Lean, but not about Yang-Mills

None of the six named files is a sketch in the crude sense: **no `sorry`, no
`Prop := True`**, 5–19 theorems each, 353–633 lines. The defect is one level up.

| file | lines | thms | `Prop:=True` | `Unit` | `sorry` |
|---|---|---|---|---|---|
| `YM_ContinuumWightmanV2` | 353 | 5 | 0 | 1 | 0 |
| `YM_ContinuumWightmanV3` | 438 | 7 | 0 | 0 | 0 |
| `YM_ContinuumWightmanV4` | 484 | 10 | 0 | 0 | 0 |
| `YM_WightmanReconstructionScaffold` | 633 | 16 | 0 | 0 | 0 |
| `YM_WightmanContinuumGapsTypedUpgrade` | 525 | 19 | 0 | 0 | 0 |
| `YMWightmanVacuumToyAttempt` | 403 | 17 | 0 | 0 | 0 |

### The structural defect: a self-certifying encoding. FACT

`PF/Referee/StandardClayStatements.lean:80-94`:

```lean
structure StandardYMEncoding where
  GaugeGroup : Type
  QYM : Type
  satisfiesClayAxioms : QYM → Prop     -- FREE FIELD
  massGap : QYM → ℝ                     -- FREE FIELD

def Clay_YangMillsMassGap_Standard (E : StandardYMEncoding) : Prop :=
  ∃ T : E.QYM, E.satisfiesClayAxioms T ∧ E.massGap T > 0
```

**The encoder supplies both the axiom predicate and the witness.** Taking
`QYM := Unit`, `satisfiesClayAxioms _ := True`, `massGap _ := 1` discharges it
immediately. So `Clay_YangMillsMassGap_Standard PF_YMEncodingV4` carries no
information about Yang-Mills; it says the author's own 12-clause conjunction
holds of the author's own witness, and that `3/2 > 0`.

This is the P≠NP spectral-gap defect one level more abstract: there the
*carrier* was arithmetic named after a theorem; here the **axioms themselves are
a parameter**.

### What the content actually is. FACT

* **V4's five "mathlib-backed" fields** are about `Matrix (Fin 2) (Fin 2) ℝ`:
  `IsSymm`, `PosSemidef`, congruence-preserves-PSD, and `trace = 2`. All true,
  all elementary 2×2 linear algebra. "OSRP preservation" is
  `∀ G, G.PosSemidef → (Mᵀ G M).PosSemidef` for 2×2 matrices — **not
  Osterwalder–Schrader reflection positivity for a field theory.**
* **The Hamiltonian is literal**: `interactingHam = !![1, 1/2; 1/2, 1]`
  (`YMInteractingHamiltonianAttempt.lean:113`). Eigenvalues `{1/2, 3/2}`, so the
  "mass gap `Δ = 3/2`" is **the top eigenvalue of a hardcoded 2×2 matrix**, and
  the "mass-gap discriminators" (`0 < Δ`, `1 ≤ Δ`, `Δ ≠ 1`) are arithmetic
  about `3/2`.
* **`GaugeGroup := L2RInf`** — an L² space. The Clay problem's gauge group is a
  **compact simple Lie group** (SU(3)). This is a category mismatch, not an
  approximation.
* **The OS measure is "the 4-dim Gaussian"** (V4 honest-scope H6), i.e. a
  measure on `ℝ⁴`, not on a space of gauge fields.

### 2. Scaffold + ConcreteWitness — what is witnessed

`concreteHamiltonian : L2R →L[ℝ] L2R` with `concreteHamiltonian_eigenvalue` and
`concreteUnitVector`: a concrete operator on `L2R` with one eigenvalue — the
2×2 matrix padded into an L² carrier. `wightmanReconstruction_concrete_witness`
witnesses `WightmanReconstructionConcreteTypedStatement`, **a Prop defined in
the same file**. It witnesses the author's typed statement, not Wightman
reconstruction.

### 3. GapsTypedUpgrade — what gap, against what

The four gaps are the ones the corpus itself names as *"the four genuine
Clay-grade mathlib barriers"* (`YMWightmanVacuumToyAttempt` header, Wave 47B):
**Bochner–Minlos on nuclear spaces, Schwartz reflection, Wightman
reconstruction, mass-gap propagation.**

The file's own theorem names state the scope precisely and honestly:
`bochnerMinlos_typed_holds_at_scaffold_level`,
`schwartzReflection_typed_holds_at_scaffold_level`,
`wightmanReconstruction_typed_holds_at_scaffold_level`,
`massGapPropagation_typed_holds_at_scaffold_level`, then
`four_typed_gaps_imply_YangMillsMassGap`.

**`_at_scaffold_level` is the whole story**: the gaps are discharged for the
finite-dimensional witness, not for the infinite-dimensional objects the
barriers concern. **JUDGEMENT: the naming here is honest and should be
credited** — someone chose names that cannot mislead a careful reader.

### 4. ToyAttempt — toy, and it says so. FACT

Self-described in its own header: *"a finite-dimensional vacuum-plus-one-particle
Wightman-style toy"*, extending a *"rank-K PSD Gram-matrix toy"*. Carries
`⟨0|H|0⟩ = 0 < m ≤ ⟨n|H|n⟩` on a finite-dimensional space. **It is a toy, it is
labelled a toy, and no reconciliation is needed.** Its Gram-matrix PSD core is
the one piece that is reusable — see §8.

## 5. ch23 vs the ledger, line by line — and the ledger misses one. FACT

ch23 has 6 `theorem` environments and 2 `proposition`. Line 309 already carries
an **inline `\manuscriptcorrection{}` ledger note dated 2026-10-05**, which says
of `thm:ym-measure-exists`:

> "this environment states a Clay existence clause verbatim and should not be a
> `theorem`… any claim whose closure would resolve a Millennium problem is
> **CONDITIONAL REDUCTION**, never PROVEN… the 2026-08-06/08 notes refute the
> `ω_c` construction it depends on… What was never changed is the `theorem`
> label itself, which is what a reader scanning environments sees. The same
> applies to `thm:mass-gap-ym` below."

| # | label | line | status |
|---|---|---|---|
| 1 | `thm:alpha-2-properties` | 103 | about `R_f(2,s)` (meromorphic continuation, asymptotics) — **not a Clay claim**; plausibly genuine |
| 2 | `thm:minlos` | 289 | **a citation** of Minlos's classical theorem, correctly attributed |
| 3 | `thm:ym-measure-exists` | 309 | **flagged by the inline note** — Clay existence clause verbatim |
| 4 | `thm:mass-gap-ym` | 357 | **flagged by the inline note** — `Spec(H) ⊂ {0} ∪ [Δ,∞)`, `Δ>0`, the Clay statement verbatim |
| 5 | `thm:area-law` | 432 | **NOT FLAGGED — same defect class.** `⟨W(C)⟩ ∼ exp(−σA)` for large Wilson loops *is quark confinement*, an open problem of the same standing. |
| 6 | `thm:universal-factor` | 490 | rests on the **α-web, which is UNDER-DETERMINED** (a second positive solution exists; `alpha_web_system.py` prints `UNDER-DETERMINED`) |

**The reconciliation is therefore: the ledger is right about 3 and 4, silent
about 5, and 6 rests on content refuted elsewhere.** The inline note's own
remedy — "the labels need to match the ledger" — applies verbatim to
`thm:area-law`, which it does not mention. **JUDGEMENT: this is the
audit-a-guard's-*scope* failure mode again; the guard exists and is correct as
far as it reaches.**

### The mass gap is void at its own constant. FACT

`codex/MANUSCRIPT_READING_LEDGER_COMPLETE_2026-10-08.md:176`:

> "`Delta_YM = 420.43 MeV` is refuted by ch23's 2026-08-06 ledger
> (`omega_c = 2.13198462` **"does not exist"**)"

Since ch23 computes `Δ = ℏc·ω_c·π/10`, a non-existent `ω_c` voids the number.
And the front matter still carries **glossary L90: "Yang-Mills … Solved here:
Delta_YM = 420.43 MeV"** — a publish-level claim contradicted by the chapter's
own ledger. **That is the highest-priority correction on this axis, and it is
Pablo-gated (public text).**

## 6. The vortex/ZPE line — confirmed dead, and mis-filed. FACT

Every `*Vortex*` file in the tree is **`NS3D…`** — Navier–Stokes, not
Yang-Mills (`NS3DVortexStretchingObstruction`, `…BilinearAttempt`,
`…OffDiagonal`, `…UniformGalerkinAttempt`, plus `I5VortexDoublingSubstrateDischarge`
which is an α-web file). One of them is literally named `…Obstruction` and
carries `vortex_stretching_3D_does_not_vanish`.

So: **confirmed, and the sharper point is that there is no YM vortex-ZPE file at
all.** The zero-point content that *was* load-bearing for YM is `ω_c`, and it is
refuted (§5). Moving past it, as instructed.

## 7. The Clay statement — Wightman is not formulable; lattice is. FACT

**The Clay problem** (Jaffe–Witten): for a compact simple gauge group `G`, prove
that a quantum Yang-Mills theory on `ℝ⁴` **exists**, satisfying the Wightman
axioms (equivalently, an OS-positive Euclidean measure with reconstruction), and
has a **mass gap** `Δ > 0` — i.e. the Hamiltonian's spectrum is
`{0} ∪ [Δ, ∞)` with the vacuum simple.

Searched the pinned tree (`.lake/packages/mathlib/Mathlib`, 6860 files):

| concept | files |
|---|---|
| Wightman | **0** |
| Osterwalder | **0** |
| reflection positivity | **0** |
| NuclearSpace | **0** |
| Bochner–Minlos | **0** |

**So the Wightman/OS form is not writable at this pin** — and these are exactly
the four barriers the corpus identified for itself in Wave 47B. Memory's prior
verdict ("not writable, no Wightman/OS") is **confirmed**, now with the numbers.

**What IS present** (and this is the finding): `IsHaarMeasure` / `haarMeasure`
with regularity instances on compact groups (`MeasureTheory/Group/Measure.lean`,
`Measure/Haar/Unique.lean`), **`MeasureTheory.Measure.pi`** — "the product of
finitely many σ-finite measures" (`Constructions/Pi.lean`) — finite-dimensional
normed-space machinery, and `specialUnitaryGroup`
(`LinearAlgebra/UnitaryGroup.lean:207`).

> **Lattice gauge theory is formulable from what exists. The continuum
> Wightman theory is not.**

**But note the honest boundary** (memory's standing caveat, and it is correct):
a finite-lattice gap is a **finite-dimensional** statement and therefore *not*
the Clay content. The Clay content is the gap **uniform in the lattice spacing**
as `a → 0`, together with the continuum limit's OS positivity. The faithful
intermediate — *"the lattice gap is bounded below uniformly in `a`"* — is
**writable as a statement** whose proof is the open problem. That is exactly the
Navier–Stokes situation (faithful Fefferman statement writable, proof open), and
it is the right shape for this axis too.

## 8. Shortest path, and the first concrete theorem

**Do not aim at the mass gap. Aim at reflection positivity of the Wilson
measure**, which is the first genuine lemma of the real constructive programme
(Osterwalder–Seiler), is *true*, is *provable*, and is unambiguously *about*
Yang-Mills.

**First concrete theorem.** For a finite periodic lattice `Λ ⊂ (ℤ/L)⁴` with
edge set `E` and gauge group `G = SU(2)`:

* configuration space `Ω := E → G`, with measure `μ₀ := Measure.pi (fun _ => haar)`;
* Wilson action `S(U) := ∑_{p ∈ plaquettes} (1 − ½ Re tr U_p)`;
* Gibbs measure `dμ_β := Z_β⁻¹ · exp(−β S) dμ₀`;
* time reflection `θ : Ω → Ω` (an involution reflecting the 0-th coordinate);
* **Theorem (reflection positivity):** for every finite family `F₁ … F_n` of
  functions supported on the positive-time half-lattice, the Gram matrix
  `Gᵢⱼ := ∫ (Fᵢ ∘ θ)·F̄ⱼ dμ_β` is positive semidefinite.

**Why this is the right first target — JUDGEMENT.** It converts the repo's
*existing* asset into a real one: Waves 48B–52D already built the **algebraic
core** (rank-1 through rank-K Gram-matrix PSD) — what they lack is an actual
measure. Attaching that algebra to the Wilson measure turns a toy into the first
lemma of the constructive programme, with no new algebra required.

**Machinery needed, precisely:**

| piece | status |
|---|---|
| Haar measure on a compact group | ✅ present |
| `Measure.pi` over the finite edge set | ✅ present |
| `specialUnitaryGroup` as a group | ✅ present (`UnitaryGroup.lean:207`) |
| **compact topological group instance on `specialUnitaryGroup`** | ❌ **NOT present — the one gap** |
| Wilson action continuity/measurability | ✅ routine from matrix continuity |
| Gram-matrix PSD | ✅ **already in the repo** (rank-K toys) |
| finite-dim spectral theory (transfer matrix) | ✅ present |

**The single blocker is the fourth row.** `specialUnitaryGroup` is defined
algebraically as `unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom` — a
`Submonoid (Matrix n n α)` — and I found **no `CompactSpace` or topological-group
instance** for it. Haar measure needs one.

**That gap is bounded and standard:** `SU(2)` is a closed, bounded subset of the
finite-dimensional normed space `Matrix (Fin 2) (Fin 2) ℂ`, so compactness
follows from the finite-dimensional Heine–Borel machinery mathlib already has.
**Estimated: one file — the topological-group and compactness instances for
`specialUnitaryGroup`, which is also a clean mathlib-contribution candidate** (a
genuine one, unlike anything else on this axis).

## 9. Verdict

**Clay/Wightman form: BLOCKER NAMED** — four mathlib barriers, all at zero, all
previously identified by the corpus itself. No amount of work on the existing
V2/V3/V4 stack approaches it, because that stack's headline is a
self-certifying encoding over a 2×2 matrix.

**Lattice form: ENTRY POINT FOUND**, one missing instance away.

**Recommended sequence:**

1. **Compactness + topological group instances for `specialUnitaryGroup`.** One
   file. Unblocks everything and is a real mathlib contribution.
2. **The Wilson measure on a finite lattice** (`Measure.pi` + Haar + Wilson
   action). Definitional, no open mathematics.
3. **Reflection positivity of the Wilson measure**, consuming the existing
   rank-K Gram-PSD algebra. **The first genuine Yang-Mills theorem in the repo.**
4. *Then* state the faithful intermediate — the gap uniform in lattice spacing —
   as an explicitly open conditional, the NS-faithful-statement pattern.

**Two corrections owed regardless of any build, both Pablo-gated (public text):**
the glossary's "Yang-Mills … Solved here: Δ_YM = 420.43 MeV", refuted by ch23's
own ledger; and `thm:area-law`'s `theorem` label, which the 2026-10-05 inline
note's own remedy covers but which it does not mention.

**OPEN / not done here:** whether V2 and V3 contain anything beyond what V4
bundles (I read V4's record and the shared constants, not V2/V3 line by line);
the exact cost of the `specialUnitaryGroup` compactness instances; and whether
`Measure.pi` composes with Haar as smoothly as expected (the σ-finiteness side
conditions on a compact group should be free, but I have not elaborated it).

---

## Label summary

* **FACT (quoted from source):** `StandardYMEncoding`'s free `satisfiesClayAxioms`
  and `massGap` fields and `Clay_YangMillsMassGap_Standard`'s definition;
  `interactingHam = !![1,1/2;1/2,1]`; V4's five fields over `Matrix (Fin 2) (Fin 2) ℝ`;
  `GaugeGroup := L2RInf`; the `_at_scaffold_level` theorem names; the ToyAttempt
  header's self-description; ch23's six theorem labels and the inline 2026-10-05
  correction; the `ω_c` "does not exist" ledger line; glossary L90; the mathlib
  zero-counts and the present-machinery locations.
* **JUDGEMENT (mine):** that the encoding defect is the P≠NP pattern one level
  more abstract; that the `_at_scaffold_level` naming is honest and deserves
  credit; that `thm:area-law` is the same defect class as 3 and 4 and the
  ledger's scope misses it; that reflection positivity is the right first
  target; that the `specialUnitaryGroup` compactness instance is the single
  blocker and a real mathlib contribution.
* **NOT established:** that no continuum route exists — only that this pin
  cannot state one and this stack does not approach one; V2/V3 read only
  through V4's bundling; the cost estimates in §8.
