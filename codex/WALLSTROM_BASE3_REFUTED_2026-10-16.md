# Wallstrom from base-3: the H¹ lead is DECORATION, not derivation

**Date:** 2026-10-16 (Legion). Scoping; no Lean. **The lead was mine, and it is
refuted.** Three independent obstructions, two of them already adjudicated in
this corpus and one conceded verbatim in its own published papers.

**Verdict: the projective limit of `ℂ^(3^k)` cannot force
`∮ m v·dl ∈ 2πħℤ`. It does not even accommodate it in the right group. The
Nelson route is not put back in business by this.**

---

## 1. The exact statement that would need proving — JUDGEMENT (framing), standard mathematics

Let `ρ(·,t)` be the gap-2 diffusion's density, `N_t = {ρ = 0}` its node set,
and `M_t = supp ρ \ N_t` the configuration region where the phase is defined.
Nelson sets `v = ∇S/m` and `ψ := √ρ · e^{iS/ħ}`.

`ψ` is single-valued **iff** the real 1-form

  `θ := (m/ħ) · v♭`  (the phase 1-form, `v♭ = g(v, ·)`)

is closed with **integral periods**:

  `[θ] ∈ image( H¹(M_t; ℤ) → H¹(M_t; ℝ) )`,

equivalently `∮_γ m v·dl ∈ 2πħℤ` for every closed `γ ⊂ M_t`, equivalently
`θ = u*(dφ)` for some `u : M_t → U(1)`. **This is an integrality condition on
a degree-one cohomology class** — the same species as Weil's prequantization
condition, one degree down.

So the target is:

> **Target.** Derive, from the substrate, that the admissible phase 1-forms
> have integral periods — i.e. that the relevant `H¹` receives a **ℤ**-lattice
> and `[θ]` lands in it.

Two things must come out: a nontrivial `H¹` (else there is nothing to
quantize *and* vortices are excluded), and that its integral lattice is **ℤ**,
not some denser group.

## 2. Does the tower force it, or accommodate it? — **neither. It obstructs it.**

### Obstruction A — `K₁(T_∞) = 0`: there are no circulation classes. FACT (classical, and stated in the corpus)

`codex/SUBSTRATE_FORCES_WHAT_2026-07-26.md:115-137` gives the complete rigid
invariant table for `M_{3^∞}`, citing the corpus's own
`ch04_timeless_field.tex:380-435` (Thm 4.16):

| Invariant | Value |
|---|---|
| `K_0` (ordered, with order unit) | `(ℤ[1/3], ℤ[1/3]₊, 1)` |
| **`K_1`** | **`0`** |
| tracial state space | one point `{τ}` |
| pairing image `ρ : T × K_0 → ℝ` | exactly `ℤ[1/3]` |
| `Aut(A)` action on `K_0` | trivial |

`K₁` is the noncommutative home of `H¹`. For AF algebras — and UHF ⊂ AF —
`K₁ = 0`. **The substrate has no degree-one classes at all.**

Consequence, and it is worse than "fails to derive": if the configuration
region's topology were inherited from `T_∞`, every closed 1-form would be
exact, forcing `∮ m v·dl = 0` for all loops. That is not quantization — it is
the **exclusion of every vortex state**, i.e. of all nonzero angular
momentum. The hydrogen `ℓ ≠ 0` states would be unreachable.

*(Note: `K₁ = 0` is stated in the book and the codex table as a classical
Glimm fact; it is **not** formalized in Lean —
`PF/Consciousness/TimelessFieldKTheoryUpgrade.lean` contains no `K_1`
statement. So this obstruction is paper-level, not kernel-level.)*

### Obstruction B — the available integrality is `ℤ[1/3]`, which is DENSE. FACT + arithmetic

The only real numbers anywhere in that table are `ℤ[1/3]` and `3^ℤ` — the
document says so explicitly: *"the only real numbers occurring anywhere in it
are the elements of `ℤ[1/3]`, together with `3^ℤ`. Every one of them is
rational."*

Quantization needs a **lattice** (discrete subgroup of ℝ). `ℤ[1/3] = {a/3^k}`
is **dense in ℝ**: the largest gap in `ℤ[1/3] ∩ [0,1]` at denominator `3^k` is
`3^{-k}` → computed: `0.333` (k=1), `1.37e-3` (k=6), `3.54e-12` (k=24). So a
condition `∮ ∈ 2πħ·ℤ[1/3]` imposes **no discreteness whatever**. Angular
momentum would range over a dense set. This is not "a different lattice" — it
is **not a lattice**.

**The same obstruction, from the same source, that killed the α-web.** r123's
`ℤ[1/3]` trace range is why seven of nine α-values lie outside the substrate's
reach; it is why the K-theoretic channel is recorded as provably obstructed.
It obstructs Wallstrom for the identical reason. That coherence is worth
noting: the substrate's arithmetic is triadic-rational, and quantization
conditions need integers.

### Obstruction C — the levels quantize; the limit destroys it. JUDGEMENT (the construction), arithmetic (the collapse)

The most generous reading of the lead: let phases at level `k` live in
`ℤ/3^k`. Then circulation sits in `(2πħ/3^k)ℤ` — genuinely a lattice at each
finite level. But the substrate **is the projective limit**, and the spacing
collapses:

```
k=1   2.209e-34      k=10  1.122e-38
k=2   7.362e-35      k=20  1.900e-43
k=5   2.727e-36      k=40  5.450e-53      (required: 2πħ = 6.626e-34)
```

`k → ∞` gives spacing `0`. **Quantization holds at every finite level and is
destroyed in exactly the limit PF uses.** The tower's discreteness is a
finite-level artefact.

### Obstruction D — base 3 plays no role, per the corpus's own papers. VERBATIM CONCESSION

`Papers/uhf_faithful_trace_glimm_2026-07-23.tex:333-337`:

> "The choice of base 3 over the more common CAR tower `M_{2^∞}` is inherited
> from the source project's surrounding ternary constructions; as a
> classification target the two are equally standard, and **every argument
> below works verbatim in any base ≥ 2**."

`Papers/glimm_uhf_lean4_2026-07-23.tex:264-266`:

> "**The base 3 plays no special role**; every argument below works verbatim
> for any base ≥ 2, and the choice is inherited from the source project's
> ternary conventions."

A structure that works identically in every base cannot supply a
base-3-specific quantization. This is the cleanest possible refutation of "the
one place base-3 might do work": **its own authors already recorded that it
doesn't.**

## 3. What the lattice spacing being ħ costs — and whether any of it can move

Suppose Obstructions A-D were somehow circumvented and an integral `H¹` were
produced. The target is `∮ ∈ 2πħℤ`. A topological argument can at best
deliver `∮ ∈ cℤ` for **some** constant `c` fixed by the geometry — it cannot
deliver the *value* of `c`.

* **Where the import enters:** `c = 2πħ` is the lattice **spacing**.
  Topology/cohomology is scale-free: `H¹(·;ℤ)` has no preferred normalisation,
  so the spacing must come from outside.
* **Can it move?** No, on the evidence already gathered. The classical route
  is dead by mass-scaling (`D_q ~ m⁻¹` vs `D_cl = Gm/c ~ m⁺¹`, magnitudes
  apart by `~10⁴⁴`); the substrate route is dead because the corpus **imports
  `ħ` into the timeless field's own evolution equation** (`ch04:658, 673, 683`
  — see `SUBSTRATE_HBAR_IS_INPUT_2026-10-16.md`).
* **So the honest best case** for a successful topological derivation would be:
  *circulation is quantized in units of some `c`*, with `c = 2πħ` an input.
  That is still worth something — it would convert Wallstrom's condition from
  an *imposed constraint* into a *structural consequence with one parameter* —
  but it is not a derivation of quantum mechanics, and it is not what the lead
  promised.

## 4. Consequences

1. **My H¹/base-3 lead is withdrawn.** I offered it in
   `GAP3_BORN_RULE_SCOPE_2026-10-16.md` as "the only point in this programme
   where base-3 could do mathematical work rather than supply a label." That
   was wrong, and the corpus had already recorded why — in a table I should
   have read first (`SUBSTRATE_FORCES_WHAT_2026-07-26.md`) and in its own
   papers' concessions. Cost: one afternoon, caught before anything was built.
2. **Wallstrom remains open and remains the gating question.** Nothing here
   resolves it; what is resolved is that *this* attack does not.
3. **The strategic point from the gap-3 note stands, unchanged and now
   sharper.** Wallstrom is a precondition for the Nelson route meaning
   anything, and it has no substrate route. Spending gap-2 effort while
   Wallstrom stands unresolved still risks deriving a theory strictly weaker
   than quantum mechanics.
4. **Where a Wallstrom attack could still come from** — flagged as directions,
   not leads, and none substrate-based: the nodal/vortex topology of `ρ` itself
   (`H¹(supp ρ \ N_t)` is generated by loops around nodal lines, and *that*
   `H¹` is genuinely nontrivial and has a ℤ-lattice — it is a property of the
   wavefunction's zero set, not of the substrate); or geometric quantization
   proper, where integrality is imposed on a prequantum line bundle and the
   question becomes why that bundle exists.

---

## Label summary

* **FACT (classical, cited in corpus):** `K₀(M_{3^∞}) = ℤ[1/3]`, `K₁ = 0`,
  unique trace, `Aut` acts trivially on `K₀`, `K₁(AF) = 0`.
* **FACT (verbatim quotes):** both UHF papers state base 3 plays no special
  role and every argument works in any base ≥ 2.
* **ARITHMETIC (computed here):** `ℤ[1/3]` gap sizes `3^{-k}`; level-`k`
  spacing `2πħ/3^k` and its collapse; the `10⁴⁴` mass-scaling figure from the
  gap-2 scope.
* **JUDGEMENT (mine):** the framing of Wallstrom as an `H¹` integrality
  condition; that `K₁ = 0` transfers to "no circulation classes" for an
  emergent configuration space; the `ℤ/3^k` level construction in Obstruction
  C; the assessment that the spacing cannot be moved; the directions in §4.4.
* **NOT established:** that no construction from `ℂ^(3^k)` could ever force
  quantization. What is established is that the substrate's *invariants* —
  which are all there is, since the table is complete and rigid — contain no
  ℤ-lattice and no degree-one classes.
