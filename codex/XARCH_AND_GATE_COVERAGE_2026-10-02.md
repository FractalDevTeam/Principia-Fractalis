# Cross-architecture confirmation, and three defects it exposed in the gate's axiom criterion

2026-10-02

**Two independent results, causally linked.**

1. `T_infinity_rigidity` and r123's two self-refutations verify identically on
   **aarch64**, from byte-identical sources: 3,266 jobs, exit 0, zero errors, and
   **all 195 audited declarations carry exactly `[propext, Classical.choice,
   Quot.sound]`** — one distinct axiom set across the whole closure.

2. Verifying that exposed **three distinct defects in `pristine_gate.sh`
   criterion (b)**, the axioms-clean criterion. Every past
   `PRISTINE over N declarations` paste for a multi-namespace module **overstated
   what (b) actually inspected.** All three are fixed, with a regression fixture
   that includes the negative control the old code failed.

The theorems were never in doubt and are not in doubt now — point 1 establishes
that independently, by a correct method, on two architectures. What was wrong is
the *instrument's report of its own coverage*. That distinction is the whole
content of this note.

---

## Part 1 — the aarch64 confirmation

### The machine

Jetson AGX Xavier, `192.168.0.102`, user `xluxx`. `5.10.120-tegra`, **aarch64**,
8 cores, 14 Gi RAM + 7 Gi swap. Tree at `/mnt/pf-build/pf`.

Usable at all because **mathlib was already built there for aarch64** — 6,866
oleans — with `lake-manifest.json` md5 `ce569bf7613b62cde405782338fcf870`,
**identical to Acer's**. Same dependency set, same `leanprover/lean4:v4.24.0-rc1`
pin, `vendor/interval` present.

### Provenance

Non-panel sources tarred from Acer at master `8fc0a376` (5.7 MB gzipped), pushed
to Xavier, extracted over the existing tree, then verified by md5 against Acer:

| file | md5, both machines |
|---|---|
| `PF/AlphaFromSubstrateKTheory_r123.lean` | `eccefe8d79687622b06fa2b8a6150b8a` |
| `PF/SubstrateRigidity.lean` | `10b267c7b8f0cbdfc0412b17e4c5e9cf` |

The aarch64 build is of the same bytes, not of a near-enough copy.

### Result

`lake build PF.Audit.PremiseAudit PF.AlphaFromSubstrateKTheory_r123 PF.SubstrateRigidity`
→ **Build completed successfully (3266 jobs)**, `EXIT=0`, zero errors, zero `sorry`.

| theorem | axioms on aarch64 |
|---|---|
| `T_infinity_rigidity` | `[propext, Classical.choice, Quot.sound]` |
| `coupling_H3_identity_holds_for_every_alpha` | `[propext, Classical.choice, Quot.sound]` |
| `resonance_phase_two_periodic` | `[propext, Classical.choice, Quot.sound]` |
| `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant` | `[propext, Classical.choice, Quot.sound]` |
| `bare_route_alpha_memZ13` | `[propext, Classical.choice, Quot.sound]` |

Across all 195 `depends on axioms` records in the log there is exactly **one**
distinct axiom set, the standard three. Log: `/tmp/xavier_confirm.log` on Xavier,
copy at `codex/logs/xavier_confirm_2026-10-02.log.txt`.

These records come from the modules' **own authored `#print axioms` blocks**,
which is why Part 2 does not undermine them: that path is independent of the
gate's generated probe.

### Why these five

- **`T_infinity_rigidity`** — the framework's strongest positive result (Glimm
  1960 UHF classification at supernatural `3^∞`, over an arbitrary
  `CStarAlgebra` carrying a `Substrate3Inf` witness).
- **`coupling_H3_identity_holds_for_every_alpha`** and the mod-2 pair
  (`resonance_phase_two_periodic`,
  `alpha_P_sq_eq_alpha_YM_not_mod_two_invariant`) — r123's self-refutations, now
  load-bearing for the honest presentation of the α framework. **A negative
  result about one's own thesis is what most benefits from independent
  confirmation**, being the claim a reader is least inclined to take on trust and
  most inclined to suspect of loose statement.
- **`bare_route_alpha_memZ13`** — the one positive convergence that survives them.
- **`PF.Audit.PremiseAudit`** also built clean (one deprecation warning,
  `Lean.ConstantInfo.isTheorem`). Confirming the *instrument* bears on everything
  it has audited.

### The finding that made this cheap

`PF/SubstrateRigidity.lean` is 2,513 lines of C\*-algebra; I had assumed it was
expensive. **Its import closure is 44 modules**, almost entirely mathlib, and
panel-free. `PF.Audit.PremiseAudit` is **1**; `r123` is **43**.

So the headline theorem is cheap to confirm **anywhere mathlib is already
built** — a ten-minute job, not a campaign. It should be standard before
anything goes out.

### Cost note

2026-09-29 → 10-02 this node ran
`lake build PF.Analytic.RiemannXiBottomEdgeAtMinus15_r331d` — **the target Acer
was already building**, at 181 panels/day against Acer's 538. Lean oleans are
architecture-specific, so its output could never have been consumed by Acer
regardless. Three days bought nothing and the next twenty would have bought
nothing. Killed; the node did something useful within the hour.

---

## Part 2 — three defects in criterion (b)

Found while writing the Part 1 verification: my first non-standard-axiom scan
appeared to flag every declaration. That was a bug in *my* scan, and chasing it
found the same bug in the gate.

### Defect 1 — wrapped axiom lists were skipped entirely

Lean wraps long axiom lists:

```
info: PF/X.lean:12:0: 'Foo.bar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`pristine_gate.sh:277` scanned with `grep -oE "depends on axioms: \[[^]]*\]"`.
`grep` is line-oriented and `[^]]*` cannot cross a newline, so a wrapped record
has no closing `]` on its line and **matches nothing at all** — it is silently
dropped from the allowlist scan.

Measured on the real Xavier log: **33 of 195 records matched, 162 skipped (83%).**
Wrapping is prefix-length dependent, so the rate differs by context — in the
gate's own probe output it was 2 of 93. Both matter: the 83% case is what
build-log audits see.

### Defect 2 — the probe resolved almost no names (the big one)

The probe emitted **bare** names under a single `open` built by pasting every
`namespace` line into one dotted path (`:259`, `:264`). For nested namespaces
that path names only the *innermost* scope, and `open A.B.C` does not open `A.B`.
So declarations in outer namespaces never resolved, produced no axiom record, and
were silently absent — while the PASS line still cited the full declaration count.

On `PF/GaussLowerBound_r209.lean` (`namespace PrincipiaTractalis.GaussLowerBound`
at `:129`, `namespace GaussWeights` at `:528`): the old probe opened
`PrincipiaTractalis.GaussLowerBound.GaussWeights` and produced **3 axiom records
for 88 probed declarations**, then printed
`PASS (b) ... over 88 declarations`.

**299 of 1,381 non-panel modules (22%) have more than one `namespace` line** and
were therefore under-resolved. Five are headline or recently-claimed-pristine:

| module | `namespace` lines | qualified | old bare-unique |
|---|---|---|---|
| `PF/SubstrateRigidity.lean` | 3 | 53 | 33 |
| `PF/H3CoxeterDiagramDerivation.lean` (r341) | 2 | 45 | 41 |
| `PF/Analytic/RectangleLogBranch_r331g.lean` | 2 | 38 | 38 |
| `PF/AlphaFromSubstrateKTheory_r123.lean` | 2 | 31 | 31 |
| `PF/SubstrateIdempotentTraceRigidity.lean` (r335) | 2 | 5 | 5 |

### Defect 3 — `sort -u` on bare names collapsed distinct declarations

Deduplicating *short* names merges declarations that legitimately share a name
across namespaces. On `SubstrateRigidity` that is **53 declarations collapsing to
33** — 20 silently never probed even had the `open` been right.

### What bounded the real risk

`sorryAx` was checked separately, by a single-token `grep -qE "sorryAx"` immune to
all three defects. So a sorry-based hole would always have been caught, and
criterion (c) independently greps the module's own code for locally declared
`axiom`. The genuine exposure was narrower than "83% unchecked" sounds: a
**non-standard axiom inherited from an import**, in a module where the records
were skipped. No such axiom exists — Part 1 establishes that for the closure that
matters — but the gate was not what established it.

---

## The repair

**`scripts/lib/qualified_decls.py`** (new) emits the fully-qualified name of every
*probeable* theorem/lemma, removing the dependence on `open` entirely. It strips
Lean comments itself (nesting `/- -/`, `/-- -/`, `--`) rather than trusting the
caller, because doc-comment prose defeats a line regex — `PF/SubstrateRigidity.lean:1929`
reads `lemma is a direct \`Classical.choose_spec\` projection. -/`, from which the
first version of this helper duly extracted a declaration named `is`.

It **excludes `private` declarations and reports how many**. Lean mangles those to
`_private.<Module>.0.<Namespace>.<name>`, so `#print axioms` cannot resolve the
plain qualified name. This is not a hole: a private lemma's axioms appear in the
dependency closure of every public declaration that uses it, and `#print axioms`
on a public theorem reports that whole closure. It is disclosed so the coverage
arithmetic stays truthful.

**`scripts/pristine_gate.sh`** criterion (b) now:

- joins each axiom record onto one line (awk, accumulate to the closing `]`) before scanning;
- **refuses to certify** if the joined record count differs from the number of
  opening records — a parser that lost or merged a record certifies nothing;
- probes fully-qualified names from `$SRC`, with no `open`;
- reports **records actually inspected** against **probeable declarations**, and
  WARNs (never passes) when a probed declaration produced no record;
- names the private-exclusion count in the PASS line.

### Regression fixture

`scripts/tests/test_axiom_scan.sh` runs the old and new pipelines side by side on
the real 195-record Xavier log plus three planted fixtures:

| fixture | OLD verdict | NEW verdict |
|---|---|---|
| real log, unmodified | PASS, 33/195 inspected | CERTIFY, 195/195 |
| **non-standard axiom, wrapped** | **PASS — misses it** | **BAD `PlantedBadAxiom`** |
| non-standard axiom, single line | BAD (caught) | BAD (caught) |
| malformed, merged records | PASS | PARSE_INCOMPLETE, refuses |

Row 2 is the negative control and the point of the exercise: the old pipeline
reports a clean pass on a planted non-standard axiom purely because the list
wrapped.

---

## Re-gate results

| module | before | after |
|---|---|---|
| `PF.AlphaFromSubstrateKTheory_r123` | (b) over 31 claimed | **PRISTINE** — (b) over **31/31** probeable |
| `PF.GaussLowerBound_r209` | `PASS (b) over 88` / 3 records | (b) **93/93**; still NOT PRISTINE on (d2) |
| `PF.SubstrateRigidity` | (b) over 53 claimed | (b) **PASS 32/32** probeable, 21 private disclosed |

`SubstrateRigidity` remains **NOT PRISTINE** on criterion **(d2)**, which is
pre-existing and unrelated to the axiom work.

**Settled the same day, and favourably.** `#audit_premises` run directly over all
32 public declarations of the module:

> `O-CIRC audit of PrincipiaTractalis.SubstrateRigidity.T_infinity_rigidity: CLEAN`
> `(1543 constants in cone, boundary = PrincipiaTractalis)`

**The headline theorem is CLEAN: it consumes everything it assumes, so the `3^∞`
substrate structure is load-bearing in the proof, not merely carried.** That was
the live worry and it is answered.

Across those 32 declarations: 10 CLEAN, 22 with findings, **116 findings, every
one of them DEAD — zero CONTAINED, zero VACUOUS.** The distinction matters and
runs the reassuring way: DEAD means the conclusion holds *without* that
hypothesis, i.e. the lemma is more general than stated (over-hypothesis, a
hygiene matter). VACUOUS would be the dangerous kind — contradictory hypotheses
making a statement empty — and there are none anywhere in the module.

Of the 116 dead fields, **109 are mathlib structure projections**, which is
instance-projection noise rather than PF hypotheses: `NeZero.out` (27),
`StarAlgHom.toAlgHom` (18), `StarAlgHom.map_star'` (18), `Fin.val` (17),
`Fin.isLt` (17), `CStarAlgebra.toCStarRing` / `toCompleteSpace` (5 each),
`OrthonormalBasis.repr` (2). **Only 7 involve a real PF structure field** —
`Substrate3Inf.tower_dense` (4), `tower_matrix` (2), `tower_mono` (1) — in three
auxiliary lemmas (`Substrate3Inf.connect_unital`, `connect_iso`,
`tower_level_isClosed`) that simply do not need the full `Substrate3Inf`
structure and could be restated with weaker hypotheses.

One accounting note: the gate reports 20 findings where this sweep reports 116,
because the gate's (d2) still drives `#audit_all` from the **bare-name** list
(`:216`) that defect 3 above collapses. The character of the findings is
identical; only the target set differs. Migrating (d2) onto
`qualified_decls.py` is the obvious follow-on and is not done here.

## Re-gated 2026-10-03 — all three PRISTINE, and the run found a further bug

`r341`, `r331g` and `r335` were re-gated on Legion against their existing oleans,
no rebuild. All three are **PRISTINE**, and the `(b)` and `(d2)` declaration counts
now agree on every one:

| module | (b) inspected records | (d2) decls |
|---|---|---|
| `PF.Analytic.RectangleLogBranch_r331g` | 37 / 37 probeable | 37 |
| `PF.H3CoxeterDiagramDerivation` | 41 / 41 probeable (+4 private) | 41 |
| `PF.SubstrateIdempotentTraceRigidity` | 5 / 5 probeable | 5 |

**The first run of `r331g` reported `(b)` over 4 declarations while `(d2)` on the
same run reported 37.** That disagreement exposed a bug in the fix described
above: `qualified_decls.py` prints names containing subscripts
(`div_cancel_left` with a subscript zero), Windows stdout defaults to cp1252, the
helper died with `UnicodeEncodeError` after 4 names, and
`mapfile -t DECLS < <(python3 ...)` discarded the exit status — so the gate
certified a clean pass over 11% of the file. The same defect class this document
is about, reintroduced by the enumerator it introduced. Acer was never affected
(UTF-8 locale), which is why it reported honest counts throughout.

Fixed in **`bf140ed4`**: UTF-8 forced on the helper's stdout, and the gate now
runs the enumerator to a file and **checks its exit status**, refusing to certify
if it failed — the enumerator-side analogue of the `REC_JOINED != REC_SEEN`
invariant guarding the record parser.

**Keep the `(b)` vs `(d2)` cross-check.** The two criteria enumerate declarations
by independent routes, so they should agree; when they disagree, one of them is
wrong. That is what caught this, and it is cheaper than any amount of re-reading
the enumerator.

## What this does and does not establish

**Does:** the kernel verdicts reproduce on x86_64 and aarch64 from identical
sources, so they are not artifacts of one toolchain build, one libc, one word
size, or one floating-point environment; and criterion (b) now inspects what it
says it inspects, with a fixture that fails if it regresses.

**Does not:** say anything about whether the theorems mean what their names
suggest. For much of the α area the answer is recorded in
`codex/ADVERSARIAL_ALPHA_2026-10-02.md`. A theorem vacuous on x86_64 is vacuous
on aarch64 too.
