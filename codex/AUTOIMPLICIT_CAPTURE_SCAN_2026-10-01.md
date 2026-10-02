# autoImplicit silent-capture scan — 2026-10-01, NEGATIVE RESULT

**Result: the `YangMillsPerelmanTemplateY1Y4Discharge` defect is not systemic. Across
all 2,227 non-panel modules there are zero other sites where a project α- or
H₃-constant is silently captured as an implicit variable. Detector validated against
the known case.**

## The hazard

PF does not set `set_option autoImplicit false`, and the lakefile sets no
`leanOptions`, so Lean's default applies: an identifier that **fails to resolve** in a
declaration's signature is silently bound as a fresh implicit variable. The statement
then quantifies over an arbitrary value of that type while the theorem's *name* goes on
claiming the named constant. Nothing fails. The file compiles.

This is a sharper hazard here than in most projects for a specific structural reason:
the corpus root namespace is `PrincipiaTractalis` (6,056 files) but nine outliers sit
under `PrincipiaFractalis`, so a file in one family referring to a constant declared in
the other resolves only if it opens that namespace explicitly.

`PF/YangMillsPerelmanTemplateY1Y4Discharge.lean` was exactly this: namespace
`PrincipiaTractalis`, opening `PrincipiaFractalis.PerelmanBackwardUnifiedAttack` but
not `PrincipiaFractalis.H3UnifiedMillenniumStructure`, which is where
`def alpha_YM_H3U : ℝ := 2` lives. Every statement in the file mentioning it quantified
over an arbitrary real. It surfaced **only** because one proof happened to run
`unfold alpha_YM_H3U`, which fails on a local variable. Had that proof used `norm_num`
or `simp` instead, the file would have compiled and the defect would have been
invisible. Fixed by one `open`.

That accident is the reason for this scan: the question is how many files got away with
it.

## Method

`scripts/`-independent read-only scan (`/tmp/autoimplicit_scan.py`). For every
non-panel module: strip comments, collect the file's `namespace` declarations and its
`open`s, collect unqualified uses of constants in the α / H₃ families, and look up each
constant's declaring namespace in a corpus-wide index built from `def`/`abbrev`
declarations with namespace nesting tracked. Flag a use when no declaring namespace is
opened by the file and none is a prefix-relative of the file's own namespace.

- modules scanned: **2,227** (panel tier excluded — generated, declares no constants)
- constants indexed: **71** (`alpha_*`, `H3_*`, `*_H3U`, `framework_alpha`)
- potential sites reported: **2**, both false positives (below)

## Detector validation

A detector with no demonstrated positive is not evidence. Checked against the known
case by re-running resolution on that file's text with and without the fix line:

```
WITHOUT the open (pre-fix)   resolves=False  -> FLAGGED
WITH the open (current)      resolves=True   -> clean
```

So the scan does detect the defect class it claims to detect, and the live corpus is
clean of it only because the one real instance has been repaired.

## The two reported sites are false positives

Both are `alpha_value` in `PF/NumberTheory/BealConjectureFrameworkAttack.lean` and
`PF/NumberTheory/InverseGaloisProblemFrameworkAttack.lean`:

```
alpha_value : alpha_Beal = 3        -- structure FIELD declaration
alpha_value := alpha_Beal_in_bracket -- structure instance FIELD assignment
```

These are structure field names that coincide with a `def alpha_value` in
`PrincipiaTractalis.MillenniumSix`. A field name in a structure declaration or
instance is not an identifier reference and is never autoImplicit-captured. The scan
does not distinguish the two syntactic positions; that is a known limitation of the
scan, not a finding about the corpus.

## Scope of the claim, stated precisely

This clears **the constant families the framework's numeric claims rest on** — the α
values and the H₃ Coxeter data. It is not a claim about every identifier in the corpus:
a capture of some unrelated name elsewhere would not be caught by this scan, because
the index only covers those 71 constants.

The complete and permanent fix for the whole class is `set_option autoImplicit false`
(project-wide, as mathlib does), which converts every such capture from silence into a
compile error. That is a one-line lakefile change whose cost is entirely in whatever it
then surfaces, and it cannot be assessed without a full corpus build. Recorded here as
the available structural fix; **retirement condition** for this document is that option
being set and the corpus building under it, after which this scan becomes unnecessary.

## Provenance

- Scan: `/tmp/autoimplicit_scan.py`, run against the live tree 2026-10-01, read-only,
  no builds. Findings JSON: `/tmp/autoimplicit_findings.json`.
- The repaired instance: commit `2c1e7437`.
