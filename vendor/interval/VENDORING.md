# Vendored: girving/interval (ported)

Kernel-verified interval arithmetic — the RH-arc Route B certified-numerics engine.
See `codex/INTERVAL_SPIKE_2026-07-24.md` (GO-WITH-PORT verdict) and
`codex/HARDY_SCOPING_2026-07-24.md`.

## Provenance

- **Upstream:** https://github.com/girving/interval (Geoffrey Irving)
- **License:** Apache 2.0 — `LICENSE` preserved in this directory; all credit for
  the library design and proofs belongs upstream.
- **Base commit:** `2eb9470` (upstream v4.23.0-rc2 era, 2025-08-15)
- **Port date:** 2026-07-24
- **Port target pin:** lean4 `v4.24.0-rc1`, mathlib `eed770a434957369c6262aa3fb1d6426419016d4`
  (identical to `PF_Lean4_Code`'s pin — lake resolves a single shared mathlib)
- **Patch:** ~50 mechanical lines across 5 files, recorded at
  `codex/interval-port-2eb9470-to-v4.24.0-rc1.patch` (applied here; the vendored
  tree = `2eb9470` + that patch + the deletions below).

## Local deletions (not upstream)

- `Interval/EulerMaclaurin/` (7 files) — removed entirely. Three files
  (`IteratedDerivArith`, `PartialDerivCommute`, `LHopital`) have non-mechanical
  proof regressions on our pin; the other four transitively import them. Nothing
  we consume needs Euler–Maclaurin. The two corresponding imports were dropped
  from `Interval.lean` (marked with a `-- PF vendoring` comment).
- Spike scratch files (`SpikeTest.lean`, `SpikeScale.lean`) and upstream
  `.github/`, `.vscode/`, `.git/`, `.lake/` — not copied.

## Standing rule: the `interval` tactic is BANNED in the corpus

`Interval/Tactic/Interval.lean` (the `interval` tactic) uses `native_decide`
(`ofReduceBool` / trust-the-compiler), which violates corpus discipline
(axiom budget exactly `[propext, Classical.choice, Quot.sound]`, no
`native_decide` on any consumed path). It is kept in the tree for fidelity to
upstream but MUST NOT be used from `PF_Lean4_Code`.

Instead certify inequalities kernel-clean via:

```lean
have h : x ∈ approx x' := by approx        -- @[approx] instrumentation
exact Interval.approx_lt hx hy (by decide +kernel)   -- or Interval.approx_le
```

`test/` also uses `native_decide` (upstream's own test suite, incl. the
`test/axioms.lean` guard that the core library itself is native_decide-free);
`test/` is only built by `lake test` inside this package and is never on a
consumed path.

## Re-porting expectation

Upstream has no releases and no commit on v4.24.x; any future toolchain/mathlib
bump of the corpus requires re-porting (expect small mechanical patches in the
same style).
