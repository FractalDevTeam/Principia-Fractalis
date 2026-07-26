# `PF/` — SHAPE INDEX. NOT CROSS-PROVER VERIFICATION.

**Read this before citing, quoting, or counting anything in this directory.**

This directory is **not** a proof corpus. It is a **declaration-name and
dependency-shape index** of the Lean 4 corpus in `../../PF_Lean4_Code/`. It records
*which Lean theorem names exist* and *how the files depend on one another*. That is its
only function.

Of the **9,860** proof obligations in these 761 `.v` files, **7,367 (74.7%)** are literally

```coq
Theorem some_impressive_sounding_name_parity : True.
Proof. exact I. Qed.
```

`True` is the trivially true proposition and `exact I` is its one-line inhabitant. Such a
`Theorem` asserts **nothing**. Declarations that are not literally `: True` very often
state a `Definition ... : Prop := True` alias (e.g. `honest_scope_coq_parity_only`,
`L1_alpha_P_sq_eq_alpha_YM`), or a `Record` all of whose fields are such aliases — closed
by `repeat (split; [exact I|]); exact I`. These are the same thing wearing a longer name.

**The headline statistics for this tree measure nothing.** "9,808 Theorems / 9,860 Qed /
0 Admitted" counts *syntax*, not mathematics. Every one of those 7,367 `Qed`s closes the
trivial goal. A `Qed` count over this tree is not evidence of anything, and the "0
Admitted" figure is additionally **false** (see below).

## Real Coq proofs live in `../PF_Real/`

`../PF_Real/` contains genuine machine-checked mathematics: 110 lemmas/theorems across
four files, **zero** `exact I`, **zero** `Admitted`, **zero** `Axiom`, and every headline
result confirmed by `Print Assumptions` to be *"Closed under the global context"*.

> **Anyone citing cross-prover verification of Principia Fractalis must cite
> `../PF_Real/`, and must never cite this tree.** This directory cannot support a claim of
> independent verification, because it verifies nothing.

## Every file here carries a banner

As of 2026-07-26 all 761 `.v` files begin with a machine-generated comment banner stating
what the file is. Nothing was deleted; the banners are prepended comments only.

## Honest correction: this tree is not uniformly `True`

An earlier, blunter version of this note claimed every theorem in every file here proves
`True`. **That is not accurate**, and stating it would have been a new inaccuracy in place
of the old one. The audit of 2026-07-26 found two populations, and the banners distinguish
them:

| Population | Files | Banner | What it means |
|---|---:|---|---|
| **Pure shape index** | **477** | `=== SHAPE INDEX ONLY — NO MATHEMATICAL CONTENT ===` | Every proof obligation is `True`/`exact I`-class. Zero content. |
| **Mixed** | **284** | `=== LEGACY PARITY TREE — MIXED CONTENT ===` | Mostly `exact I`, but contains at least one obligation closed by a real tactic, or an `Admitted`, or an axiom-like declaration. Per-file counts are printed in each banner. |

The 2,481 obligations closed by real tactics (`lra`, `reflexivity`, `lia`, `nra`,
`vm_compute`, `field`, `rewrite`, induction) are **kernel-checked but unaudited, and
overwhelmingly not the mathematics their names advertise.** In the sampled majority they
are one of:

- **arithmetic over hand-chosen literals** — `(72 : Z) = 72` by `reflexivity`;
  `(1970 : R) < 1977` by `lra`; `(7 + 1 - 8 : Z) = 0`; `(2 : R) = (2)%R`;
- **definitional unfolding** of a framework constant — `alpha_NP - alpha_Hodge = 1/4`
  by `unfold; lra`, where both sides are `Definition`s chosen to make it hold;
- **a conditional reduction** `hypothesis -> claim` where the hypothesis is itself a
  `Definition ... : Prop` encoding the open conjecture. This verifies the *implication*,
  never the claim. `MillenniumSixReductions.v` is the honest archetype: all 52 of its
  obligations use real tactics and it discharges **no** Millennium problem.

A minority are genuine, self-contained mathematics whose statements do match their names —
`IntervalArithmetic.v` (bounds on `sqrt 2`, `sqrt 5`, `PI` via `nra`) is the clearest case,
along with parts of `Analytic/` (`CantorIFS.v`, `TsumHankelAgreement.v`,
`USlitSimplyConnected.v`). These are real but narrow, and several rest on the axiom
stand-ins below. **No `Qed` in this directory should be read as verifying the result its
declaration name suggests without reading the proof.**

## Further defects a reader should know about

- **`Admitted` is present, contrary to the "0 Admitted" claim.** 12 obligations across 5
  files: `Wave16/YangMillsLevelKSpectrum.v` (5), `Wave20/HodgeDim4CY4Substrate.v` (3),
  `Wave15/ConsciousnessRHBridge.v` (2), `Wave15/PerelmanBackward.v` (1),
  `Wave18/NS3DVortexStretchingObstruction.v` (1). `Admitted` still produces a `.vo`, so
  these files *compile* while assuming their conclusions.
- **244 axiom-like declarations** (`Axiom` / `Parameter` / `Hypothesis`) across 37 files —
  most densely `Analytic/HPOperatorConstruction.v` (20), `Analytic/HankelFubini.v` (18),
  `Consciousness/FractalResonance.v` (14), `Analytic/JonquieresZetaSeriesSummable.v` (13),
  `Wave19/NS3DLocalRegularityBKM.v` (13). Where these stand in for missing Coq library
  theory, downstream proofs in those files inherit them as assumptions.
- **The checked-in `.vo` artifacts are stale.** They were built under Coq 8.18
  (`.vo` version `81800`); the installed prover is Rocq 9.1.0 (expects `90100`). The tree
  therefore does not currently rebuild from its committed artifacts without a `make clean`
  and full recompile.

## Why keep the tree at all

It is a genuinely useful index: it pins every Lean declaration name and the file
dependency graph, so a rename or signature change on the Lean side breaks a compile here
and gets noticed. That is a real (if modest) engineering function. It is simply not
verification, and the banners now say so in every file.

## Build

```sh
export PATH="$HOME/.opam/default/bin:$PATH"
cd /home/xluxx/Principia-Fractalis/PF_Coq_Code
coqc -Q PF PrincipiaTractalis PF/<file>.v      # single file
```

See also: `../COQ_REALIZATION_PLAN.md` (what can and cannot be made real, and why) and
`../PF_Real/README.md` (scope of the real proofs).
