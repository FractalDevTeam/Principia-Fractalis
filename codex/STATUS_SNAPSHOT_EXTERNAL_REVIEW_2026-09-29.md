# Principia Fractalis — status snapshot for external review

**Date:** 2026-09-29
**Author:** Pablo Cohen (psolo / xluxx) with Claude Opus 5 (1M context)
**HEAD (master, Acer ACTIVE tree):** `0d8ea1a4` — 21 commits ahead of `origin/master`, not pushed
*(verified 2026-09-28 on `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE`)*

> **Verification convention used below.** "Kernel-verified" means an `.olean` produced by the
> Lean kernel is present in the ACTIVE tree *now*. A commit hash alone is provenance, not
> current verification. Claims verified earlier whose artifacts are not presently on disk are
> marked **RE-VERIFICATION PENDING**.

## Machine-verified 2026-09-27

- `lake build` EXIT=0, 3216 jobs, on the four r333–r336 substrate-collapse modules + r337 PremiseAudit.
- 27 principal theorems across r333/r334/r336 print exactly `[propext, Classical.choice, Quot.sound]`
  under `#print axioms`. Zero project axioms.
- Consequence: ch04 Thm 4.18 is REPAIRED, not withdrawn. Corrected reading
  M⁴ = Aut(𝒯_∞)/Inn(𝒯_∞) = Out(𝒯_∞), with Inn(𝒯_∞) machine-verified nontrivial
  (r334 witness = conjugation by 1 + E_01 at substrate level 1).

*Not independently re-checked in the 2026-09-28/29 session; carried forward as recorded.*

## Kernel-verified pillars (post-r315, standing)

1. **T_infinity_rigidity** (r217, `18f55a14`, 2026-09-11) — first machine-verified Glimm-1960 UHF
   classification for supernatural 3^∞ in any proof assistant. Verified absent from mathlib4,
   Isabelle/HOL, Coq/Rocq, Agda, Lean 3. Fills six mathlib gaps as byproducts.
2. **K-theoretic obstruction** (r123 + r332) — seven of nine α-values and the ratio α_NS / α_RH = π
   lie outside ℤ[1/3], hence outside the substrate's classifying invariant range. Substrate is
   unique up to ⋆-iso AND provably underdetermines the α-skeleton.
3. **Xi_Positive_At_15** (r315, `4f7b216d`, 2026-08-23) — unconditional; two independent formal
   architectures (r313–r314e via theta truncation + certified |R_{≥2}| < 1/10⁶; r315 direct via
   r120 panel-generator specialization). r324 (`8e7bb46f`) excludes any critical-line riemannZeta
   zero below height 15.
4. **Brun B1 + Mertens M1–M5** (2026-09-23 → 25) — twin-prime BoundingSieve on mathlib's
   SelbergSieve, plus Chebyshev upper/lower, Abel summation, log-over-p bounds, Bertrand's postulate.
5. **Two-anchor α-cascade** (2026-09-25) — nine α-values doubly-anchored by Perelman 2003
   (α_Poincaré = 1) + the 2026 Navier–Stokes/Euler chain: Córdoba–Martínez-Zoroa →
   Buckmaster–Alpöge (Lean-verified Euler blow-up, 2026-08-22) → OpenAI-formalized
   (openai/NavierStokesAndEuler, 2026-09-08, Apache-2.0). Clay has NOT accepted the NS result and
   OpenAI declined the prize; it corroborates rather than closes.

*(The ξ-rectangle edge work previously listed here as item 4 has been moved to its own section
below — its artifacts are not currently present. See immediately following.)*

## ξ-rectangle edges — RE-VERIFICATION PENDING

**Moved out of the "standing" list above. Do not cite as current kernel-verification.**

Source-complete and previously verified: top edge r331c (`34dd98db`, 2026-09-22),
Re ξ⟨σ,15⟩ < -1/10⁴ on σ ∈ [0,1]; bottom edge on [0,1] at t = 0 at r329b; right edge at r331b.

Artifact state in the ACTIVE tree, measured 2026-09-29:

| Item | State |
|---|---|
| `RiemannXiTopEdge_r331c.olean` | **absent** |
| `RiemannXiEdgeEnclosure_r331c.olean` | present, dated Sep 8 — **older than its Sep 25 source** |
| `RiemannXiBox0Panels` | 228 / 239 rebuilt |
| `RiemannXiBox100Panels` | 185 / 228 rebuilt |
| `RiemannXiBox2Panels` | **0 / 228** |

The cause is mechanical, not mathematical: the tree's source mtimes postdate its oleans, so Lake is
regenerating the panel corpus. A capped rebuild is in progress on the Acer — **253 panels rebuilt,
zero failures** — with roughly 282 heavy panels remaining (~22 h at the measured rate).

Promote this section back to "standing" only when `RiemannXiTopEdge_r331c.olean` exists and the
three panel groups read 239/239, 228/228, 228/228.

## Mechanical corpus audit (2026-09-18, `PF/Audit/PremiseAudit.lean`)

- 213 corpus capstones audited. 99 CLEAN, 114 with findings.
- T_infinity_rigidity audits CLEAN post-r337.
- r301 universal Millennium capstone assumes RH by four routes — two literal (RH-as-conjunct in
  `riemann1859_original_conjecture` and `bombieri2000_clay_official`), two by one-step modus ponens.
  Theorem is valid; carries no RH information.
- `MinimalRigidityForces*` family: 35 / 35 with findings, 0 clean. Minimal-rigidity hypotheses are
  DEAD in every proof.
- α-skeleton identities in `cross_millennium_shared_invariants_substrate_capstone` are assumed,
  not forced.
- Perelman "anchor" is a hypothesis — no property of Perelman's theorem is used.
- The distinction between the kernel-clean substrate tier and the Referee-tier "rigidity forces X"
  family is now mechanical, not editorial.

## Book state (v2.7.0, 2026-09-27)

38 chapters, ~913 pp. Full `title.tex` + `version_history.tex` refresh logging the three-month arc
2026-06-23 → 2026-09-27. Preface + ch04 REPAIR block + ch34A anchor attribution
(Córdoba–Martínez-Zoroa / Buckmaster–Alpöge / OpenAI-formalized) + ch22 §614
external-corroboration section corrected. Banned phrase "scoping" swept book-wide
(16 files, 4 LaTeX labels renamed, zero residual). PDF not yet rebuilt.

## Grand dependency graph audit (2026-09-27 refresh)

`codex/GRAND_PROBLEM_DEPENDENCY_GRAPH_2026-09-27.md`. 14 tracks re-ranked. Rank-1 next attack:
r331d bottom edge + r327 argument-principle threading → `riemannHypothesis_below_15`.
Substrate-tier, low circularity risk, ~95% infrastructure already committed.

## Competitive landscape (external, verified via web search 2026-09-27)

- **OpenAI ten-proofs (Astra, 2026)** — Lean 4.32.0, Apache-2.0, zero-sorry. Ten open problems:
  sphere packing (Cohn–Elkies), binary/spherical codes, non-sofic groups constructed (Gromov 1999),
  Connes rigidity for group von Neumann algebras DISPROVED, arithmetic circuit complexity, quantum
  parallel repetition, GapCVP, Ehrhart volume, multicolor Ramsey (Erdős 183), extremal graph theory
  (Erdős 146, 180 disproved). The Connes rigidity disproof is a direct C\*-neighbor of PF's
  T_infinity_rigidity and sharpens the significance of PF's positive result — general
  operator-algebra rigidity fails, PF's specific 3^∞ UHF rigidity does not.
- **Anthropic** — Fermat's Last Theorem formalized (13M lines Lean, 11 days); unreleased Claude made
  RH progress via 60 agentic sub-Claudes; Jacobian conjecture disproved; Vinogradov's Three Primes
  Theorem (Prove2Me, 3 days). Anthropic Science Lab now offering grants + credits to external
  mathematicians.

## r331d status (in flight)

**Source complete, kernel verification pending.** 112 lines, five declarations:
`neg15_eq_conj_15`, `re_conj_at_neg_15`, `bottom_edge_re_neg_full`, `bottom_edge_neg_xi_re_pos`,
`bottom_edge_ne_zero`. Imports `PF.Analytic.RiemannXiTopEdge_r331c` and
`PF.Analytic.RiemannXiSymmetries_r326`.

Math is trivial: ⟨σ, -15⟩ = conj ⟨σ, 15⟩, so Re ξ⟨σ, -15⟩ = Re ξ⟨σ, 15⟩ via r326's
`riemannXiEntire_conj`; r331c gives the RHS < -1/10⁴.

**Why it has not sealed.** Not ambient memory pressure, and not a laptop. Three *concurrent
duplicate* `lake build` invocations of the same target were running on the Acer, each fanning out
to `nproc` = 12 workers on a 15 Gi box, because Lake 5.0.0-src+919e297 exposes **no `-j` flag**.
They OOM-killed one another (exit 137) for roughly a day. Corrected by capping concurrency with CPU
affinity — `taskset -c 0,1`, then `-c 0` for the heavier `Box100` / `Box2` tier. Since the cap:
253 panels rebuilt, **zero OOMs**.

**Compute in use.**

| Host | Arch | Role | Oleans | Heavy panels left |
|---|---|---|---|---|
| Acer `192.168.0.94` | x86_64, 12c / 15 Gi | primary | 6,342 | 282 |
| Xavier `192.168.0.102` | aarch64, 8c / 14 Gi | redundant insurance | 566 | 621 |

Both build the identical revision (r331d 4177 B, r331c 3928 B on each host). Xavier is far behind
and is not expected to finish first; it is left running as a failover copy, not a speedup.

*Correction to the prior snapshot:* the earlier claim that Xavier provisioning "hit an ext4 unmount
corruption that lost the source" is not supported by any record found in the session transcripts or
on the hosts. Xavier is provisioned, carries the same Lean toolchain
(`leanprover--lean4---v4.24.0-rc1`), and holds the r331d source intact.

No mathematical or design ambiguity blocks the seal — only panel rebuild time.

## Publication stance (Pabs's directive)

The book (with its Lean companion code) is the submission when a submission occurs. Not slice
papers. Publication either (a) upon crown novel discovery of world-relevance urgency, or (b) upon
completion of research. Nothing published externally without Pabs running multi-model stress-test
vetting first.

---

*Every claim above is either kernel-verified with a present artifact, carried forward from a dated
prior verification and labelled as such, explicitly marked RE-VERIFICATION PENDING, or labelled
external / in-flight.*
