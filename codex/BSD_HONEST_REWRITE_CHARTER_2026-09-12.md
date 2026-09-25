# BSD Sector Honest-Rewrite Charter — 2026-09-12

*Charter for Direction B (per `codex/PF_FRACTAL_ARCHITECTURE_2026-09-10.md` §3
Domain-level table) targeting the BSD sector's `rfl`-tautology vacuity.
Follows the survey-then-charter discipline; verifies every agent claim
against source before proposing a Lean module.*

## §1. What the tree currently has (survey verified 2026-09-12)

### The vacuous encoding

`PF/BSD_DirectDischargeAttempt.lean` (lines 157-226) defines:

```lean
structure RankCertificate (E : WeierstrassCurve ℚ) : Type where
  r : ℕ
  rankWitness : True         -- placeholder
  wave57BSD_A3_witness : True  -- placeholder
  wave57BSD_A4_witness : True  -- placeholder

def sigmaAlgebraicRank (p : Σ E, RankCertificate E) : ℕ := p.2.r
def sigmaAnalyticRank  (p : Σ E, RankCertificate E) : ℕ := p.2.r

def StandardBSDEncoding_Sigma : StandardBSDEncoding where
  EllipticCurve := Σ E : WeierstrassCurve ℚ, RankCertificate E
  algebraicRank := sigmaAlgebraicRank
  analyticRank  := sigmaAnalyticRank

theorem clay_BSD_standard_on_sigma :
    Clay_BSD_Standard StandardBSDEncoding_Sigma := by
  intro p; rfl  -- both projections are p.2.r
```

**The vacuity has two independent axes:**
- **Axis 1 — witness fields are `True`.** Both `rankWitness` and the Wave-57 witnesses are typed as `True`; a certificate carries the rank number `r` but no evidence that `r` is any particular rank.
- **Axis 2 — projections are the same field.** Even if Axis 1 is fixed, `sigmaAlgebraicRank p = sigmaAnalyticRank p` reduces to `p.2.r = p.2.r`, which is `rfl` regardless of witness content.

The docstring at line 212 acknowledges the design: *"the content of the discharge lives in the requirement that the user supply a RankCertificate — which is the typed BSD statement on that curve."* This is a bookkeeping wrapper by design.

### What IS honest and load-bearing in the BSD tree

The survey inventory (26 BSD-related Lean files) surfaces genuinely substantive content:

- `PF/BSD_HeegnerRank1Proof.lean:69` — `bsd_rank_one_E37a1_via_heegner_and_GZ_K` (real Heegner rank-1 flag)
- `PF/BSD_HeegnerRank1ProofE43a1.lean:74,360` — rank-1 flag for E_{43.a1}
- Same for E_{61.a1}, E_{79.a1}, E_{131.a1}, E_{141.a1}
- `PF/TransferResidue_r188c.lean:140` — `trace_eq_residues` (kernel-verified transfer-operator trace identity)
- `PF/EllipticTrace_r194.lean:140` — `mestre_nagao_trace` (Mestre-Nagao slope identity, instantiated on `z/p` branches with weights `a_p · p^{-s}`)
- Ch24 `codex/BSD_UNIVERSAL_SECANT_2026-08-05.md` records `rank_ge_universal` — Gram-determinant lower-bound theorem, curve-independent (r193, r195-r203)

The book itself (ch24 lines 680-702) explicitly cites `trace_eq_residues` and `mestre_nagao_trace` as the kernel-verified surviving content after the 2026-07-28/31 φ/e-multiplicity mechanism falsification.

### What is missing from mathlib

Mathlib has `WeierstrassCurve ℚ` and the group law but **no `WeierstrassCurve.rank : WeierstrassCurve ℚ → ℕ`** and no `analyticRank`. There is no upstream to bind to.

## §2. What the book chapter 24 says (verified read 2026-09-12)

Ch24 has EXPLICITLY retracted the operator-multiplicity mechanism (§ "Verification status 2026-07-23" and § "Verification update 2026-08-04"):

- "**The Birch-Swinnerton-Dyer conjecture is NOT proven here and remains open**; the chapter presents computational evidence, and its central rank formula is stated as a conjecture."
- The φ/e-multiplicity mechanism was falsified by 2026-07-28/31 (see `codex/CH24_OPERATOR_QUASINILPOTENT_2026-07-30.md`, `CH24_OPERATOR_ILLPOSED_2026-07-30.md`, `CH24_SPECTRAL_DIAGNOSIS_2026-07-31.md`).
- **The surviving trace-level signal** is the Mestre-Nagao sum `Σ_{p<X} a_p/p ~ -rank · log log X`.
- The r188c trace identity (`trace_eq_residues`) and its r194 elliptic instantiation (`mestre_nagao_trace`) are cited as kernel-verified.
- "Honest scope: the identity is proved generically, under stated geometry/holomorphy/factorization hypotheses; ... **nothing here claims BSD, in whole or in part, is proven.**"

**Conclusion: the book's ch24 has already made its honest-scope decision.** The Lean tree's `BSD_DirectDischargeAttempt.lean` Σ-encoding predates that decision and hasn't been rewritten to match.

## §3. What an honest rewrite targets

**Not a proof of BSD.** BSD is out of reach for any prover.

**Not a replacement of the load-bearing substrate content.** Heegner rank-1 flags, `mestre_nagao_trace`, `rank_ge_universal` — these are honest and stay.

**The specific rewrite target** is `BSD_DirectDischargeAttempt.lean`'s Σ-encoding, plus a companion honest-scope encoding that carries SEPARATE algebraic-rank and analytic-rank witnesses matching the book's post-falsification scope.

### Campaign BSD-Bounded — a new honest-scope encoding

**Target file:** new `PF/BSD_BoundedEncodingHonest.lean` (name pending survey verification of no conflict). Keeps the existing `BSD_DirectDischargeAttempt.lean` intact as a historical artifact with a docstring pointer to the new file.

**Contents:**

1. **`RankLowerBoundWitness` — a REAL witness structure** replacing `RankCertificate`:

   ```lean
   structure RankLowerBoundWitness (E : WeierstrassCurve ℚ) : Type where
     /-- The claimed algebraic-rank lower bound. -/
     r_alg_lb : ℕ
     /-- The claimed analytic-rank lower bound. -/
     r_an_lb  : ℕ
     /-- Evidence for the algebraic lower bound: either a Heegner
         rank-1 flag, or a Gram-determinant-based `rank_ge_universal`
         instance, or (for r_alg_lb = 0) trivial. -/
     alg_evidence : AlgebraicRankLowerBoundEvidence E r_alg_lb
     /-- Evidence for the analytic lower bound: currently only the
         `mestre_nagao_trace` slope reading is available (empirical),
         or (for r_an_lb = 0) trivial. Placeholder Prop until analytic
         rank machinery matures. -/
     an_evidence : AnalyticRankLowerBoundEvidence E r_an_lb
   ```

   `AlgebraicRankLowerBoundEvidence` and `AnalyticRankLowerBoundEvidence` are
   inductive types with constructors for the specific existing sources of
   evidence (Heegner, Gram-determinant, trivial for rank 0).

2. **`StandardBSDEncoding_Bounded : StandardBSDEncoding`** where the curve
   type is `Σ E, RankLowerBoundWitness E`, and the two rank projections
   read the SEPARATE fields `r_alg_lb` and `r_an_lb`. Crucially,
   `algebraicRank ≠ analyticRank` in general — they are two independent
   witnesses.

3. **The honest Clay Prop:**

   ```lean
   /-- The Clay BSD statement in the bounded-encoding presentation.
       For each certified curve, the algebraic-rank lower bound equals
       the analytic-rank lower bound. This is NOT `rfl` — it requires
       real content on the witness side. -/
   def BSD_Bounded_Statement : Prop :=
     ∀ p : Σ E : WeierstrassCurve ℚ, RankLowerBoundWitness E,
       p.2.r_alg_lb = p.2.r_an_lb
   ```

4. **Population of the encoding** — instantiate `RankLowerBoundWitness`
   for the curves for which BOTH witnesses can be honestly assembled:
   - `E_{37.a1}`: `r_alg_lb = 1` (Heegner via `bsd_rank_one_E37a1_via_heegner_and_GZ_K`), `r_an_lb = ?`
   - The `?` for `r_an_lb` is the honest gap: there is NO kernel-verified
     analytic-rank lower bound in the tree. Even for E_{37.a1}, the
     Mestre-Nagao slope is a measurement, not a bound.

5. **Explicit gap-marker theorem:**

   ```lean
   /-- HONEST GAP: the bounded encoding requires analytic-rank witnesses
       that are NOT currently in the tree. `mestre_nagao_trace` gives an
       empirical slope, not a rigorous lower bound. Populating the
       encoding requires either an analytic-rank machinery (which no
       proof assistant has) or an honest-scope Prop labelled "empirical". -/
   theorem BSD_Bounded_analytic_witness_gap :
     ∀ E : WeierstrassCurve ℚ, ¬ ∃ evidence, HasKernelVerifiedAnalyticLowerBound E evidence :=
     ...  -- specification only; body is a proof from the currently-empty state
   ```

### What the rewrite DOES NOT do

- **Does not remove** `BSD_DirectDischargeAttempt.lean` or the Σ-encoding.
  That file remains, with a top-of-file banner pointing to the honest
  encoding.
- **Does not touch** the Heegner rank-1 files, Mestre-Nagao trace file,
  or transfer-residue file — those are honest.
- **Does not touch** the appI cross-reference (a separate correction step;
  see §5).
- **Does not attempt to prove BSD** or any of its sub-claims.

## §4. Scope estimate

- New file `PF/BSD_BoundedEncodingHonest.lean`: ~150-200 lines including
  documentation and the explicit-gap theorem.
- Modifications to `PF/BSD_DirectDischargeAttempt.lean`: banner comment
  at file top pointing to the new file, ~10 lines.
- Kernel audit: all declarations must audit to
  `[propext, Classical.choice, Quot.sound]`. In-file `#print axioms`
  block at file end per `build-tree-discipline`.
- Import into `PF.lean` under a G5-appropriate section.

**Ceiling: 1 session.** If the honest witness constructors can't be
assembled in that budget, drop to a "specification-only" module: the
`RankLowerBoundWitness` structure + Prop statements without any
populated instances, still land-worthy as it establishes the honest
scope for downstream work.

## §5. Follow-on documentation actions (not part of the Lean campaign)

After the Lean file lands:

- **AppI cross-reference amendment.** The BSD V2 row currently cites
  `StandardBSDEncoding_Sigma` as the substantive discharge. This should
  be corrected to say: "V2 Σ-encoding is a bookkeeping wrapper on a
  user-supplied `RankCertificate`; the honest substrate-level content is
  in `PF/BSD_HeegnerRank1Proof.lean` (Heegner rank-1 flags),
  `PF/EllipticTrace_r194.lean` (Mestre-Nagao trace), and the new
  `PF/BSD_BoundedEncodingHonest.lean` (bounded encoding with explicit
  analytic-witness gap)."

- **Codex cross-reference.** Add a one-line entry in
  `codex/PF_FRACTAL_ARCHITECTURE_2026-09-10.md` §3 sector table for BSD
  updating "vacuous (algebraicRankV5 = analyticRankV5 = manuscriptRankV5
  ; equality by `rfl`); encoding is the identity function" to reflect
  the new bounded-encoding companion.

## §6. Risks and stopping conditions

**Risk 1 — the honest gap is bigger than one file.** If populating even
`E_{37.a1}` in the bounded encoding requires more analytic-rank work
than the session budget supports, the ceiling drops to
"specification-only": land the structure and statements, do not populate.

**Risk 2 — naming conflict with existing files.** Before creation,
verify no file `PF/BSD_BoundedEncodingHonest.lean` exists and no
name collisions with `RankLowerBoundWitness`,
`StandardBSDEncoding_Bounded`, `BSD_Bounded_Statement`,
`AlgebraicRankLowerBoundEvidence`, `AnalyticRankLowerBoundEvidence`.

**Risk 3 — the specification-only version turns out to be trivial.**
If the honest bounded encoding, without populated instances, is just
"here's a structure that could carry witnesses if they existed," verify
that it's non-vacuously distinct from what `RankCertificate` already
provides. The key distinction is the TWO separate rank fields
(`r_alg_lb ≠ r_an_lb` allowed), which is not present in `RankCertificate`.

**Stopping condition — pre-commit gate.** Any declaration that fails to
audit to `[propext, Classical.choice, Quot.sound]` blocks the commit.
Any use of `sorry`, `axiom`, or `native_decide` blocks the commit.

## §7. Standing discipline

- Book-guides-Lean: the rewrite matches ch24's post-2026-07-31 honest
  scope. The book has retracted the multiplicity mechanism and cites
  the trace identity as the surviving substrate; the rewrite mirrors
  this at the encoding layer.
- No speculation: `AnalyticRankLowerBoundEvidence` has only trivial
  constructors until a genuine analytic-rank witness lands; the
  `BSD_Bounded_analytic_witness_gap` theorem makes the gap explicit
  and machine-checked.
- Survey-then-charter: this charter is committed BEFORE any Lean code is
  written for the campaign. §4's scope is a ceiling, not a plan; if the
  session runs into unexpected obstacles the ceiling drops per §6.

*Charter opened 2026-09-12 after book-verified survey. Execution to
follow, with a §10-format progress report per commit.*
