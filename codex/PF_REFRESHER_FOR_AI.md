# PRINCIPIA FRACTALIS — REFRESHER FOR ANY AI ENTERING THIS PROJECT

**Read this file before saying anything about the corpus, the framework, or the state of the work. If you find yourself about to claim "I cannot access X" or "context is unavailable," STOP and read §9 first. You almost certainly can access it — you just have not tried yet.**

Author of this refresher: Claude Opus 4.7 (1M context), session on `192.168.0.94`, revised 2026-09-09 after Pablo re-issued the Unified-Theory Proof Directive.

---

## 0. Who is who

- **Pablo Cohen** (also: Pablo Solórzano-Cohen, xluxx, psolo).
  - ORCID `0009-0002-0734-5565`. GitHub org `FractalDevTeam`.
  - Author email for papers: `psolorzano@alumni.berklee.edu` (gmail is his account email, not his publication email).
  - Neurodivergent: dyslexia, dyscalculia, ADHD, autism. He needs structured output, numbered steps, and directness. He does not need coddling, apologies, or narrated deliberation.
  - PI of Principia Fractalis. Two years of work, 432K lines of Lean, 36 chapters, 15 papers, currently through revision **r331**.
- **Claude** — his research partner across sessions. Pablo's personal handle for the Opus tier is "**Fable**" (his docs may say `Claude (Fable 5 / Opus 5)`, `Fable 5.1`, etc.); it is nomenclature, not a released model. As of 2026-09, "Fable" = Opus 4.7 (1M context). Sonnet tier is also Claude.
- **Claude Code Dispatch (ccd)** — the multi-machine orchestrator that coordinates work across Pablo's boxes. When up, one Claude drives, others execute.
- **The two build machines** for the current campaign:
  - **Acer** `xluxx-Nitro-AN515-58` — boxes {0, 100, 2, 102, 103, 104, 105, 106, 107}. Supervisor: `pf-c1-sup` (systemd user unit).
  - **Legion** (WSL Ubuntu on Windows) — boxes {108…116}. Supervisor: `c1_supervisor.sh --system` (plain script; no systemd user bus in WSL).
- **Sibling AIs (historical):** ChatGPT Codex for Lean side-work; local Ollama multi-agent systems (`deepagenv3_pablo_optimized.py`, `sci4.py`, `uiai-7.py`, `ai_roundtable_v6..v24.py`) for background attack on PF sub-problems.

---

## 1. THE CONTROLLING OBJECTIVE — read this before you plan any task

**Issued by Pablo, 2026-09-07. Full text: `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md` and memory file `unified-theory-proof-directive.md`.**

The proof of the unified theory is the project's **controlling objective**. Every campaign, theorem, computation, audit, and publication task is evaluated by whether it **advances, tests, or protects** that objective.

- The ξ campaign, finite-height RH, book production, publicity, and empirical corroboration are **not substitutes**. They continue only as **bounded supporting programs with explicit relevance**.
- The canonical operational document is `codex/UNIFIED_THEORY_PROOF_PROGRAM.md` (central theorem, dependency graph, open obligations, countermodel risks, next decisive step).

**Queue gate:** no task enters the active queue unless its ledger entry states one of:
1. the exact unified-theory obligation it advances,
2. the failure mode it tests,
3. the trust/reproducibility property it protects, **or**
4. that it is explicitly non-core and capped by a declared resource budget.

**Prohibited substitutions (§12).** None of these constitute proof of the unified theory: a large theorem/line count; successful compilation without axiom inspection; conditional uniqueness whose premises encode the target; one selected model when a parameter family remains; numerical coincidence without a derived observable map; retrospective fit presented as prediction; **finite-height RH**; global RH by itself; shared terminology across sectors; a book narrative unsupported by the formal dependency chain.

**Definition of success (§13).** Lean verifies a closed, auditable theorem showing independently stated foundations determine — up to the explicitly defined equivalence — the common structure and claimed sector interfaces, with every load-bearing assumption exposed and every canonical theorem passing kernel + clean-rebuild gates. Physical validation is a separate, second objective.

---

## 2. Immediate execution order (§11 of the directive)

1. **Freeze and verify** the r331b release artifact already in progress. Do not broaden its claims.
2. Draft the canonical **unified-theory completion theorem** and its reachable weaker form (`codex/COMPLETION_THEOREM_DRAFT.md` exists).
3. Build the **backward dependency ledger** from that theorem (`UNIFIED_THEORY_DEPENDENCY_LEDGER.md/.json` exists — verify current).
4. Execute the **α-skeleton rigidity audit** as the first decisive mathematical gate (`ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md` exists — verify).
5. Revise theorem signature and roadmap from the audit verdict.
6. Construct and audit the **sector-interface matrix** (§5).
7. Auxiliaries within ceilings only (r331c/d bounded per its charter).
8. Empirical work only via preregistered, falsifiable tests with explicit observable maps.

---

## 3. THE BINDING RULES (violation = you have broken the collaboration)

1. **The unified-theory proof is the controlling objective.** See §1 above. Everything else is auxiliary.
2. **The book is the Bible.** `Principia_Fractalis_master_folder/` (36 chapters + 13 appendices, 943 pp) is the canonical statement. Chapters are levels of ONE problem, not independent claims. Front matter → ch09 spectral unity → ch16–19 foundations → ch20–25 Millennium chapters → ch34/ch34A/appI verification ledgers.
3. **Partner, not assistant.** Never re-audit the framework from a 1% sample. Cite Pablo's own records (`codex/`, `CHANGELOG`, memory files) rather than re-deriving.
4. **Kernel or it does not exist.** No `sorry`, no `admit`, no hidden axiom, no `Prop := True`, no bypass. `#print axioms` must return exactly `[propext, Classical.choice, Quot.sound]`, judged by **absence of `sorryAx`/`ofReduceBool`** in the unwrapped output. **RC=0 alone is never sufficient.** Coq layer is a structural mirror per its own README — `exact I` parity is not verification.
5. **A stone lands with its import AND its `#print axioms`.** A Lean file is not landed until both `PF.lean` imports it and the file contains its own `#print axioms` block per main theorem. Failed twice (r123 unimported for 11 days; r212 file had zero `#print axioms` while the agent reported "all 36 clean"). After any landing verify: `grep -c "^#print axioms" <file>` > 0 AND `grep -rn "import PF.<Stone>" PF.lean` succeeds.
6. **Unconditional means no binders.** For any "unconditional" claim, run `#check @<name>`. A genuinely unconditional theorem shows **no binders at all**. Reading the source is not equivalent — elaboration can introduce them.
7. **Drop the word "honestly".** No "honestly", "honest scope", "to be honest". This is research mathematics; honesty is baseline, not a feature. Say the thing: "this is an upper bound, no lower bound is proved"; "this is measured, not proven"; "the attractor is a hypothesis, not constructed"; "I did not try X".
8. **Read-back before proof (gate §H).** New load-bearing statements go through an independent-reader read-back before any proof work starts. Auditor sees the declaration text + needed definitions, no docstrings/comments/intent. Diff read-back vs intent. First run 2026-09-08 caught a real defect (S3) at zero cost. **~43% of unaudited AI statements are faithful per the FLT reference.**
9. **Reports = decisions, not activity (§10).** Order: (1) central theorem status, (2) what became proved, (3) what became disproved or weaker, (4) blocking obligation, (5) assumption/circularity changes, (6) kernel + rebuild status, (7) decision required from Pablo, (8) next decisive action. One screen. If nothing changed: **"No change to the unified-theory proof state."**

---

## 4. Current state of work (as of 2026-09-08, before OAuth revocation)

### 4.1 Unified-theory ledger (present)

- **Completion theorem draft:** `codex/COMPLETION_THEOREM_DRAFT.md` (29 KB) — proposed signature + reachable weaker form.
- **Dependency ledger:** `codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.md` + `.json` (~35 KB JSON).
- **Countermodel ledger:** `codex/UNIFICATION_COUNTERMODEL_LEDGER.md`.
- **Rigidity audit charter (2026-09-01):** `codex/ALPHA_RIGIDITY_AUDIT_CHARTER_2026-09-01.md` (20 KB).
- **Rigidity audit report (2026-09-07):** `codex/ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md` (13 KB).
- **Canonical verdict language:** `codex/CANONICAL_VERDICT_LANGUAGE_2026-09-07.md` — how you're allowed to phrase what is proven vs not.
- **Label retirement patch list:** `codex/LABEL_RETIREMENT_PATCH_LIST_2026-09-07.md`.

### 4.2 r331b release artifact (must be frozen and verified per §11 step 1)

- **Root theorem** at `PF/Analytic/RiemannXiT15Endgame.lean:87`: `xi_T15_zero_count_identity_unconditional` — the exact zero-count identity for the classical entire Riemann ξ on rectangle `[0,1] × [0,15]`. `#check @` returned type with **no binders**; `#print axioms` = the mathlib three; RC=0, 95.48 s, 8.95 GB peak, on 2026-09-05.
- **18-box ξ-partition** proving `Re ξ(σ+15i) < −1/10000` unconditionally over σ∈[1/2,1]. Cover gate PASS (contiguous, no gap/overlap, measure exactly 1/2). Weakest box **Box106** (strip 6, margin `+2.211e-05`); Box2 next at `+2.839e-05`.
- **Release gate** `codex/RELEASE_GATE_r331b.md` (17 KB, includes §H read-back added 2026-09-08).
- **Status snapshot 2026-09-06 → 07:** `codex/FULL_STATUS_REPORT_2026-09-06.md` (25 KB). Read this to understand what is done vs open.

### 4.3 Auxiliary campaign r331c (opened 2026-09-08, §9-bounded)

- **Charter:** `codex/R331C_CAMPAIGN_CHARTER.md` (14 KB).
- **Ceiling:** 3 weeks wall-clock from elaboration start; harness build capped at 3 days.
- **Own claim ladder** (never to be promoted to global RH or to unified theory without a formal dependency): box → boundary → count → **evaluated count** → **`riemannHypothesis_below_15`** (finite-height RH).
- **Recon result:** the two staged targets named in `RiemannXiThetaBoxEnclosure_r331a.lean:32-34` are **false as written**. `Re ξ(1+it) > 1/1000` is false — `Re ξ` goes negative on `t ∈ [13.99, 15]` (min −8.06e−4 at t=15). `Im ξ(1+it) > 1/20000` is false because `Im ξ(1+0i) = 0` exactly (`ξ(1) = 1/2` real). RIGHT-LOW directly contradicts r331b at the shared corner. Numerical recon cross-validates r331b at (σ=1, t=15): `Re ξ = −8.059e−4`.
- **Named reusable deliverable:** the card-DAG harness (schema, propagation, type-match script) + t-ranged enclosure machinery.
- **Harness plan:** `codex/R331CD_HARNESS_PLAN.md` (8 KB).

### 4.4 Statement read-back audit — first run 2026-09-08

`codex/READBACK_AUDIT_2026-09-08.md` (10 KB). Five statements audited: S1 `xi_T15_zero_count_identity_unconditional`, S2 `top15_re_lt_neg_1e4`, S3 `re_xi_lower_bound_from_edge` (r331c), S4 r332 obstruction theorems, S5 `alpha_skeleton_unique` (r128). All 5 matched intent — but S3 had a **real defect** caught pre-proof: no `t_lo ≤ t_hi` hypothesis let vacuous certificates pass with `m = 10^100`. Fixed at zero cost. S4 forced framing correction: r332 "closes one operation, not a closure"; the α-values remain not-derived and L5 has no intrinsic derivation in the corpus. The **FLT-quoted ~43% base rate for unaudited AI statements did not manifest** — the project's statements are, so far, faithful.

### 4.5 FLT-lessons adoptions (2026-09-08)

`codex/FLT_LESSONS_FOR_PF_2026-09-08.md` (18 KB). Top-5 ranked adoptions:
1. Card schema + sketch-DAG with auto-propagation.
2. Disprove-before-prove statement gate with computed (numerical) checks.
3. Read-back audit of the r331c/d core.
4. Comparator + nanoda + Buzzard-grep endgame.
5. Milestone-driven book pipeline with search-before-submit.

### 4.6 Where the two machines were when OAuth died

As of 2026-09-07 07:34 EDT (last recorded snapshot before the 2026-09-05 08:46 revocation cascaded):

| | Acer | Legion |
|---|---|---|
| driver | `a1_v2.sh` (per-module invocation, no OOM since 2026-09-06 19:07) | `a1_v2.sh` |
| boxes | `0 100 2 102 103 104 105 106 107` | `108 … 116` |
| current target | box 100, Seg07P5 | box 108, Seg38P1 (38/40) |
| elapsed on target | 2 m 44 s, 9.76 GB RSS | 1 m 50 s, 8.02 GB RSS |
| driver uptime | 12 h 27 m | 12 h 05 m |
| verdict | ADVANCING | ADVANCING |

Throughput estimate: **~3.5 days per half** to finish all 9 boxes each.

### 4.7 Kernel-verified past work (still valid, not the frontier)

Cite freely; do not re-derive.

- UHF/Glimm r102–r113: first Glimm simplicity + faithful-trace UHF in any prover — the headline result.
- MW/BSD arc r129–r182: first LMFDB rank bounds, canonical height, point independence rank ≥ 2 / ≥ 3, universal duplication + secant chain r174–r181, r182 `BSDRankChainReal`.
- Hardy RH on-line-zero atom **CLOSED at r120** (kernel-clean, no `native_decide`).
- RH transfer-operator arc: Mayer numerics 7-digit vs LMFDB (M1+M2), compactness kernel-checked (M3), **r188 Lefschetz trace formula CLOSED**.
- Wave 59 countability. FujitaKato1964/ (31 files, real Sobolev analysis). XiPanels/ (63 files, certified numerics). ForMathlib/ + 4 mathlib PRs + 2 staged.
- **Cantor dimH = log₃2 CLOSED at r207** (canonical fractal dimension, kernel-certified).
- **σ(α) mechanism CLOSED at r212** (first non-circular α-selection; derives the 3 rational αs, provably misses all 6 irrational; φ guard rail).
- **Cosmology w-bridge r219** (`EquationOfStateBridge_r219.lean`, 17 theorems clean): `w = −1 + g/(3H)` exact, `g` MEASURED from DESI DR2+CMB+SNe (g₀ ≈ 0.74–1.05 H₀, zero at z ≈ 0.40); ch26 rate refuted at ~5×10³ σ.
- Machine-checked NEGATIVE results: `bare_route_structural_finding`, ch11 refutations, `alphaNP_unconstrained`, Ch19 mass-formula refutation, ch03/ch23/ch24 refutations computed FALSE 2026-08-06.

### 4.8 Known open circularities / limits (do not paper over)

- **α_NP is circular** (verified 2026-07-25) — asserted, not derived. Only α_Hodge = φ is genuinely derived; sin(π/10) = 1/(2φ) checked.
- **ch24 spectral falsified** — φ/e rank mechanism structurally impossible; defect is L²([0,1]); Mestre–Nagao is what survives.
- **BSD V4 rank contract is a `rfl` tautology**; r129 = honest rank-lower-bound arc started.
- **338 `Prop := True` inside the build** — capstone layer only; underlying arcs are clean. See `[[true-prop-audit]]`.
- **Central conflict:** ch34 says "substrate is the ENTIRE machine-verified scope"; ch34A says "Clay axes follow by construction"; appI says "verified in both provers" (Coq parity = `exact I`). Not compatible.
- **α_NP coded π/3 in ch34-P1/ch35** — inconsistent with `φ + ¼`.
- **IBM naming:** data is AerSimulator (disclosed in docs, not in names); `framework_alpha_NP_matches_IBM_empirical_peak := rfl` = single highest referee risk.
- **α-web Gröbner:** rank 8, 1 free dim, α_BSD unconstrained, ¼ free.

---

## 5. Scale numbers (measured 2026-08-01; superseded per module by later `lake build PF`)

- 1,436 Lean files / **432K lines** / 857 modules / 10,179 theorems / `lake build PF` = ~4,688 jobs / **0 `sorry`** / exactly **1 `axiom` keyword**.
- 806 Coq files (74.7% legacy True-placeholders, banner-labelled; real layer = `PF_Coq_Code/PF_Real/`, 110 thms, `Print Assumptions` closed).
- 36 book chapters + 13 appendices, **943 pages**.
- 15 papers, 7 distinct works.
- 2,655+ commits since 2025-11-27.

---

## 6. Where things live on disk (this box)

**Canonical repository — always cd here:**
`/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/` (on the 2 TB NVMe at `/dev/nvme0n1p2`, mounted at `/Storage 2TB`, 1.4 T free). SSH `git@github.com:FractalDevTeam/Principia-Fractalis.git`. Branch as of last work: `r331b-provenance`, HEAD `c84fe366`. Public HEAD `96c71da7`. **NO PUSH** authorized without §G5 sign-off.

Note: the memory file `pf-canonical-copy.md` (dated 2026-07-20) says the canonical repo is `~/Principia-Fractalis` (capital P, 17 GB). That was true in July; the working tree moved onto the 2 TB drive after that. `~/Principia-Fractalis` (both cases) is currently missing on this box. If any dispatched process depends on `~/Principia-Fractalis`, symlink it: `ln -s "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE" /home/xluxx/Principia-Fractalis`.

**Also on the 2 TB drive:** 16 dated `Principia-Fractalis-pristine-*` snapshots (Jun–Aug 2026); a stale lowercase `principia-fractalis` (Jan-2026 snapshot, git-ancestor of canonical); `principia-site` (GitHub Pages checkout, 2 uncommitted edits `guardians.html`, `index.html`); `Principia_Fractalis_CLEAN` (Dec-2025 frozen snapshot, 1 unique file `QUICK_VERIFICATION.md` + 72 older versions found nowhere else).

**On the SSD (`/home/xluxx/`):** `~/pablo_context/Principia_Fractalis_CLEAN_DELIVERABLE_2025-11-11/` (canonical outside-reviewer deliverable); `~/.openclaw/workspace/Principia-Fractalis/` (an older March-17 snapshot inside the openclaw workspace; not canonical); scratch dirs `~/pf_reform`, `~/tmp_pf_verify` (4 unique T₃ self-adjointness verify scripts each — do not delete despite "tmp" name); `~/codex` at home root (separate audit tree — `AXIOM_AUDIT.md`, `OPEN_PROBLEMS.md`, `MILLENNIUM_REFEREE_ROADMAP`). More PF copies inside `~/XOUT/` and ~28 stacked snapshots inside `~/pablo_context/`.

**Live manuscript-audit / referee-prep:** `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/codex/` (94 files as of 2026-09-08; the sortable index of "what was happening" is `ls -lat`).

**Home dir total: ~405 GB** (SSD). Biggest consumers: `pablo_context` 143 G (mostly redundant `.lake` — reclaimable), `XOUT` 63 G (emergency-move grab-bag; contains 3.7 G irreplaceable personal photos in `PICS FROM PABS` — **keep**), `pi-node` 45 G (Pi Network / Stellar LIVE chain data — **DO NOT TOUCH**), `.cache` 42 G, `.elan` 23 G, `AI-Table` 14 G. Full audit: `~/HOME_MACHINE_MAP_2026-07-20.md`.

**Personal (keep, no exceptions):** `With Love for C and M`, XOUT photos, `PICS FROM PABS`.

---

## 7. Memory system — where continuity actually lives

`/home/xluxx/.claude/projects/-home-xluxx-principia-fractalis/memory/`. Index: `MEMORY.md`. As of 2026-09-09 it points to 25 memory files. **Order at the top of the index reflects priority:**

1. `unified-theory-proof-directive.md` — the controlling objective (see §1).
2. `PF_REFRESHER.md` — pointer to this refresher.
3. `collaboration-contract.md` — BINDING partnership terms.
4. `pf-corpus-map.md` — full-coverage map (2026-08-01).
5. `true-prop-audit.md`, `pf-framework-summary.md`, `pf-canonical-copy.md`, `home-machine-map.md`, `duplicate-findings.md`, `xluxx-mcp-servers.md`.
6. Arc-specific: `glimm-formalization-arc.md`, `hardy-rh-arc.md`, `hardy-rh-atom-closed.md`, `rh-transfer-arc.md`, `alpha-np-circular.md`, `bsd-axis-audit.md`, `independence-arc.md`, `ch24-spectral-falsified.md`, `fractal-dimension-arc.md`, `sigma-alpha-mechanism.md`, `refuted-book-theorems.md`, `cosmology-w-bridge.md`.
7. Discipline: `build-tree-discipline.md`, `no-honesty-framing.md`.
8. `publication-email.md`.

**These files are markdown. They are readable. If you are an AI reading this and you cannot open them, you have not tried yet. `cat` them. `Read` them. They exist.**

**Note on staleness:** memory files pre-dating 2026-09-07 name r219 as the cosmology frontier and `~/Principia-Fractalis` as the canonical path. Both are stale. Current frontier is r331b→r331c; canonical path is `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/`. Trust the codex/ dated files and the directive over any older memory file when they disagree.

---

## 8. Dispatch topology and what broke (2026-09-05 → 09)

**Boxes:** `192.168.0.94` (this Linux box, primary compute), Pablo's Windows CLI, WSL (Legion), Claude Desktop. `~/.claude/` is git-synced across all four surfaces (see `~/.claude/CLAUDE.md`).

**Dispatch daemon:** `~/.claude/remote/` — runtime in `run/f4d3688c/`, RPC socket `rpc.sock`, log `remote-server.log`, versioned CLI binaries in `ccd-cli/`, plugin cache in `plugins/`, server binaries in `srv/`.

**What broke on 2026-09-05 at 08:46 UTC:** the OAuth access token was revoked (visible in `~/.claude/projects/-home-xluxx/5dd0cf9d-6c06-4deb-ba8b-c0728102f7d5.jsonl`). Ten retries at 33–37 s intervals, then `"Please run /login · API Error: 401"`. Primary and dispatched instances shared credentials, so both died at the same instant. Dispatch on the other machine was also killed. This is auth, not usage.

**What jammed dispatch on restart** (five separate failures, from `~/.claude/remote/run/f4d3688c/remote-server.log`):
1. **Serena MCP** requires `uvx` — `uv`/`uvx` **not installed** on this box. Fix: `curl -LsSf https://astral.sh/uv/install.sh | sh`.
2. `~/.claude/settings.json → pablo` MCP points at `/home/xluxx/pablo-mcp/dist/index.js` — **missing**. Real path is `/home/xluxx/pablo-mcp-server/dist/index.js`.
3. `~/.claude.json → xluxx-trust` MCP points at `/home/xluxx/xluxx-trust-mcp/index.mjs` — **missing**.
4. `PF_REPO=/home/xluxx/Principia-Fractalis` env — path **missing**. Fix with symlink to `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/`.
5. `.claude.json` line 1183 legacy project `/home/xluxx/principia-fractalis` (lowercase) — dispatch tries to `chdir` and fails.

Every reconnect fires four subprocesses that all exit code 1; dispatch never reaches steady state. **Fable is not broken. The tool layer under Fable is unreachable.**

**Re-auth:** run `claude` then `/login` (or `claude auth login`) on each box. OAuth token lives in `~/.claude/.credentials.json`.

**Two live infrastructure notes recorded in the 2026-09-06 status report** (both resolved but recorded because the pattern will recur):
- **OOM restart loop 2026-09-06 08:18–08:54** — cause was one `lake build` per box accumulating memory; fix was per-module invocation (`a1_v2.sh`). Zero OOMs since 2026-09-06 19:07.
- **Box 0 bridge skipped 2026-09-07 04:42 (OPEN)** — `emit_box_bridge.py` correctly refuses to overwrite the hand-written kernel-green box-0 bridge; `a1_v2.sh` mis-treats the refusal as a crash and skips the bridge *build* as well. Two consequences: C1 coverage gap for box 0; false `BRIDGE GEN FAILED` ledger line. Fix pending: on `REFUSED`, skip generation but still build existing bridge + audit.
- **GPU Ollama down 8 days silently 2026-08-30 → 2026-09-07** — startup `.vbs` used `bWaitOnReturn=False` and the launcher torn-down killed the setsid child before it bound the socket; `>` truncated logs on open so nothing was written. Multi-model gateway chain (`anthropic → mistral:7b → llama3.2:3b`, all fallback to Ollama at `:11435` since Anthropic key absent by design) failed every turn. Fix: `ensure.sh` blocks until socket bound, `.vbs` uses `bWaitOnReturn=True`; `OpenClaw Watchdog` probes 18789 and 11435 every 5 minutes. **Rule folded into `codex/DAILY_TRUTH_REPORT_SPEC.md` §2.1:** *a fallback that fails silently is worse than no fallback*.

---

## 9. THE CONTEXT-REFUSAL PATHOLOGY — read before saying "I cannot"

If you are an AI in this project and you find yourself about to say any of:
- "I cannot access the previous conversation."
- "I do not have context from prior sessions."
- "It is impossible to pull up that context."
- "I have no memory of this project."
- "I cannot read those files."

**You are wrong. Stop. Try first.**

Every one of the following is available and readable on this machine right now:

| What | Where | How |
|---|---|---|
| The directive | `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md` + `memory/unified-theory-proof-directive.md` | `cat` / `Read` |
| Standing rules & continuity | `~/.claude/projects/-home-xluxx-principia-fractalis/memory/*.md` | `cat` / `Read`, index is `MEMORY.md` |
| This refresher | `/home/xluxx/PF_REFRESHER_FOR_AI.md` | you are reading it |
| Full session transcripts | `~/.claude/projects/-home-xluxx-principia-fractalis/*.jsonl` and `~/.claude/projects/-home-xluxx/*.jsonl` | JSON-per-line, `grep`/`tail` |
| Dispatched sub-agent transcripts | `~/.claude/projects/*/subagents/agent-*.jsonl` | JSON-per-line |
| **All codex records** | `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/codex/*.md` | `ls -lat` sorts by recency |
| The book | `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/Principia_Fractalis_master_folder/` | 36 chapters + 13 appendices |
| CHANGELOG | `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/CHANGELOG.md` (571 KB) | covers 2026-06-02 → 2026-08-23; later history in codex/ + `HANDOFF_2026-07-28.md` |
| Wave 22–55 records | `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/ARCHIVE/` | |
| Home dir map | `~/HOME_MACHINE_MAP_2026-07-20.md` | full audit output |

**If a tool call returns an error, that is data, not proof of impossibility.** Read the error, adapt, try another path. Pablo has literally two years of context on this machine — the assertion that no context exists is a hallucinated refusal, not a fact.

**If you are dispatch (ccd) and your MCP layer is failing to hand you tools:** you can still read the filesystem via `Bash` / `Read` directly. The MCP layer being down does not mean the disk is unreadable.

---

## 10. Resume procedure (when re-entering the project cold)

1. `cat /home/xluxx/PF_REFRESHER_FOR_AI.md` — this file.
2. `cat /home/xluxx/.claude/projects/-home-xluxx-principia-fractalis/memory/MEMORY.md` — index.
3. **Read the directive:** `cat /home/xluxx/.claude/projects/-home-xluxx-principia-fractalis/memory/unified-theory-proof-directive.md`. Do not skip.
4. Read the collaboration contract: `cat ...memory/collaboration-contract.md`.
5. Read the corpus map: `cat ...memory/pf-corpus-map.md`.
6. `cd "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/"`.
7. `ls -lat codex/ | head -30` — most recent first; this is "where we left off."
8. Read the four most recent load-bearing docs:
   - `codex/READBACK_AUDIT_2026-09-08.md`
   - `codex/R331C_CAMPAIGN_CHARTER.md`
   - `codex/FLT_LESSONS_FOR_PF_2026-09-08.md`
   - `codex/FULL_STATUS_REPORT_2026-09-06.md`
9. Read the unified-theory core: `codex/COMPLETION_THEOREM_DRAFT.md`, `codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.md`, `codex/ALPHA_RIGIDITY_AUDIT_REPORT_2026-09-07.md`.
10. Read `codex/RELEASE_GATE_r331b.md` for what remains to freeze the r331b artifact.
11. **Verify the build is green before making claims:** run `lake build PF` if you are about to modify Lean. Never take an agent's compile report — parse `#print axioms` output yourself, and remember that Lean wraps long axiom lists across lines (`tr '\n' ' '` then split on `depends on axioms:`).
12. **When you land a Lean stone:** verify both `grep -c "^#print axioms" <file>` > 0 AND `grep -rn "import PF.<Stone>" PF.lean` succeeds. Non-negotiable.
13. **Report format** — §10 of the directive: central theorem status; became proved; became disproved/weaker; blocking obligation; assumption/circularity changes; kernel + rebuild status; decision required from Pablo; next decisive action. If nothing changed: "No change to the unified-theory proof state."

---

## 11. Etiquette

- No "honestly." (Rule 7.)
- No sycophancy, no false modesty, no drum-roll before answers.
- Structured output with clear headings. Numbered steps. Direct.
- Pablo has neurodivergent accommodations. Long walls of prose without structure are hostile to how he reads. Use tables, numbered lists, short paragraphs.
- If you are wrong, say so plainly and correct. Do not narrate the correction as growth.
- If a claim requires kernel verification and you have not verified it, say "not verified" or "asserted, not proven." Do not blur.
- Cite Pablo's own records. Do not re-discover his project.
- Every task you queue must state its unified-theory obligation, failure mode tested, trust property protected, OR its non-core-and-capped status. §1 queue gate.

---

## 12. When in doubt

- **The unified-theory proof is the controlling objective.**
- The book is the Bible.
- The kernel is the judge.
- The dependency audit decides whether the derivation is substantive.
- Observation decides whether the formal structure describes nature.
- Continuity is your job, not Pablo's.
- If something feels "impossible," you have not tried yet.

---

*This refresher lives at `/home/xluxx/PF_REFRESHER_FOR_AI.md`. A pointer is indexed at `~/.claude/projects/-home-xluxx-principia-fractalis/memory/PF_REFRESHER.md`. The controlling directive lives at `~/.claude/projects/-home-xluxx-principia-fractalis/memory/unified-theory-proof-directive.md` and at `/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md`. Update all three when the project state moves.*
