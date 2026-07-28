# CONTINUATION PLAN — written 2026-07-28 (Fable budget low)

Single source of truth for resuming work in ANY future session.
Read this + the two wall maps first; everything else is in git history.

## Where everything lives

- Lean corpus: `PF_Lean4_Code/` (pin v4.24.0-rc1, mathlib eed770a4).
  Build: `env PATH="$HOME/.elan/bin:$PATH" lake build PF` (~4,644 jobs).
  Single file check: `lake env lean PF/<file>.lean`.
- Wall maps: `codex/BSD_NONTORSION_ARC_PLAN_2026-07-27.md` (arc 1, CLOSED),
  `codex/RANK2_INDEPENDENCE_ARC_PLAN_2026-07-28.md` (arc 2, ACTIVE).
- W2 certificates: `codex/W2_CERTIFICATES_389a1.md` + regenerating script
  `codex/w2_certificates_389a1_gen.py` (run with /home/xluxx/ai-env/bin/python).
- Ground-truth data pack (all curves): scratchpad file
  `cohort_data_pack.txt` — IF the scratchpad is gone (it is
  session-temporary!), regenerate any curve's data with sympy exactly as
  in `w2_certificates_389a1_gen.py`'s style; the committed wall maps
  contain every load-bearing number already.
- Persistent memory: `~/.claude/projects/-home-xluxx-principia-fractalis/memory/`
  (index MEMORY.md; see `bsd-axis-audit.md` for the whole BSD story).

## Verification protocol (NEVER skip)

agent/self proves → independent `lake env lean` rebuild → check NO sorry /
native_decide / new axioms → transitive `#print axioms` =
`[propext, Classical.choice, Quot.sound]` → register import in `PF.lean`
→ full `lake build PF` → commit → push. Axiom output from a FAILING build
means nothing (sorryAx appears via error recovery).

## State of arc 2 (independence: rank ≥ 2 on 389a1, rank ≥ 3 on 5077a1)

DONE and pushed (all kernel-clean):
- W0: r143 (389a1), r144 (5077a1) — dbl_x + quartic lower bound + rank ≥ 1
- W1: r145 (389a1, window [H⁴/1728, 17H⁴]), r146 (5077a1, [H⁴/105754, 114H⁴])
- W2 GROUND TRUTH: complete verified certificate suite (see the W2 report;
  key: gcd(DD,S,P) ∣ 389³; control forms are exactly r143's F, G3; m=2
  determinant route via irreducible sextic R6)

IN FLIGHT at time of writing:
- W3 = r147 DONE (canheight constructed; = 0 iff torsion; both directions). Was:: lognh,
  hseq R n = lognh(2ⁿ•R)/4ⁿ, CauchySeq via geometric modulus log(1728)/4ⁿ,
  canheight := limUnder atTop, API: nonneg, dbl (=4×), window (≤ log1728/3),
  canheight_eq_zero → torsion (via Northcott-for-ℚ + finite-orbit trick),
  ideally the converse too. IF ITS FILE EXISTS but wasn't committed:
  verify per protocol and commit as r147. If absent: relaunch from the
  spec in the wall map §W3 (full spec was in the agent prompt; the wall
  map has enough to reconstruct it).

NEXT STONES in order:
1. r147 = W3 (canonical height 389a1) — verify/land the in-flight file.
2. r148 — r148a, r148b AND r148c DONE & PUSHED (r148c: DD_upper 4H², Sf_upper 17H²; Pf_upper 10H² + lower bounds + secant bridge + root bookkeeping + log assembly remain) (content bound gcd(DD,Sf,Pf) | 389^4 complete via squaring trick, no corner cofactors needed) (certificate layer: DD/Sf/Pf defs, diagonal
   sanity, both Cramer certs, dvd_R6_of_dvd_forms). REMAINDER of r148:
   level-2 composition (R6 → 389³ via the F/G3 certs in the W2 report),
   size bounds, mathlib addX/slope bridge (secant case), quadratic-root
   height bookkeeping, Real.log assembly. Target: the quasi-parallelogram
   |lognh(P+Q) + lognh(P−Q) − 2lognh P − 2lognh Q| ≤ C₂.
   Inputs all ready: homogenized DD, S, P (wall map), the Cramer m=2
   certificates + level-2 Bézout identities (W2 report — compose as TWO
   ring lemmas, do NOT inline the expanded corners, κ~10⁹ there).
   Structure mirrors r131+r133: gcd control (∣389³) + size bounds
   (coefficient sums in the W2 report) + quadratic-root height bounds:
   for x₃,x₄ roots of A T² − B T + C (A≠0): max heights vs max(|A|,|B|,|C|)
   both directions (elementary; x₃+x₄ = B/A, x₃x₄ = C/A).
   Degenerate cases: x₁ = x₂ handled by r143/r145 duplication bounds
   (P₂ = ±P₁); one of the points = O reduces to trivial.
3. r149 = W3 upgrade with W2: exact parallelogram for canheight
   (limit of quasi-parallelogram under 2ⁿ-scaling), then bilinearity:
   pairing(P,Q) := (ĥ(P+Q) − ĥP − ĥQ)/2 and ĥ(mP+nQ) = m²ĥP + 2mn·pairing + n²ĥQ
   (standard: iterate parallelogram; integer induction).
4. r150 = W4 (389a1): regulator window. Compute by norm_num the exact
   rationals lognh(2ⁿ•P), lognh(2ⁿ•Q), lognh(2ⁿ•(P+Q)) for n up to ~6
   (P=(0,0), Q=(1,0); P+Q compute via the group law — sympy first!),
   derive rational windows for ĥP, ĥQ, ĥ(P+Q) via canheight_window scaled
   (|ĥ − hseq n| ≤ log1728/(3·4ⁿ)), then det > 0 in interval arithmetic.
   Sanity target: regulator ≈ 0.1524 (NOT a proof input).
   NOTE: window uses log 1728 — irrational; keep bounds as
   log(rational) ≤ ĥ ≤ log(rational) and compare dets via
   log-monotonicity, or bound log 1728 by rationals via
   Real.log_le_sub_one_of_pos-style estimates or exp bounds
   (mathlib: Real.exp_one_lt_d9 etc. — plan the exact route BEFORE writing).
5. r151 = W5 (389a1): positive-definite q(m,n) ⟹ (m,n) ↦ mP+nQ injective
   ℤ² → E(ℚ) ⟹ 2 ≤ Module.rank ℤ E389a1(ℚ). Rank step mirrors r129 with
   ℤ² (Module.rank ℤ (ℤ×ℤ) = 2; LinearMap.lift_rank_le_of_injective).
6. r152+ = repeat W2–W5 for 5077a1 (3×3 regulator, Sylvester minors;
   generators (−2,3), (−1,3), (0,2); regulator ≈ 0.417). All ground
   truth regenerable via the W2 script pattern with a=(0,0,1,-7,6).

## Also open (lower priority)

- 102a1 rank ≥ 1: needs per-step variant (rational 2-torsion at x=0;
  the invariant "h > κ ⟹ x ≠ 0 ⟹ not 2-torsion" carried through the
  chain sigma — sketch in bsd-axis-audit memory).
- turing repo: commit f3a3334 local-only, blocked on FractalDevTeam push
  access for DrDMT-VR.
- mathlib PR #42101: may need Authors: header attribution decision.
- Papers: six_as_one.pdf BSD sentence must be reworded (the audit:
  "discharges" was a rfl tautology — now replaceable by the REAL results
  r129–r146); skeleton paper should cite r128 instead of
  framework_alpha_unique_under_perelman_anchor (wrong arity/constant).

## Working style (Pablo's standing directives)

Be bold, no hedging, mathematical truth and rigor above all. Structured
output, direct language (neurodivergent accommodations). Do the work
autonomously; report outcomes, not plans. Never fake: no sorry, no
native_decide, no Prop := True, hypotheses in theorems not prose.
sympy-verify every identity before writing Lean (this produced 8
consecutive first-pass-clean files). Commit + push after every verified
stone.
