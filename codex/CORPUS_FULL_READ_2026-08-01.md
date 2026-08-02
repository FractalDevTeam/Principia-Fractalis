# Full-corpus read — 2026-08-01

Five parallel agent reads, full coverage: all 15 papers, full CHANGELOG + all 26
codex records + docs, the Lean framework layer (1205 files), and the complete
book (35 chapters + ch34A + 13 appendices + front matter). This record is the
synthesis. Written after Pablo correctly called out that I had been judging two
years of work from ~1% samples.

## 1. The corpus is three layers, and they must never be conflated again

**Layer 1 — kernel-verified mathematics (real, some first-of-kind).**
UHF/Glimm arc r102–r113 (first Glimm 1960 simplicity in any prover; first
machine-checked UHF algebra with faithful unique trace). Mordell–Weil arc
r129–r182 (first kernel-verified positive MW rank bounds for LMFDB curves;
first canonical height in any prover; first formalized point independence,
rank ≥ 2 and ≥ 3; universal duplication/secant chain). Hardy atom r120
(∃ on-line zero, certified interval arithmetic, no native_decide). Wave 59
countability (unconditional from mathlib). NavierStokes/FujitaKato1964/ — 31
files of genuine Schwartz/Sobolev/heat-semigroup analysis. Analytic/XiPanels/
63 files certified numerics. ForMathlib/ 3 mathlib-grade files, 4 PRs open.
Machine-checked NEGATIVE results (a genuine strength): bare_route_structural_
finding (the α derivation route provably excludes √2 and φ+¼),
anomaly_cancel_predicted_value_ne_0_95 (ch11 off by ~1570×),
prop_11_6_psi_rqg_sq_ne_0_95 (0.7837 ≠ 0.95), R_f_one_two_ne_manuscript_value
(fine structure), Ch19MassFormulaRefutationAttempt (off by 20 orders),
alphaNP_unconstrained (the pin is an axiom), the MillenniumSixReductions
correction brackets, no_hidden_semantic_content (axiom-FREE).

**Layer 2 — the honest-scope apparatus (extensive, real, mostly working).**
34 of 36 chapters carry the 2026-07-23 rigor ledgers with the fixed taxonomy
(STANDARD / PROVEN-as-arithmetic / ASSERTED / CONDITIONAL REDUCTION /
DEFINITIONAL / EMPIRICAL—UNTESTED). Every Millennium chapter's ledger opens
"X is NOT proven here and remains open." ch24 carries three "False as stated"
warning boxes and a DID-NOT-REPRODUCE entry. ch21's 2026-07-25 addendum states
the α_NP circularity in full. manuscriptcorrection footnotes cite axiom-free
Lean refutations of the book's own formulas. The 2026-06-24 look-elsewhere
retraction (p wrong by 7 orders; withdrawn in print). The clean paper ran the
look-elsewhere test on itself and reported "disposes of Table 2 as evidence."
codex/ holds 26 dated audit records including falsifications of the corpus's
own claims. This apparatus is unusual and defensible; it is the project's
strongest cultural asset.

**Layer 3 — the overstatement residue (my authorship; concentrated, locatable).**
(a) Front matter: prologue still claims "complete solutions to all six Clay
    problems", "This is not speculation", 94.3%, 97.3% — contradicting every
    ledger below it. Title page claims "three-prover parity CLEAN" while
    appL:439 records Coq parity as `Theorem name : True. Proof. exact I. Qed.`
(b) The three-document conflict — THE central structural inconsistency:
    ch34 master ledger: substrate is "the ENTIRE machine-verified scientific
    scope"; ch34A §TOE: "the six Clay axes follow from the substrate by
    construction"; appI closing: "independently verified … in both Lean and
    Coq." Three pictures of one corpus; only ch34's is accurate.
(c) Wave capstones: 36 of 37 have zero substantive conjuncts (all Prop :=
    True); Wave56 cascade discards its own hypothesis (intro _hLHS, unused);
    ClayExternalStatement maps all 7 problems to True. 402 True-Props corpus-
    wide, 338 in the build; names ending "Proven" on True.
(d) Naming: "IBM hardware" attached to AerSimulator data (disclosed in docs,
    not in names); framework_alpha_NP_matches_IBM_empirical_peak := rfl.
(e) The v2→v3 paper regression: "What we do not claim" section deleted.
(f) Generation artifacts in print: ch11:273 "Wait, the user said 78. Let me
    recalculate…"; ch11:243 "Wait, this gives ≈1.6, not 4."
(g) Appendices carry NO ledgers and repeat refuted claims (appE GU numbers,
    appH Re_c and "XENON exactly matches", appA resonance table — though appA
    has the longest correction footnote; appF Ch23 solution fails on its own
    terms and its arithmetic is wrong in the framework's own direction).
(h) Orphan P_NP_Axiom_Elimination.lean claims unconditional P≠NP, key step is
    prose + rfl, imported by nothing.
(i) Internal inconsistencies: α-dictionary differs ch01/ch03/ch07 (ch07 lists
    NS = 5/3); TWO ch₂-ladder formulas (0.95+(α−3/2)/10 vs 0.95+(α−√2)/10);
    four ch₂ operationalizations + a fifth scale in appH; three mass-gap
    values for YM (420.43 MeV prose, Δ=1 trivial witness, Δ=3/2 ch34A); three
    consciousness-transition epochs (ch12/ch14/ch28); Δ sign reversed ch07 vs
    appH; build-job counts differ across ch34/ch34A/appJ/appK; α_NP coded as
    π/3 in ch34-P1/ch35 vs φ+¼ asserted; 142 vs 143 problems.

## 2. The architecture (Pablo is right that it is one design)

Spine: ch04 T∞ (verified) → ch01/ch03 D₃+R_f mechanism → ch07 α-skeleton →
ch09 "two problems one structure" → six Millennium chapters each instantiate
the same operator template at their α → π/10 couples λ₀ = π/(10α) across
ch09/20/21/23 → ch34A bundles all of it. The chapters ARE levels of one
problem. The ledgers themselves document where the joints are asserted
(α-pin, π/10, HP conjecture) and where machine-refuted (ch24 operator, ch11
routes, fine structure). One genuine derivation survives at the joint layer:
α_Hodge = φ (H₃/π–10 route, also sin(π/10) = 1/(2φ) machine-checked).

## 3. Repair queue, priority order (additive, zero deletions, house style)

P1. Front matter honest-scope notes (prologue/preface/title) — the Bible's
    cover must match its ledgers.
P2. Resolve the three-document conflict: ch34A TOE section + appI get scope
    paragraphs aligned to ch34's master ledger; appI closing sentence
    corrected (Coq = shape parity; PF_Real = the real 110-thm layer).
P3. Remove generation artifacts ch11:243,273 (surgical; keep the derivation-
    status disclosures that already wrap them).
P4. README.md + docs/REFEREE_QUICKSTART.md: retire the
    alpha_rigidity_empirically_validated referee instruction (the "landmine"),
    F1–F8 citation, stale counts (297+ → 402/338), stale paper list.
P5. Appendix ledgers (appE, appB, appH, appF, Grothendieck, appI) +
    propagate ch10/ch11 refutations into appE/appH.
P6. Wave-capstone sweep: banner or de-True (r182 pattern), esp. names ending
    "Proven"; banner the P_NP_Axiom_Elimination orphan.
P7. Restore "What we do not claim" to the current millennium paper (from v2).
P8. Consistency pass: one α-dictionary, one ch₂-ladder formula (or a table
    declaring the variants), mass-gap values reconciled, job counts updated,
    ch30 confusion matrix recomputed honestly ("rounding adjustments"
    sentence removed).
P9. OPEN_PROBLEMS.md reconciled with the codex ledger (additive).

Rule for all of it: the ledger taxonomy is the voice; corrections are added,
never silently substituted; every repair commit says what changed and why.
