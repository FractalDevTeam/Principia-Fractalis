# Chapter Audit Ledger — the 20-Chapter Sweep, 2026-10-05

Complete findings record for the sweep that covered every chapter not already
carrying a 2026-10-05 correction. Seven parallel audits, ~29,500 lines of
manuscript, cross-checked against the Lean corpus.

**This document exists so that nothing found is lost between sessions.** Items
marked LANDED have a PRISTINE Lean module and a `\manuscriptcorrection{}` in the
chapter. Items marked **OPEN** are verified but not yet written into the
manuscript — they are the work queue, in severity order.

## How to read the verification column

* **VERIFIED** — I recomputed or re-derived it myself, independently of the
  audit that reported it. Every such claim below was checked before being
  written down.
* **AGENT** — reported by an audit and not yet independently re-derived. Treat
  as a candidate, not a finding. Three agent claims were **downgraded** during
  this sweep after my own check (see *Corrections to the audits* at the end), so
  this distinction is not a formality.

## Severity

* **S1** — the claim is false or impossible as stated, and something load-bearing
  rests on it.
* **S2** — false or impossible as stated, locally contained.
* **S3** — underived premise presented as established, or a stale restatement.
* **S4** — cosmetic, or already scoped by the chapter.

---

# 1. LANDED

| Ch | Site | Sev | Finding | Verified |
|---|---|---|---|---|
| 21 | `:343–372`, `:455` | S1 | Compactness + non-decreasing enumeration force **every** eigenvalue to 0, so `Δ = 0` against the boxed `Δ ≈ 0.0891`. Answers the `λ₀` question: over-determined to zero, not merely unpinned. Repair: unbounded operator with compact resolvent. | VERIFIED |
| 21 | `:516`, `:1011` | S2 | `conj:golden-modulation` refuted in Lean since before the chapter's last edit; open-problem item 3 asks for an object proved not to exist. | VERIFIED |
| 10 | `:353` + 12 sites | S1 | `d_f = 3 − ζ₂/2` unestablished; fails the K41 baseline both directions (gives 8/3 where K41 is space-filling `D = 3`). **My own earlier "repair" propagated it.** | VERIFIED |
| 29 | `:410` | S1 | "Adjusted improvement = 94.3%" exceeds the unadjusted 94.043%, while any parameter penalty must *lower* it. Ten readings tested, none reproduces it. | VERIFIED |
| 29 | `:442` | S3 | `ΔBIC = 319.6` restated after being corrected to `320.37` three lines above — **created by the earlier pass**. | VERIFIED |
| 22 | `:112` | S1 | Purely-imaginary eigenvalues ⟺ `det(∇u) = 0` **and** `ch₂(∇u) ≤ 0`; the second is rotation-dominating-strain, i.e. the chapter's own physics — but it is *opposed in sign* to its `ch₂ ≥ 0.95` threshold. | VERIFIED (400k matrices) |
| 22 | `:385` | S1 | "Vorticity remains bounded" above an equation dividing by `r⁻¹`, which states `\|ω\| ∼ C/r`, diverging. By BKM that is the singularity Step 5 excludes. | VERIFIED |
| 20 | `:349`, `:368` | S1 | Boxed scaling formula returns `4.44 × 10⁶` where the chapter's own verbatim block prints `14.2267`; factor `3.12 × 10⁵` consistent across all three rows. | VERIFIED |
| 20 | `:470` vs `:483` | S2 | Same section says 9-class and 10-canonical. `Δ_Σ = 0.0059` matches the **ten**-value sum (0.005924), not the nine (0.005704). | VERIFIED |
| 20 | `:360` | S4 | `30.425` labelled "(3rd)"; it is the **fourth** nontrivial zero. | VERIFIED |
| 25 | `:512` | S1 | "22 divisors" on a K3; `ρ ≤ h^{1,1} = 20`. Chapter says `ρ=20` ten lines later; Lean already proves `picard_le_twenty`. | VERIFIED |
| 25 | `:514` | S2 | "240 cycles" on an abelian 4-fold; total Hodge dimension across every codimension is `70`. | VERIFIED |
| 25 | `:354` | S3 | `ε_quantum = 0.95 − 6/π²` exactly — the remainder to a pre-chosen target. ch26 carries this caveat; ch25 does not. | VERIFIED |
| 23 | `:437` | S1 | `σ = Δ²/(4πℏc)` gives `71.29`; asserted `440.21² = 193 785`. Factor `2718`. Independent of the retracted `ω_c`. | VERIFIED |
| 23 | `:107,144,596` | S1 | `ℛ_f(2,s) = ζ(s) → 1` per the chapter's own correction, so `ℳ(s) → e^{−1} ≈ 0.368`, **not** Gaussian suppression. The existing correction never followed its own root cause here. | VERIFIED |
| 24 | `:590–594` | **S1** | **"rank `E(ℚ)` = 0 (proven)" is false.** `P = (3,5)` is on `y² = x³ − 2` (the chapter's own introduction prints it), `2P = (129/100, −383/1000)` likewise, heights grow super-exponentially; by Mazur `P` has infinite order, so `rank ≥ 1`. | VERIFIED |
| 24 | `:601–606` | **S1** | **The named "generator" `(−2,−4)` is not on `y² = x³ − x`** (`16 ≠ −6`), and that is the `n = 1` congruent-number curve of rank 0, not `n = 5`. | VERIFIED |
| 24 | `:106–110` | S2 | `#E(𝔽₅) = 6`, `a₅ = 0`; chapter says `2` and `4`. Found one of five affine points. | VERIFIED |
| 24 | `:457–474` | S2 | Complexity proof sums a term it computed as `O(N log²N)` and reports `O(N^{1/2+ε})`. | VERIFIED |
| 17/18 | `:269` vs `:446`; `18:121` | S1 | `C` defined twice over different domains; ch18 uses the `Spec(T_∞)` form, which ch16 proves **empty**, so `C = 0`, `I_C ≡ 0`, `‖C‖ = 0` against item 3's `‖C‖ = ∞`, and item 4 quantifies over subsets of `∅`. ch34A drew this conclusion and it never reached ch17/18. | VERIFIED |
| 34A | `:1762` | S3 | Bare `PROVEN` on a tautology, qualified to `PROVEN-as-Lean-tautology (only)` using the chapter's own convention. | VERIFIED |

---

## STATUS UPDATE — end of 2026-10-05

**The OPEN queue below has been worked.** Everything that was S1 or S2 and
marked VERIFIED, plus every S1 that was marked AGENT and then independently
re-derived, is now LANDED: a PRISTINE Lean module and a
`\manuscriptcorrection{}` in the chapter. Four more modules were added after
this document was first written:

| module | decls | covers |
|---|---|---|
| `Ch01Ch03Ch04Ch06FoundationDefects` | 22 | ch04's inverse-limit collapse and inert `F_α`; ch06's Bell state; ch03's phase sequence; ch01's base-3 conversion |
| `Ch30Ch31Ch32ClinicalStatistics` | 17 | ch30's permuted metrics, stratified total, heading, per-1000; ch31's unbounded band ratio; ch32's age slope |
| `Ch12Ch13Ch28Ch34PhysicsDefects` | 18 | ch12's crystallization energy, pairing factor, two predictions; ch13's standing withdrawn paragraph; ch28's Hubble scale; ch34's level-16 memory |
| `Ch23Ch24MillenniumNumerics` | 17 | ch24's false rank, off-curve generator, point count, complexity; ch23's string tension and UV claim |

Also landed as prose notes, each arithmetic claim recomputed first: ch01's two
`max D₃` approximations (both exactly one high, against the chapter's own exact
`2k` theorem); ch03's three spectral-gap digits (matching no certified value,
with ch09 printing a fourth for the same quantity); ch23's two Clay-clause
`theorem` labels (content already scoped by the chapter's ledger, labels never
changed); ch04's "dyadic base-3"; ch05's cross-reference to vortex material ch04
does not contain.

**What remains open is now, in the main, authorial rather than findable.** The
residue is listed at the end of this update.

### The four of my own errors the tooling caught

Recorded because the ratio matters: four defects were introduced *by me* during
this queue and every one was caught by a check rather than by my own reading.

1. `decide` proved the negation of a strata-count theorem — I had used integer
   division where rounding was meant (`143 × 0.993` truncates to 141).
2. Lean refused `0.968 < 422/436`; the true value is `0.96789`, below it. The
   claim had to be restated as a rounding bound, which is what a three-figure
   printed value actually means.
3. The GeV⁻²→pb conversion was written `3.894 × 10⁹`, a factor of ten too large.
4. The speed of light was written `2.998 × 10⁹` instead of `2.998 × 10⁸`.

And the empty-math-environment guard — added after an earlier pass left a stray
`egin{equation}\end{equation}` in ch25 — fired on my own ch04 edit and
refused the write.

**The lesson is the one the campaign keeps relearning.** Items 3 and 4 are the
same defect class this very document catalogues in the manuscript: a constant
transcribed at the wrong order of magnitude, invisible on inspection, caught
only by recomputation. I found them in the book and then committed them myself,
twice, in the module written to document them.

### Residue

* **Authorial, cannot be read off the text**: which multifractal model ch10
  intends; ch29's observation count and fit provenance; ch20's actual scaling
  calculation and whether its corroboration target is 9 or 10 values; ch25's K3
  divisor count and abelian-fourfold convention; ch21's `λ₀` referent under the
  repaired operator; ch04's Haar measure; ch17's propagator domain; ch30/ch32's
  clinical provenance; and above all **which of the five `ch₂` quantities the
  0.95 threshold belongs to**.
* **Found but not yet written into the manuscript**: ch34's PF_L4L module
  miscount and its stale "repository root" location claim; ch34's Mayer-trace
  decimal placed beside "kernel-checked"; ch31's `N ≥ 2` cap versus the 800+
  reported values above 0.95, and its two incompatible `Φ` values; ch24's
  `L_f` continuation; ch03's `η(s)` item and its stale numerical-verification
  table; ch12's single symbol for two `m_C` scales; ch13's `Δr_h/r_h`
  dimensions; ch28's acoustic-peak formula; ch06's `W²` off-diagonal typo
  (harmless — only `Tr(W²)` and `‖W‖_F²` enter, and `ch₂ = 0.50` is unaffected);
  ch04/ch06's bacteria classification; and the absence of any mention of
  `PRISTINE` in ch33/34/35, the three chapters that tell the reader what is
  verified.
* **One Lean item**: `SubstrateRigidity`'s last `(d2)` finding, on
  `tower_union_starHom_uniformContinuous`, needs a structure split (23 in-file
  references). Deliberately not started at the tail of a session on that file.

---

# 2. OPEN — verified, not yet in the manuscript

Severity order. These are the queue.

## S1 — load-bearing

| Ch | Site | Finding | Verified |
|---|---|---|---|
| 04 | `:227–272` | **The construction of `T_∞` contradicts its own K-theory answer.** Def 4.5 sets `φ_{k,k'} : A_{k'} → A_k` (coarse-graining, *down*) and Def 4.6 boxes `T_∞ = lim←`. The inverse limit of `ℤ ←×3− ℤ ←×3− ⋯` forces `3^k | a₀` for every `k`, so it is the **zero group** — not the boxed `ℤ[1/3]`. The boxed answer needs the *direct* limit, which is also what Lean formalizes (`Substrate3Inf.tower_mono`, inclusions going *up*). The final values `K₀ = ℤ[1/3]`, `K₁ = 0` are correct for `M_{3^∞}`; only the method and direction are broken. Also: the chapter concedes the `φ` are merely completely positive contractions, not `*`-homomorphisms, while the next theorem applies `K`-theory functoriality to them. | VERIFIED |
| 31 | `:189–193` | **A third, unbounded `ch₂`.** `ch₂ = \|P_β²/(P_δ·P_θ)\|^{1/3}` has no normalisation and is unbounded: `(10,1,1) ↦ 4.64`, `(100,1,1) ↦ 21.5`. It contradicts ch32's own stated constraint `0 ≤ ch₂ ≤ 1` (`32:361`), and blows up exactly when β dominates — the alert state the 0.95 threshold is meant to pick out. | VERIFIED |
| 30 | `:242–254` vs `:272–293` | **Boxed sens/spec/PPV/NPV do not match the chapter's own confusion matrix, and two are permuted.** From `TN=402, FN=9, FP=14, TP=422`: sens `97.9`, spec `96.6`, PPV `96.8`, NPV `97.8`. Boxed: sens `96.8` (= the correct **PPV**), spec `97.8` (= the correct **NPV**), PPV `97.4` and NPV `97.2` matching **none** of the four. | VERIFIED |
| 12 | `:333–337` | **Impossible direction.** `E_cryst ∼ m_C·exp(−1/(b₀g_C²))` with `b₀ > 0` gives `E_cryst < m_C = 10⁻⁵` eV for *every* positive `b₀`, yet `∼ 1` eV is claimed — 10⁵× its own input mass. Computed across `b₀ ∈ [0.01, 5]`: max `2.06 × 10⁻¹⁴` eV. | AGENT |
| 28 | `:263–271` | `Λ_eff = Λ₀ ∼ M_Pl⁴` with `H_I² = Λ₀/3` is dimensionally inconsistent as typeset (GeV² vs GeV⁴), and with the chapter's own reduced-Planck convention gives `H_I = M_Pl/√3 = 1.39 × 10¹⁸` GeV, not the stated `10¹⁴` — 4.1 orders. The two numbers are the full-Planck and GUT-inflation scales respectively. | AGENT |
| 13 | `:325–337` | **Same pattern as ch29:442, worse.** The 2026-10-03 remark at `:300–323` proves `w_C ∈ [−1/3, +1/3]`, states the negative-pressure dark-energy mechanism "does not follow", and says "that claim is withdrawn as stated" — and the paragraph it names is **still there, unedited**, three lines below, asserting negative pressure and `Λ_eff(t) = Λ₀exp[−∫Γ_C]`. `EquationOfStateBridge_r219.lean` independently proves that mechanism cannot give `w < −1`. | AGENT |
| 34 | `:255`, `:598`, `:609` | **ch34 was skipped by the correction pass that fixed its sibling.** It restates the exact P1 figures ch35's own 2026-10-03 correction proves impossible from the code shown: level-16 dense needs **14.8 PB**, not "128 GB" (factor `1.2 × 10⁵`); the "4 hours / 10 minutes" runtimes are the same wording ch35 calls "not of the right order". `grep '2026-10-03'` over ch34 returns **zero** matches while ch33 and ch35 return several. | AGENT |

## S2 — contained

| Ch | Site | Finding | Verified |
|---|---|---|---|
| 01 | `:1297–1299` | `987654321 = (2111222010202101210)₃` is wrong — that numeral is `975268155`. True expansion `2112211110001000200`, digit sum **15**, not the stated 21. The parity conclusion survives only because both are odd, which hides it from a reader checking the punchline. | VERIFIED |
| 03 | `:73` | The displayed phase sequence contains `0`, which `\|ω_n(α)\| = 1` — proved in the same chapter at `:150` — forbids. With ch01's own parity theorem `D₃(n) ≡ n (mod 2)`, `ω_n(1) = (−1)ⁿ` exactly: strictly period 2, contradicting "not purely periodic!". | VERIFIED |
| 06 | `:568`, `:549` | **The Bell-state witness is wrong, and the chapter's own reconciliation note repeats it as settled.** `ch₂ = 1 − Tr(ρ_A²)` on a 2-qubit Bell state is `1 − 1/2 = 1/2`, not `1`. For any `d`-dimensional subsystem `Tr(ρ²) ≥ 1/d`, so `ch₂ ≤ 1 − 1/d`; reaching 1 needs `d → ∞`. Same `1/2` ceiling as the matrix formula — a fresh instance of the exact class the 2026-10-03 pass caught, which slipped through the note that catalogues it. | VERIFIED |
| 03 | `:273–281` | `Δ_P = 0.0891219046`, `Δ_NP = 0.1337359842` match **no** certified value. `SpectralGap.lean` gives `Δ = 0.0539677`; ch09 quotes a fourth value `0.1330222423` for the same quantity. The three-way inconsistency is already named in `SpectralGapInconsistencyAnalysis.lean` and disclosed in ch09/ch07/ch21 — ch03's ledger says only "numerical outputs, not a proof". | VERIFIED |
| 30 | `:359–382` vs `:242` | Stratified accuracy table pins 821 correct (142+252+183+153+91); headline confusion matrix says 824. Three-patient discrepancy between two presentations of one cohort. | VERIFIED |
| 30 | `:453` | Heading "The 15 Discrepant Cases" over a body listing 23 (9 FN + 14 FP), consistent with the matrix. | VERIFIED |
| 04 | `:172–178` | `F_α = C*({ℛ_f(α,n)})` is generated by **complex numbers**, not operators, so it is a subalgebra of `ℂ` — at most 1-dimensional. The `α`-dependent "fractal resonance" tensor factor contributes nothing to any `A_k` or to `T_∞`. Already flagged in `codex/FRAMEWORK_TRANSLATION_2026-08-06.md:152`; ch04 carries no note. | AGENT |
| 12 | `:142–148` | The 4-term field-strength formula does not have the antisymmetry asserted on the next line: under `μ↔ν` the third term keeps its sign. `:88`'s version of the same formula ends "+…", conceding incompleteness; `:142` presents it as complete. | AGENT |
| 34 | `:628–639` | "Four PF_L4L modules build clean" counts 3 module files; two of the four items are `def`s in the same file, and declaration names are used as module paths. The source audit says "2 of 8 + 1 new" = 3. | AGENT |
| 34 | `:678`, `:687` | "all committed at the repository root for referee inspection" — the five `REFEREE_PROOF_*.md` moved to `ARCHIVE/2026-06-08-cleanup/root_docs/`, and ch34 was edited after the move. A referee following the instruction finds nothing. | AGENT |
| 31 | `:91–134` vs ch30/32 | ch31's own 2026-10-03 correction proves `{ch₂ ≥ 0.95}` is **empty for every `N ≥ 2`** for the generic formula family, and ch30/ch32 report 800+ EEG-derived values at or above 0.95 without citing it. Whether the clinical construction escapes the cap has never been shown, only assumed by omission. | AGENT |
| 31 | `:66–78` | `Φ = −log₂(1−0.95) ≈ 4.32` bits, stated as equality; the Lean theorem ch30 cites for the bridge proves an *inequality* with `Φ := 2·S_vN` (natural log), giving `≥ 2ln20 ≈ 5.99` — different number, different object, and only for Schmidt spectra of finite-dimensional reduced density matrices, not EEG. | AGENT |

## S3 — underived or stale

| Ch | Site | Finding | Verified |
|---|---|---|---|
| 32 | `:402–406` | Age slope `−0.00012`/yr is `−0.0012`/decade; chapter says `0.012` — 10× overstated. Its own two reference ages confirm `0.0012`. | VERIFIED |
| 30 | `:352` | `973 − 600 = 373` per 1000, not the stated `350`; the derived `70,000–105,000` national figure is built from 350 (exactly `350 × 200k…300k`), so it inherits. With 373: `74,600–111,900`. | VERIFIED |
| 03 | `:113–129` | Proposition items (2)–(3) stated as established with proof "in the exercises". Item (2) fails numerically: `R_f(2/π,2) = −0.631 + 0.751i` is complex, `η(2) = π²/12 ≈ 0.8225` is real. Lean formalizes only the `α = 0` case. | AGENT |
| 24 | `:227–247` | `L_f(E,s)`'s continuation, functional equation and order-preservation rest on "analytic and non-vanishing for almost all primes" with no proof, citation or convergence estimate. Distinct from the already-flagged spectral defects. | AGENT |
| 12 | `:114` vs `:333` | Two values of `m_C` 32 orders apart under one symbol. `Ch12QFTLagrangian.lean` already splits them (`mC_UV_GeV`, `mC_IR_GeV`) and proves the ratio bracket, while declaring the bridging relation open and never proving it for any concrete parameters. The prose uses one symbol for both. | AGENT |
| 12 | `:432`, `:459` | Cross-section `2.84 × 10⁻¹²` pb vs stated `10⁻¹⁵`; fringe spacing `6.2 cm` vs stated `10 μm` (factor ~6200). | AGENT |
| 13 | `:213–217` | Inside the 2026-10-03 correction's *own added text*: `ħ/(Mc·r_s²)` carries units of 1/length — the very defect the block calls out in the old text — and gives `2.03 × 10⁻⁸⁰`, not `10⁻⁴⁰`; the dimensionless candidate gives `2.99 × 10⁻⁷⁷` and scales as `1/M²`, not `1/M`. | AGENT |
| 28 | `:404` | `ℓ ∼ 95 × (1100/0.95) ∼ 10⁵` is arithmetically self-consistent but has no derivation anywhere. | AGENT |
| 01 | `:976–977` | `max D₃ ≈ 13` and `≈ 25` are both exactly 1 high (true: 12, 24), against the chapter's own exact `max = 2k` proved two pages earlier. Same direction, same amount — a convention, not two typos. | AGENT |
| 34 | `:793` | A 16-digit decimal for the full Mayer trace sits beside "kernel-checked", but the cited theorems prove summability and convergence plus the `K=1` closed form — not that decimal. The value is numerically right; the placement drops the hedge ch34 uses elsewhere. | AGENT |
| 04 vs 06 | `04:641` vs `06:661` | Bacteria at `ch₂ ≈ 0.3` ("mechanical") in ch04, used as the canonical **proto-conscious** example in ch06's own `0.5–0.95` row. | AGENT |
| 33/34/35 | — | `PRISTINE`/`pristine_gate.sh` appear **nowhere** in the three chapters that tell the reader what is verified. Their "zero axioms / zero sorry" standard covers gate criteria (a)–(c) and is silent on (d) unused binders and (e) non-vacuity — narrower than the project's own bar, and the gap is not flagged. | AGENT |

## S4 and cosmetic

| Ch | Site | Finding | Verified |
|---|---|---|---|
| 23 | `:309`, `:357` | `thm:ym-measure-exists` and `thm:mass-gap-ym` state the Clay clauses verbatim under `theorem`, which the Millennium rule forbids. Substantively retracted by the chapter's own notes; the labels were never changed. | VERIFIED |
| 03 | `:416–434` | "All computations show agreement with theoretical predictions" is stale — the chapter's own 2026-08-06 correction refutes the RH-resonance theorem using that same `N = 50,000` regime, with nonzero values the audit reproduced to 4 digits at `N = 4 × 10⁶`. | AGENT |
| 03 | `:317–323` | An unlabelled `theorem` + `proof` restating the `πα/10` claim the chapter's ledger files as EMPIRICAL/OPEN; the ledger addresses only the `observation` two pages earlier. | AGENT |
| 06 | `:499–503` | Displayed `W²` has `0` where the off-diagonal is `0.18`. Final `ch₂ = 0.50` unaffected (only `Tr(W²)` and `‖W‖_F²` are used). | AGENT |
| 12 | `:195` | `4!/(2!)⁴ = 1.5`, not the asserted `3`. The value 3 is the right pairing count; the formula should be `4!/(2²·2!)`. | AGENT |
| 05 | `:131` | "Recall from Chapter 4 … zero-energy emergence points where counter-rotating vortices meet" — ch04 contains no vortex or emergence-point material (untruncated grep). | AGENT |
| 04 | `:398` | `ℤ[1/3]` called "dyadic rationals base-3"; dyadic means base-2. Lean's own comment says "3-adic". | AGENT |

---

# 3. Corrections to the audits themselves

Three agent claims were **downgraded or corrected** by my own verification. Recorded because the pattern matters more than the instances: an audit's severity judgement needs checking as much as its arithmetic.

1. **ch22's "mathematical impossibility" was not one.** The audit reported
   "eigenvalues purely imaginary" as impossible for a real traceless `3×3`.
   A pure rotation satisfies it. The honest finding — satisfiable but underived,
   and equivalent to `det = 0 ∧ ch₂ ≤ 0` — is *more* useful, because the second
   condition turned out to be the chapter's own physics.
2. **ch17's "C is the zero operator" needed attribution.** The audit attributed
   the empty domain to the boxed definition at `:446`, which integrates over the
   critical line. The defect is that the chapter carries **two** definitions and
   ch18 uses the other one. `C` is not zero outright.
3. **ch16/17/18's "every ch₂ value exceeds the bound" overstated the coupling.**
   The clinical chapters use digital-sum and band-ratio constructions, not ch06's
   matrix formula, so `ch2Matrix_le_half` does not directly bind them. The real
   finding is the unbounded band-ratio formula and the `N ≥ 2` cap — different
   defects with the same flavour.

Earlier in the same campaign a report claimed two ch27 error bars were "outside
either stated error bar" when the intervals overlap. Four downgrades across the
campaign, all in the direction of over-severity.

---

# 4. Pattern notes

**The dominant defect class is not arithmetic — it is a correction that stopped
one line short.** ch29:442, ch13:325, ch34's P1 table, ch23's UV-suppression
claim, ch06's Bell-state witness and ch17/18's missing backport are all the same
shape: the defect was found, written down correctly, and the dependent sentence
three lines away was left standing. Two of those were created by *this
campaign's own* correction passes. Any future pass should finish by grepping the
chapter for the corrected quantity and checking every restatement.

**`ch₂` is at least five different quantities.** The Chern–Weil bundle density
(renormalised to `[0,1]`), the matrix trace formula (range `[−1/2, 1/2]`), the
entanglement form `1 − Tr(ρ_A²)` (`≤ 1 − 1/d`), ch04's
`Tr(C²ρ)/Tr(ρ)`, and ch31's unbounded band ratio. All five converge on one
`0.95` threshold. ch06's own reconciliation note lists three of the five and
repeats an error about one of them. **This is the single highest-leverage
authorial decision in the book**, because the threshold appears in a dozen
chapters and at least three of the five candidate quantities cannot reach it.

**Where the book is strong.** ch02 showed no uncorrected defects across three
dated corrections, all independently re-derived. ch13's four 2026-10-03
corrections are arithmetically sound. ch33 and ch35's corrections all recompute
exactly. ch17's compact-operator theorem states `λ_n → 0` **correctly**, which is
what makes ch21's error a local defect rather than a systemic
misunderstanding. The two-anchor cascade files and the 25-file r183–r209 arc all
exist as cited, with no `sorry` and no vacuous Props. Git hashes cited in ch34
all resolve. The kernel-verified/empirical/asserted distinction is maintained
accurately wherever it appears.

---

Author: Pablo Cohen + Claude Opus 5. 2026-10-05.
