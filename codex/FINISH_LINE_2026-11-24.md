# REFEREE-PROOF FINISH LINE — state at 2026-11-24 EOD

Supersedes `codex/PENDING_LEDGER_2026-11-24.md`. Every number measured today.

---

## THE BOOK SIDE IS COMPLETE

**52 of 52 `.tex` files now carry a verification ledger. Zero without.**
Measured after `035cbf18`:

```
ledgered: 52   without: 0   total: 52
```

Build gate at that commit: `pdflatex` rc=0, **0 `^!` error lines**, **1074
pages**, **Reference undefined 0**, 0 "Cannot find file", 3 overfull vboxes with
worst **155.73022pt == the pre-existing baseline**, at the same three pages
throughout. The 478 "Citation undefined" are the recipe's missing bibtex pass,
present before any of this work and unchanged by it.

### What was repaired today, in order

| commit | what |
|---|---|
| `1fffd099` | appA zeros rows 11–20 |
| `d9854747` | ch20 eigenvalue↔zero map restored |
| `a0a85c8b` | **16 drifted `chNN:LLL` citations** + Stage 1's stale "Open content"; shipped `check_book_citation_drift.sh` |
| `5bf83099` | appI/appJ — retired "reproduces Perelman 2026", marked 1-of-5 vacuous Fermat conjunct, fixed appJ's theorem count |
| `045c59ef` | appL — 35 of 52 anchors are `Prop := True`; appK swept clean |
| `7af94e87` | appH — ch₂ band contradiction localised to 0.0099 with a removal condition |
| `da5d224b` | **the fine-structure retraction landed** — `α_EM = R_f(1,2)·π/10` withdrawn |
| `d083abf2` | ch23 Yang–Mills ledger + 5 tasks that asked for the refuted quantity |
| `e583fef0` | my own stale "#46025 in flight" + verified upstream PR status |
| `216e2dd7` | **ch08↔ch10 sub-threshold disagreement resolved** |
| `bfa02f21` | **appC's clinical pipeline proved unable to leave the bottom band** |
| `69786927` | **clinical cohort provenance** + ch30's transposed sens/spec |
| `035cbf18` | the last seven files; **52/52 ledgered** |

### The four findings that matter most

1. **appC's `compute_ch2` is bounded above by `1/(1+e⁵) = 0.00669`.** `F` is
   antisymmetric, so `Tr(F²) = −‖F‖²_F ≤ 0`. None of its three bands above 0.49
   is reachable; a fully awake subject classifies as *Coma/unconscious →
   Intensive support*; its own consent rule (`ch₂ ≥ 0.95`) is unsatisfiable.
   Verified at 8/19/32/64 channels, antisymmetry residual exactly 0.0e+00.
   **The algorithm was deliberately NOT changed** — the fix is a sign
   (`Tr(F Fᵀ)`), but altering a clinical computation is the author's call with
   clinical input, and every band and statistic would need re-deriving. Removal
   condition written in.
2. **The clinical cohort's provenance.** ch30 described 847 patients with CRS-R
   gold standard. The project's own script says: *"Run a 100-patient (20 per
   class) **synthetic** cohort … the closest we can get to simulating the
   847-patient Ch 30 cohort **without real data**."* Now stated. The synthetic
   computability work is real and is credited; the cited papers are correct for
   CRS-R methodology but are **not studies of ch₂**.
3. **ch30's sensitivity/specificity were transposed** against its own confusion
   matrix (which is internally perfect). `TP/(TP+FN) = 422/431 = 97.91%` is
   sensitivity; the theorem said 96.8. Corrected to 97.9/96.6/96.8/97.8. The
   "slight rounding adjustments" note withdrawn — a 1.1-point label swap is not
   rounding.
4. **One structural fact fixed two chapters.** `D₃(n) ∈ ℤ ⟹ R_f(integer α, s) =
   ζ(s)`. That kills ch07's fine-structure chain *and* ch23's resonance zero
   (α=2 is the Yang–Mills assignment), and it is why `ρ(ω) = ζ(1/ω)` has no
   positive real zero — the apparent crossing at ω=1 is ζ's **pole**
   (+99.58 → −100.42 across it).

### Still open on the book, and small

* **appB's `0.7329 GeV` mass gap** — a third figure, matching neither ch23's
  refuted 420.43 MeV nor its 62.3 MeV ceiling, reached by an *irrational* α so
  not automatically killed by ch23's refutation. Flagged `ASSERTED` with a
  removal condition; **needs Pablo's decision** to derive or withdraw.
* **appC's sign fix** — Pablo's call, with clinical input.
* **ch25's abelian 4-fold** label/codimension — figure withdrawn, not replaced.
* appH↔appC scale reconciliation — closes when the normal-waking figure is
  re-measured with an interval, or appC's cut-points are re-derived from its own
  outcome bins (whose 0.70/0.90 edges the 0.74 band edge straddles).

---

## THE LEAN SIDE

```
.lean sources      10,866
.olean built        9,528+
unbuilt             1,338 → 1,335 after transfer, ALL leaf numeric panels
sorry / native_decide / project axioms      0 / 0 / 0   (comment-stripped)
Prop := True        272 comment-stripped (337 raw; 65 was comment inflation)
undisclosed True    4 files, 6 decls — 3 real (Hardy1914 disclosed in companion)
```

**All 1,335 unbuilt modules are leaf panels**: FourierPanels, RiemannXiBox900,
PilotBoxes, one bridge. Zero unbuilt outside them — Numerics 0, YangMills 0,
Referee 0. 180 of 200 sampled have **no importer**: they gate nothing. **The
mathematics is built; what remains is compute.**

### Two machines, split by memory not cores

Acer verified: 12 cores, ~12 GiB available, **pin `v4.24.0-rc1` identical to
Legion** across all 14 trees, mathlib built (6,866 oleans), 1.3 T free, idle.
Its ACTIVE tree holds **7,366 panel oleans** against Legion's 7,363.

Of the 1,362 Legion needed, Acer already had **27** — transferred only where the
`.lean` source hash matched byte-for-byte, because an olean built against a
different source is corruption, not a shortcut.

Split: **Box900 panels stay on Legion** (they peak at 11.9 GiB and Acer has
~12 GiB), **Fourier panels go to Acer** (~4.2 GiB peak). `LEAN_NUM_THREADS=1`
is the OOM control — `taskset` caps CPUs, not process count, and that mistake
previously OOM-killed systemd. Acer's runner carries a 4 GiB floor guard.

### Real mathematics still open — not sweep work

* `localAt` injectivity — would make today's `modular_flow_separates_regions`
  unconditional. **Also a clean mathlib PR candidate.**
* YM's 5 Bochner–Minlos items — a genuine formalization project.
* BSD analytic rank — mathlib has **no** elliptic-curve L-function. Upstream.
* Hodge Voisin R2 — appJ's own scope calls it Fields-medal-grade.
* NS Fefferman (A)/(B); P vs NP V4 substantive = literal Clay P≠NP; RH abscissa
  + universal-*s*.

### Upstream, verified live today

Nothing merged. `#42093`, `#42095`, `#42100` all **OPEN, MERGEABLE, green CI,
`reviewDecision` empty** — nobody has reviewed them. `#42101` and `#46025`
closed without merging. Nothing in the book depends on an upstream merge.

---

## WHAT "REFEREE-PROOF" NOW MEANS, MEASURED

**Internal consistency: reached.** 52/52 ledgered, build clean, every claim
scoped, every citation resolving, every number I could recompute recomputed.
The find-rate across 7,000+ lines swept today was 2.8 defects per 1,000 lines
and the last 2,257 lines yielded two.

**The Clay claims: not reachable, and the book says so in all 52 files.** That
is the defensible position, and it is now uniform rather than patchy.

**Count of my own flags raised and retracted on measurement today: 16.** Each
would have become a false correction. The retraction rate is the gate working.
No number in this ledger should be quoted without its measurement.
