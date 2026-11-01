# RETRACTION — two claims in my commit messages of 2026-11-01 were false

Written 2026-11-01. Neither claim appears in the manuscript, so neither can be
corrected by editing the book; they are retracted here and in the commit message
of the repair commit.

## R1 — "This closes the pi/10 origin question book-wide" (commit 2eec28d3)

**FALSE.** The commit enumerated four mutually inconsistent origin stories for
the "10" in pi/10 (decimal notation at ch07:95-101; a 10-bin entropy optimum at
ch07:132-141; the base-3 numeral 10_3 at ch09:255; the self-similarity scale
ell_Phi at ch10:220), plus two false derivations (the integral identity at
ch09:430 and the polylogarithm expansion at ch07:121), reported all six as
repaired, and declared the question closed book-wide.

A later eight-agent sweep found **two more, in ch03, both twins of defects that
same commit's chapter had just had repaired**:

* `ch03:352` — an `observation` stating
  `lim_{alpha -> alpha_c} R_f(alpha, s_c)/(alpha - alpha_c) = (pi/10) * xi(alpha_c, s_c)`
  "where xi is a resonance coefficient depending on the specific phenomenon".
  This is the same unconstrained-factor vacuity as the ch07:105 theorem repaired
  in c8aaabe5 — an unconstrained factor absorbs any constant, so the equation
  defines xi and constrains nothing about pi/10. It is **worse** than ch07's
  was: the numerator is `R_f(alpha, s_c)`, not the difference, so the limit
  diverges unless `R_f(alpha_c, s_c) = 0`, which the chapter never asserts.

* `ch03:370` — a `theorem [Polylogarithm Evaluation]` stating
  `R_f(alpha,1) = Li_1(e^{i pi alpha}) * Phi(alpha) = pi*alpha/10 + O(alpha^2)`.
  This is the same false Taylor-in-the-variable form that c8aaabe5 withdrew from
  ch07:121 as "false in form", with the identical logarithmic blow-up at the
  expansion point: `R_f(alpha,1) -> sum 1/n = infinity` as `alpha -> 0`, since
  `sigma(0) = 1`.

* `ch03:386` — sources the 1/10 to "Detailed Fourier analysis (Chapter 4)".
  Measured: `chapters/ch04_timeless_field.tex` contains **zero** occurrences of
  "fourier" (case-insensitive), zero of "/10", zero of "{10}", and zero of
  "0.314". The pointer leads nowhere.

So there were **six** claims, not four. The error: I asserted a book-wide
property after sweeping four chapters, which is the same
verified-the-site-not-its-siblings failure the commit itself was repairing.

**Provenance note, in ch03's favour.** The corpus had already adjudicated ch03's
*status* correctly — `codex/MANUSCRIPT_READING_LEDGER_2026-10-07.md` records
"ch03: pi/10 filed EMPIRICAL / OPEN ... and ch03 is the chapter that is right" —
and ch03:399 and ch03:520 do carry that filing. So this is **not** a downgrade
target. The ledger layer is correct; the displayed observation, the displayed
theorem, and the Chapter-4 pointer are what need repair. That repair is an
authorial change to another chapter's stated results and is left for Pablo's
word rather than taken unilaterally.

## R2 — "'Derivation from Polylogarithms' now occurs 0 times in the book" (commit c8aaabe5)

**True case-sensitively only.** `ch07:861`, the chapter's own verification-status
ledger, names the retired box by its old title in lowercase, and additionally
still rated the derivation "heuristic" when the same commit had established it
is false in form — so a reader consulting only the ledger would have come away
with the weaker verdict.

My own standing rule, recorded in memory as `feedback_absence_needs_naming_sweep`,
is that a grep's silence is a fact about the grep. I used a case-sensitive one to
support an absence claim.

Repaired in the book: the ledger now records the derivation as false in form and
withdrawn, states that the `pi` IS derived (chain rule on `e^{i pi alpha D_3(n)}`)
and that only the `10` remains structural (`h(H_3) = 10`). The ASSERTED
(not derived) classification and the theorem's name and label are unchanged — the
verdict is strengthened, not softened.

## Pattern

Both retracted claims are absence or completeness assertions made without a
sweep adequate to support them. R1 asserted completeness over a book after
examining four chapters; R2 asserted absence over a book using a case-sensitive
grep. The arithmetic in the underlying repairs was in both cases correct and is
unaffected.
