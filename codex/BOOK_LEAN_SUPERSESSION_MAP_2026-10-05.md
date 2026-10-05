# Book–Lean Supersession Map

**Date:** 2026-10-05
**Prompted by:** Pablo's observation that the book was written a year ago and
that the Lean development has since refined parts of it, so some book formulas
are not *wrong* — they are *superseded*.

That observation is correct, it is measurable, and this document measures it.

---

## 0. The distinction this document exists to draw

Two defect classes have been conflated in the repair work so far:

**ERROR.** The book states something the mathematics does not support, and
never did. Example: ch11's muon `g−2`, where the GUT scale was substituted into
a formula whose printed output requires a TeV scale. No version of the corpus
ever supported that pairing. Repair = correct it.

**SUPERSESSION.** The book states what was true, or was the best available
value, at the time of writing. The Lean development then refined it. The book
simply was not updated. Repair = point the book at the refined result, and say
what changed.

These require different notes, and calling a supersession an error
misrepresents the project's history. The corpus did not blunder; it advanced,
and the map did not keep up.

**Methodological rule earned here, to apply to all remaining repair work:**
before labelling a book formula an error, check whether the Lean contains a
refined version of it. If it does, the finding is a supersession.

---

## 1. The principal instance: `λ₀(H_NP)`, and therefore `Δ`

### What the Lean certifies

`PF/SpectralGap.lean` carries the closed forms, and its own docstring marks the
change:

```lean
noncomputable def lambda_0_P  : ℝ := pi_10 / Real.sqrt 2        -- π/(10√2)
noncomputable def lambda_0_NP : ℝ := pi_10 / (phi + 1/4)        -- π/(10(φ+¼))
noncomputable def spectral_gap : ℝ := lambda_0_P - lambda_0_NP

/-- Numerical value of the spectral gap (CORRECTED v3.3.1) -/
theorem spectral_gap_value : |spectral_gap - 0.0539677287| < 1e-8
```

with `lambda_0_NP` certified at `0.168176418230` (`SpectralGap.lean:101`).

### The two value sets

| quantity | superseded (book) | certified (Lean) | change |
|---|---|---|---|
| `λ₀(H_P)` | `0.2221441469` | `0.2221441469` | **none — this was always right** |
| `λ₀(H_NP)` | `0.1330222423` | `0.1681764182` | **+26.4 %** |
| `Δ` | `0.0891219046` | `0.0539677287` | **−39 %** |
| `1/Δ` | `11.2206` | `18.5296` | ch34A already carries the refined figure |

**The supersession is entirely in `λ₀(H_NP)`.** The old `0.1330` was an
empirical spectral-truncation value; the certified closed form
`π/(10(φ+¼))` gives `0.1682`. `λ₀(H_P) = π/(10√2)` is unchanged, so nothing
that depends only on it is affected.

The old empirical value **does not appear in the Lean at all.** It was
corrected at v3.3.1 and the Lean is self-consistent. This is a pure
book-lags-Lean gap.

### The corpus already knew

ch09's own rigor ledger records it:

> **CONDITIONAL REDUCTION (not a proof)** — "P≠NP via spectral gap". The
> theorem's own text is explicit: the conclusion holds only *conditional on*
> the empirical spectral-truncation value `λ₀(H_NP)≈0.1330`, which does *not*
> match the certified closed form `π/(10(φ+1/4))≈0.1682`.

So the discrepancy was identified and labelled. What was never done is
propagating the certified value into the chapters that use the old one.

---

## 2. Incidence: the refinement reached 2 of 12 chapters

Measured by grep over `Principia_Fractalis_master_folder/chapters/*.tex`,
2026-10-05.

### Chapters carrying the superseded `Δ = 0.0891` — **ten**

`ch03_resonance`, `ch07_constants`, `ch09_spectral_unity`,
`ch10_hydrodynamic`, `ch19_physical_applications`,
`ch20_riemann_hypothesis`, `ch21_p_vs_np`,
`ch32_consciousness_quantification`, `ch34_verification`, `ch35_software`

### Chapters carrying the certified `Δ = 0.0540` — **two**

`ch21_p_vs_np`, `ch34A_substrate_theorem`

### Chapters carrying the superseded `λ₀(H_NP) = 0.1330` — **five**

`ch03_resonance`, `ch09_spectral_unity`, `ch21_p_vs_np`,
`ch34_verification`, `ch35_software`

### Chapters carrying the certified `λ₀(H_NP) = 0.1682` — **one**

`ch09_spectral_unity`

### Chapters citing the closed forms symbolically — **none**

No chapter writes `π/(10√2)` or `π/(10(φ+¼))` as the definition. Every chapter
quotes decimals. That is why the refinement did not propagate: there is no
symbolic anchor to update, only scattered numerals.

### Two chapters carry BOTH values

`ch21` has both `Δ` values; `ch09` has both `λ₀(H_NP)` values. Internally
inconsistent, and in ch09's case knowingly so — its ledger says as much.

---

## 3. What changes, and what does not

**Shifts by a known factor.** Claims scaling linearly in `Δ` shift by
`0.605×`. Claims of the form `exp(c·Δ·N)` shift their `N` by `1.651×` — this
is why ch09's quantum-enhancement figure moves from `N ≈ 9.64` to
`N ≈ 15.93` qubits under the certified value. `1/Δ` moves from `11.22` to
`18.53`, which ch34A already records as superseding ch07's old figure.

**Does not change at all.** `Δ > 0` holds under both values, so every claim
resting on the *sign* of the gap rather than its size is untouched. In
particular the structural shape of the P-vs-NP argument is unaffected; what
changes is the numerical gap, not its positivity.

**Does not move any ledger label.** P-vs-NP remains CONDITIONAL REDUCTION, for
the reason ch09's ledger already gives. Propagating the certified value does
not make it PROVEN — if anything it removes an objection, since the chapter
would no longer rest on a value it admits does not match the closed form.

---

## 4. Action list, per chapter

For each chapter below: replace the superseded numeral with the certified one,
cite the closed form symbolically so the next refinement has an anchor, and
recompute any downstream number that scales with `Δ`.

| chapter | superseded value present | downstream recompute needed |
|---|---|---|
| ch03_resonance | `Δ`, `λ₀(H_NP)` | check |
| ch07_constants | `Δ`, and `1/Δ = 11.22` | **yes** — ch34A already supersedes this figure |
| ch09_spectral_unity | both values, knowingly | **yes** — enhancement `N` 9.64 → 15.93 |
| ch10_hydrodynamic | `Δ` | check |
| ch19_physical_applications | `Δ` | check |
| ch20_riemann_hypothesis | `Δ` | check — note ch20's own `Δ=0.08127` is a *different* number again, flagged separately |
| ch21_p_vs_np | both `Δ` values | **yes** — internally inconsistent |
| ch32_consciousness_quantification | `Δ` | check |
| ch34_verification | `Δ`, `λ₀(H_NP)` | check |
| ch35_software | `Δ`, `λ₀(H_NP)` | **yes** — printed eigenvalues are the old pair |

`ch35` deserves note: its printed `λ₀(H_P) = 0.2221441469` and
`λ₀(H_NP) = 0.1330222423` are exactly the superseded pair, and a separate
2026-10-03 correction already established that those values cannot have been
produced by the float64 code in that chapter. Two independent defects on the
same two numerals.

---

## 5. A related open item, NOT the same supersession

`ch20_riemann_hypothesis` quotes a "limiting spectral gap `Δ = 0.08127`" for
critical-line convergence. That is a third number, distinct from both
`0.0891` and `0.0540`, and nothing in the text asserts it is the same constant
as the P-vs-NP gap. It is recorded here so it is not folded into this
supersession by mistake. Settling whether it is the same quantity is an
authorial question.

---

## 6. Why this matters beyond the numbers

The book is the map of the theory — it is where the parts are laid out and
related. The Lean is where individual parts get verified and, in doing so,
sometimes sharpened. When a part is sharpened, the map should be redrawn, and
the mechanism for redrawing it has been informal: whoever noticed, updated the
chapter they were looking at. That is how `ch34A` and part of `ch21` came to
carry the refined `Δ` while ten chapters did not.

The structural fix is the symbolic anchor. If chapters cited
`λ₀(H_NP) = π/(10(φ+¼))` rather than `0.1330`, a refinement to the closed form
would propagate by reference instead of by search-and-replace, and this
document would not have been necessary.

---

*Measured against the live Acer tree, 2026-10-05. Every count in §2 was
obtained by grep today, not recalled.*
