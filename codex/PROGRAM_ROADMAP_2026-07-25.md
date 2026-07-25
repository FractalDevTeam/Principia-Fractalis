# Principia Fractalis — program roadmap (2026-07-25)

Standing purpose: **scientific rigor and mathematical truth, for the benefit of all
sentient life.** Nothing gets claimed beyond what is verified; everything verified gets
published so others can build on it. Honest labels are not hedging — they are what makes
the work usable by anyone else.

## Track A — mathlib upstreaming (IN FLIGHT, finish first)

| PR | Content | Status |
|----|---------|--------|
| [#42093](https://github.com/leanprover-community/mathlib4/pull/42093) | `TwoSidedIdeal.closure` | Build+Lint green, MERGEABLE, awaiting review |
| [#42095](https://github.com/leanprover-community/mathlib4/pull/42095) | `cfcₙ` into closed two-sided ideals | v4.33 API drift patched (`.id s` + `[Fact]`; no `h0`), re-verify locally then push |
| PR-3 | clopen spectral projections (`ClopenSpectralProjection.lean`) | staged, needs module recipe + v4.33 port |
| PR-4 | r115 zeta-conjugation lemmas (`riemannZeta_conj` et al.) | staged in PF, port is mechanical, standalone |

Local build loop now established (mathlib cache in scratchpad clone) — **verify locally
before every push** rather than using CI as the compiler.

## Track B — the book / corpus (after Track A)

- 36/36 chapters carry honest verification-status ledgers (943 pp, rebuilt 2026-07-23).
- **Open reconciliations surfaced by the ledger pass** (each is a real internal
  inconsistency, worth fixing in the next revision):
  1. `α_NP = π/3` in ch34 verification code vs `φ + 1/4` everywhere else.
  2. ch16 builds `T∞` as a *commutative* ζ-value algebra, contradicting ch04's
     (kernel-verified) *noncommutative* UHF `T∞`. ch04's is the proven one.
  3. ch09: empirical λ₀ = 0.1330 vs closed form 0.1682.
  4. ch07/ch11: `ch₂ = 0.95` derivations carry inline refutations in the text itself.
- **Coq layer**: `PF_Coq_Code/` (738 `.v` files) is a *structural-shape mirror*, not an
  independent verification (the repo README says so). Decide: either upgrade it to real
  independent checking of the r102–r113 arc, or state its status plainly and stop
  implying parity. Rigor says: say what it is.

## Track C — research (continuing, honestly bucketed)

Per `codex/RESIDUAL_TRIAGE_2026-07-23.md`:
- **Bucket 1 (closeable, standard-but-unformalized)** — keep closing these. Done so far:
  r112/r113 (faithful + simple + unique trace = Glimm 3^∞ factor), r114 (retired the r101
  `True` placeholder), r116 (BSD `Re s > 3/2` convergence). Live: the Hardy Route-B
  Xi-witness arc (r115–r119) — Hardy 1914 (**infinitely many zeros ON the line**), which is
  classical and true, and is **not** RH.
- **Bucket 2 (asserted, not derived)** — α_NP = φ+¼ and the α-skeleton. A real derivation
  attempt is worthwhile; per Wave 57 + `AlphaRealizationNoGo` the *pin* is P-vs-NP-equivalent,
  so any success here is a major result and any claim here must stay labeled.
- **Bucket 3 (genuinely open / Clay-hard)** — RH (both Hilbert–Pólya props), P vs NP,
  Navier–Stokes regularity, continuum Yang–Mills, BSD, Hodge. **Serious attempts are
  welcome; claims are not.** The rule that has served this project: attack them, and
  report exactly what the kernel accepts — nothing more.
- **Corroborating-evidence research** — continue, but under the ledger discipline: an
  observation is "consistent with", never "confirms"; a defined-in-range constant is
  DEFINITIONAL, not a prediction.

## The invariant

Every claim ships with its status: PROVEN (kernel) / CONDITIONAL REDUCTION / ASSERTED /
EMPIRICAL-UNTESTED. That is what makes this science rather than assertion, and it is the
only thing that makes it useful to anyone beyond us.
