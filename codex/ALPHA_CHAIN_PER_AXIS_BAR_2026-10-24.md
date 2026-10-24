# The α-chain, per axis, against the October 1 bar — MEASURED

**Legion, 2026-10-24.** Phase B of Rio's α-chain prompt (version 2), Step 5.
Companion to the Phase A framing corrections committed the same day.

Every row below was read out of the Lean sources with file and line. Nothing
here is inferred from a summary, including my own earlier summaries.

## The bar, stated as two separable halves

`codex/ALPHA_SUPPLIED_VS_DERIVED_2026-10-01.md` sets the standard an axis must
meet for its α to count as derived rather than supplied. It has two halves, and
they fail independently, so they are scored separately:

* **(A) A non-circular forcing equation.** A realisation predicate that does
  *not* mention `α_X`. The reference form is `RealisesP (a) := 0 < a ∧ a ^ 2 = 2`
  — an equation plus a side condition, whose solution set is a single point. The
  anti-pattern is `RealisesX (a) := 0 < a ∧ a = α_X`, which says "a is the value
  exactly when a is the value" and forces nothing.
* **(B) A proved identification.** A machine-checked theorem that the predicate's
  solution *is* the table value, plus a non-vacuity witness so the implications
  downstream are not idle.

A third item is **not** part of (A) or (B) and is tracked separately below,
because conflating it with them is what produced the overclaims Phase A removed:

* **(C) An independent origin for the equation itself** — the equation derived
  from the substrate operator rather than supplied as a hypothesis.

## Result

| axis | (A) non-circular equation | (B) proved identification | (C) equation's origin |
|---|---|---|---|
| **P** | ✓ `0 < a ∧ a² = 2` — `CrossMillenniumImplicationChains.lean:50` | ✓ proved, but gated behind an idle hypothesis — `reverse_chain_YM_pins_P_value`, `CrossMillenniumReverseChains.lean:80`; witness `:247`. See the framing note below. | OPEN — supplied |
| **Hodge** | ✓ `1 < a ∧ a² = a + 1` — `CrossMillenniumImplicationChains.lean:66` | ✓ `chain_Hodge_self_realises` → `φ` — `:187` (root separation by `nlinarith`, not `unfold`); restated in the capstone at `:260`; **no non-vacuity witness located** | OPEN — supplied |
| **Poincaré** | ✓ `0 < a ∧ a² = 1` — `PoincareAnchorForced_r338.lean:88` | ✓ `poincare_forced` → `1` — `r338:98`; witness `r338:148`; **negative control** `r338:141` | OPEN — stated so in `r340` Not-claimed 1 |
| **NS** | ✓ `0 < a ∧ 2a = 3π` — `NSAlphaFromH3ExponentSum_r340.lean:111` | ✓ `NS_forced` → `3π/2` — `r340:114`; uniqueness `:118`; witness `:124` | OPEN — stated so in `r340` Not-claimed 1 |
| **YM** | ✗ circular `0 < a ∧ a = α_YM` — `:53` | **forced from P**: `chain_P_implies_YM : RealisesP aP → RealisesYM (aP²)` — `:80`, consumes `hsq` | inherits P's |
| **RH** | ✗ circular `0 < a ∧ a = α_RH` — `:62` | **forced from Poincaré**: `alpha_RH_from_poincare_datum` — `r338:134`, via `poincare_forced` | inherits Poincaré's |
| **BSD** | ✗ circular `0 < a ∧ a = α_BSD` — `:59` | **forced from NS, but from the CIRCULAR NS predicate**: `chain_NS_implies_BSD : RealisesNS aNS → RealisesBSD (aNS/2)` — `:171` | **BROKEN — see below** |

### Reading the table honestly, in both directions

**Better than the blanket line suggests.** The October 1 accounting's finding —
that the *invariants* were read off the values they force — is true and Phase A
has now stopped three files from claiming otherwise. But the *realisation
predicates* are a second, stronger apparatus, and on four axes they are not
circular at all: **P, Hodge, Poincaré and NS each have an equation that never
mentions its α, together with a machine-checked proof that the equation pins the
table value.** Two more axes, **YM and RH**, are then forced from those anchors
by implications that genuinely consume their hypothesis (`chain_P_implies_YM`
rewrites with `hsq`; `alpha_RH_from_poincare_datum` goes through
`poincare_forced`). A summary that says only "the α-values are read off the
table" understates the Lean content on six of seven axes.

**Worse than the headlines claimed.** Column (C) is OPEN everywhere. No axis
derives its forcing equation from the substrate operator. `r340` says this
plainly in its own Not-claimed list, and `H3CoxeterOrigin.lean:300` says its
results are "arithmetic identities between stipulated rationals, NOT derivations
of α_RH, α_NP from group" structure. So the chain is **non-circular but
root-supplied**: given the four root equations, six axes follow; the four root
equations are premises.

### A framing note on the P identification (reported, not changed)

The theorem that pins `√2` is stated as

```lean
theorem reverse_chain_YM_pins_P_value :
    ∀ {aYM : ℝ}, RealisesYM aYM → ∀ {aP : ℝ}, RealisesP aP → aP = Real.sqrt 2
```

and its proof opens `intro aYM _` — the YM hypothesis is **discarded unused**.
So the content actually proved is the stronger, unconditional
`RealisesP aP → aP = √2`, but the statement gates it behind `RealisesYM`, which
is the circular predicate. This is an **under**claim, not an overclaim: the
file proves more than it states, and it needlessly makes the P axis's
identification look dependent on a circular premise.

Per the job's guard this is reported, not restated — no theorem statement is
changed here. The fix is to state the unconditional form alongside it, which is
an addition and belongs with the BSD bridge lemma below.

## The one broken link, and its repair

**BSD is the only axis whose forcing chain is rooted in a circular predicate.**

`r340` built the non-circular NS predicate `RealisesNS_forced (a) := 0 < a ∧
2a = 3π` and proved `NS_forced : RealisesNS_forced a → a = 3π/2`. But
`chain_NS_implies_BSD` still takes the **old, circular** `RealisesNS`, so BSD's
forcing is rooted in `a = α_NS` and the H₃ work does not reach it. Nobody
re-pointed the chain at the new root when `r340` landed.

The repair is one lemma:

```lean
theorem realisesNS_of_forced {a : ℝ} (h : RealisesNS_forced a) : RealisesNS a
```

Both conjuncts are immediate — positivity is the first component of `h`, and
`a = α_NS` is `NS_forced h` composed with `α_NS = 3 * Real.pi / 2`, which is the
literal definition. Composing it with `chain_NS_implies_BSD` roots BSD in the
H₃ exponent datum, taking the chain from six axes to seven.

This is an **addition of a theorem**, so it is out of scope for the α-chain job,
whose guard is absolute: *no theorem statement and no proof body is changed.*
It is filed here as the single next action rather than done silently.

## What (C) would take, priced

Closing column (C) on even one axis means deriving a root equation from the
substrate rather than supplying it. The two H₃ axes share one bottleneck, and
`H3CoxeterOrigin.lean` states it without hedging: it does not prove the
framework's `H_α` operator inherits the H₃ Coxeter structure. That single
proposition is the common root of both the Poincaré route (Coxeter number
`h(H₃) = 10`) and the NS route (exponent sum `Σ{1,5,9} = 15`). It is one
proposition, not a programme, and it is the highest-leverage open item in the
α-chain — closing it would move two axes from "root-supplied" to "root-derived"
at once.

`r340` also records a strictly smaller item: the exponent *list* `[1,5,9]` is
entered as data rather than computed from the Coxeter diagram, and notes that
mathlib carries Coxeter-group theory, so computing it is bounded work rather
than research. That is a real, finishable improvement and it is independent of
the operator question.

## Provenance of this note

All counts and citations re-read from the sources on 2026-10-24 under
`/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code`. Two claims
I made earlier in the session and withdraw here, recorded so they are not
re-derived from the transcript:

1. **"Two incompatible P/NP relations."** False. `alpha_PvsNP` is the P-vs-NP
   *axis* quantity (`= α_Poincare + 1/4 = 5/4`); `α_NP = φ + 1/4` is the *class*
   value. Different baselines, same deficit. The October 1 accounting had already
   flagged exactly this shape of non-contradiction, and
   `H3CoxeterOrigin.lean:255` independently confirms `α_NP := φ + 1/4` as the
   live value.
2. **"`α_BSD = 3π/4` vs `alphaBSD := 1/2` is a contradiction."** Not established.
   `ALPHA_SUPPLIED_VS_DERIVED_2026-10-01.md:133` already reads it as a different
   quantity. The `TuringEncoding` family carries its own α-set, agreeing with the
   canonical table on RH, YM and Poincaré.

Both were manufactured by grepping a codex note for phrases instead of reading
it. The note had adjudicated both.

SPDX-License-Identifier: Apache-2.0
