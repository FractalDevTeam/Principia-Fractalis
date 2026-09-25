# r331c CAMPAIGN CHARTER

**Opened:** 2026-09-08 on Pablo's GO. Bounded under directive §9.
**Status:** recon and statement work started. **No elaboration slot taken; both
machines remain on C1.**

---

## 1. PURPOSE AND CLAIM LADDER

The finite-height chain:

    r331c: right-edge / sector control -> principal-log contour evaluation
      -> r331d: count = 1, plus critical-line witness
      -> literal riemannHypothesis_below_15

**Own claim ladder** (directive §9): box → boundary → count → **evaluated** count
→ finite-height RH. **No rung is ever promoted as evidence for global RH or for
unification absent a formal dependency.** The distance between "one rectangle to
height 15" and RH is the whole of RH.

## 2. §9 BOUNDS

| field | value |
|---|---|
| **Ceiling** | 3 weeks wall-clock from elaboration start; harness build capped at 3 days |
| **Stopping conditions** | ceiling hit; **or** a root statement fails read-back twice; **or** the t-ranged reparameterisation of the quadrature machinery proves infeasible; **or** stage C1 (Λ₀ enclosures in t) shows the oscillatory integrand admits no tractable enclosure |
| **Named reusable deliverable** | the card-DAG harness (schema, propagation, type-match script) — reusable by r331d and the book queue — **plus** the t-ranged enclosure machinery, which r331a lacks |
| **Resource** | recon/design/statement work NOW in parallel (Python + drafting, no build contention). Machines only after C1 completes and the gate closes: Acer → r331c/d, Legion → rigidity/sector |
| **Escalation** | exceeding any ceiling auto-pauses and reports to Pablo |

## 3. RECONNAISSANCE — THE STAGED TARGETS ARE REFUTED

`RiemannXiThetaBoxEnclosure_r331a.lean:32-34` names two targets:

    r331c (RIGHT LOW:  closes  Re xi(1+it) > 1/1000)
          (RIGHT HIGH: closes  Im xi(1+it) > 1/20000)

**Both are false as written.** Numerical recon (mpmath, dps=40, 6001 samples,
σ=1, t ∈ [0,15]):

| target | verdict | evidence |
|---|---|---|
| `Re ξ(1+it) > 1/1000` | **FALSE** | `Re ξ` goes negative on `t ∈ [13.99, 15]`; min **−8.06e−4** at t=15 |
| `Im ξ(1+it) > 1/20000` | **FALSE** | `Im ξ(1+0i) = 0` exactly. `ξ(1) = 1/2`, real |

**RIGHT LOW contradicts r331b directly.** r331b proves
`Re ξ(σ+15i) < −1/10000` for σ ∈ [1/2,1]. At the shared corner σ=1, t=15 that
says `Re ξ < −1e−4`, while RIGHT LOW would demand `Re ξ > 1e−3`. The two staged
targets cannot both be goals of the same campaign.

**The recon is cross-validated against landed work.** At (σ=1, t=15) it computes
`Re ξ = −8.059e−4`, independently reproducing r331b's theorem at that corner.
The tool agrees with the kernel where the kernel has spoken.

### What is actually true

| fact | value |
|---|---|
| `Im ξ(1+it) > 0` for all `t > 0` | min **+2.89e−5** near t≈0.0025 |
| `Im ξ(1+it) → 0` as `t → 0`, linearly | `Im ξ ≈ 1.1548e−2 · t` for small t |
| `ξ(1) = 1/2` | exact, real, positive |
| `Re ξ < 0` on `[13.99, 15]` | min −8.06e−4 |
| `arg ξ(1+it)` range | `[0, 2.938]` rad — **never reaches π** |
| crosses the negative real axis | **never** |

**The winding argument does not need a half-plane. It needs the negative real
axis avoided**, so the principal branch of `log ξ` stays continuous along the
edge. That is what holds, and the staged targets were a stronger, false, proxy
for it.

## 4. DRAFT ROOT STATEMENTS — through the gate before any proof work

Gate §H read-back **dispatched**; these are **not frozen** until it returns and
is diffed.

```lean
-- A  right edge, bulk
theorem right_edge_im_pos_bulk :
    ∀ t : ℝ, (1:ℝ)/100 ≤ t → t ≤ 15 → (0:ℝ) < (riemannXiEntire ⟨1, t⟩).im

-- B  right edge, near zero (needs a linear lower bound, Im ~ c·t)
theorem right_edge_im_pos_near_zero :
    ∀ t : ℝ, 0 < t → t ≤ (1:ℝ)/100 → (0:ℝ) < (riemannXiEntire ⟨1, t⟩).im

-- C  the corner, exact
theorem xi_at_one : riemannXiEntire ⟨1, 0⟩ = 1/2

-- D  assembled edge statement — the operationally correct one
theorem right_edge_avoids_neg_real_axis :
    ∀ t : ℝ, 0 ≤ t → t ≤ 15 →
      (0 < (riemannXiEntire ⟨1, t⟩).im) ∨ (0 < (riemannXiEntire ⟨1, t⟩).re)

-- E  r331d target
theorem xi_T15_zero_count_eq_one :
    (∑ ρ ∈ (finite_zeros_rectangle ...).toFinset,
        (analyticOrderNatAt riemannXiEntire ρ : ℂ)) = 1

-- F  final target
theorem riemannHypothesis_below_15 :
    ∀ s : ℂ, 0 < s.re → s.re < 1 → 0 < s.im → s.im < 15 →
      riemannZeta s = 0 → s.re = 1/2
```

**Known open questions on these, to be settled by the read-back:** whether D's
disjunction genuinely suffices for principal-log continuity; whether B's open
condition `0 < t` is workable for a certificate-based proof over a closed
interval; and what the inferential gap from E to F actually contains — **F needs
to know WHERE the zero is, not only that there is one**, and nothing in A–E
supplies that. That gap is the campaign's real risk and is named here, not
discovered later.

## 5. HARNESS — card-DAG at our scale

Per `codex/R331CD_HARNESS_PLAN.md`. Estimated **40–120 cards**, so a JSON file
plus a ~50-line propagation script *is* the system; Prove2Me's platform would
cost more than the campaign.

- **Cards.** One file per statement (`:= by sorry`), one per proof, type-match
  enforced by script.
- **Sketch imports.** Proofs may import unproved cards — the skeleton goes in
  top-down today without paying compile cost for unfinished leaves.
- **Per-card isolated compilation**, chained build **once per milestone**.
- **DAG as shared memory** — state lives in the DAG, not a session's context.
- **Sorry-leakage prevention at our scale:** (i) `#print axioms` per card, never
  RC (gate §B0); (ii) statement-level read-back on every milestone (gate §H);
  (iii) the audited core is fixed in advance — roots A–F plus the milestone
  lemmas — and nothing below it needs auditing.

## 6. SEQUENCE

1. **Root statements** — drafted (§4); read-back dispatched; diff; **freeze**.
2. **Harness build** — 1–2 days, no build contention.
3. **Recon deepening** — stage C1 is the real risk: the t-dependence enters
   through `cos((t/2)log u)` and `sin((t/2)log u)`, so it is **oscillatory where
   r331b's σ-dependence was monotone**. `box_pow_sum_lb/ub` do not transfer.
   Probe whether an enclosure is tractable **before** committing the campaign.
4. **On C1 completion + gate closure** — machines split; elaboration begins.

**Step 1 precedes step 4. Statement work precedes proof work. That ordering is
the lesson r331c has already paid for once today.**

## 7. WARNINGS CARRIED FORWARD

From the r331b staging plan, unchanged and still binding: do not re-render a
parsed rational; `approx` has no lemma for a bare integer literal, and at σ=1 the
factor `q1 = t` lands on integers far more often than anything in r331b, so this
will bite early; one `lake build` per module (now enforced by `a1_v4`'s policy
block); audits from `#print axioms`, never RC; every long-running unit gets a
supervisor.

**Added today:** every consumer carries a non-degeneracy hypothesis. The
`t_lo ≤ t_hi` omission in stage C0 would have permitted green certificates over
zero t-measure. Fixed before elaboration; the module now builds clean.

---

---

## 8. ROOT-STATEMENT READ-BACK — RESULT, AND WHAT IT CHANGED

Gate §H read-back on the six draft roots returned 2026-09-08. **Every checkable
claim it made was confirmed numerically.** The drafts are **NOT frozen**; the
statement set is incomplete and one intended lemma shape is false.

### 8.1 THE CAMPAIGN-CRITICAL FINDING — the top edge lies ON the branch cut

ξ is real on the critical line (Hardy's Ξ), and `t = 15` is past the first zero
at `t ≈ 14.1347`, so `Ξ(15) < 0`. Confirmed to 40 digits:

    xi(1/2 + 15i) = -7.0569795882e-04  +  (-4.83e-45)i      arg = -pi exactly

**`ξ(1/2 + 15i)` is real and negative. The top edge passes through the principal
branch cut.** Any "top edge ∈ slitPlane" lemma is **FALSE**, and the device that
works on the right edge does not transfer.

Argument across the top edge, σ from 0 to 1 at t=15:

| σ | 0 | 0.25 | 0.5 | 0.75 | 1 |
|---|---|---|---|---|---|
| arg ξ | −2.938 | −3.021 | **−π** | +3.021 | +2.938 |

It crosses the cut, and does so exactly at the critical line.

**The constructive fix, supported by the same data:** `Re ξ(σ+15i) < 0` for
**all** σ ∈ [0,1] — max is −7.06e−4 at σ=1/2. So the top edge lies in the open
**left** half-plane, and `−ξ` lies in the right half-plane there. Track the
argument on a rotated branch (`log(−ξ)`), or split at σ=1/2.

**r331b already proves half of this.** `top15_re_lt_neg_1e4` gives
`Re ξ(σ+15i) < −1e−4` on σ ∈ [1/2, 1]; conjugate/functional symmetry extends it
to [0, 1/2]. **The top edge is not new work — it is r331b plus a symmetry step.**

### 8.2 THE HEIGHT CEILING IS 15.54, NOT ~20

On σ=1, `arg ξ(1+it)` first reaches π at **t = 15.54**. Max arg on [0,15] is
2.9383, leaving a margin of **0.2033 rad**.

The right-edge argument budget is ≈ π per zero. **This proof shape works at
T = 15 and fails by T = 16.** Any sequel at greater height needs a different
architecture. Record before anyone plans one.

### 8.3 CORRECTIONS TO MY OWN RECON

- I reported the global min `Im ξ = +2.89e−5` at t = 0.0025 — **below statement
  A's own interval**, so it never certified A. Corrected: **min Im on [0.01, 15]
  = +1.1548e−4, attained at the left endpoint t = 0.01.** A holds, and the
  binding constraint is the near end, not the far end.
- The auditor's independent value `ξ'(1) = ½(1 + γ/2 − ½log4π) = 0.011555`
  matches my recon slope `1.1548e−2` to four digits. Cross-validated.

### 8.4 STATEMENT B IS NOT PROVABLE AS PLANNED — and the fix is clean

`Im ξ(1+it) → 0` as `t → 0`. Any interval-arithmetic certificate over a closed
interval whose closure contains 0 returns a lower bound ≤ 0. **A direct
certificate for B cannot work**, and would have looked like a tooling bug.

Fix: define `η(s) := (ξ(s) − 1/2)/(s − 1)`, entire **because** `ξ(1) = 1/2`
(statement C licenses it). Then

    Im xi(1+it) = t * Re eta(1+it)

so B reduces to `Re η(1+it) > 0` on the **closed** interval [0, 0.01], with
`η(1) = ξ'(1) ≈ 0.0116`. Closed interval, bounded below by a positive constant —
exactly what a certificate wants. **B's public statement stands; its proof
obligation is restated via η.**

### 8.5 THE STATEMENT SET IS ~4 OF ~12

Missing, and now named: bottom edge (σ∈[0,1] at t=0 — ξ real and positive, Δarg
= 0); **top edge** (§8.1); left edge (σ=0, from the right edge by
`ξ(s)=ξ(1−s)` and `ξ(s̄)=conj ξ(s)` — **verify the conjugate-symmetry lemma
exists in Mathlib**); the **argument-principle gluing lemma**, which is the
actual work and which no draft expresses; the **ζ↔ξ bridge** on 0<Re s<1; and
the order ≥ 1 obligation (`analyticOrderNatAt` returns 0 in *two* degenerate
cases).

### 8.6 E ⟹ F NEEDS A LOCATING STEP — confirmed

E gives total multiplicity 1, which is consistent with a single simple zero at,
say, `0.7 + 14.13i`. **E alone does not imply RH in the box.** Two routes:

- **(a) Reflection — preferred, no numerics.** If `ρ = σ+it` is a ξ-zero in the
  box with `σ ≠ 1/2`, then `1 − ρ̄` is a *distinct* zero in the same box, giving
  count ≥ 2 and contradicting E. Needs the functional equation and conjugate
  symmetry — both needed anyway for the left edge.
- **(b) IVT.** `Ξ(14) = +2.01e−4`, `Ξ(15) = −7.06e−4` — confirmed — gives a
  critical-line zero, and E forces uniqueness. Needs realness of Ξ plus two
  certified signs.

### 8.7 INTERVAL ARITHMETIC MUST USE Λ, NOT Λ₀

At `s = 1+15i`: `|s(s−1)| = 225.5`, `|Λ₀| = 4.44e−3`, and `s(s−1)Λ₀ = −1.00161…`
— the `+1` in the Lean definition **cancels ~3 significant digits**. Confirmed.
Analytically `2ξ = s(s−1)Λ` has no cancellation. Any evaluator working from the
Lean definition literally will lose those digits. **Plan the enclosures around
Λ.**

### 8.8 RENAMES REQUIRED BEFORE FREEZE

- **F → `riemannHypothesis_upper_strip_below_15`.** F restricts to `0 < Im s <
  15`; "below 15" reads as `|Im s| < 15`. The lower strip follows by conjugate
  symmetry but that step is not in the statement. **F proves less than its name.**
- **E → `..._multiplicity_sum_eq_one`** — "count" suggests cardinality; the
  statement is a multiplicity-weighted sum. They coincide only via the order ≥ 1
  lemma.
- **D** understates: it is strictly stronger than slitPlane membership. Keep the
  strength, state the slitPlane corollary explicitly so the gluing lemma can cite
  the standard Mathlib predicate.
- **A `_bulk` is misleading** — A's margin is the angular one (0.2033 rad against
  a branch cut) plus a 3-digit cancellation; B has a 4-digit-verified linear
  model and a large margin. The naming has the difficulty backwards.

### 8.9 ONE PINNING HAZARD

`finite_zeros_rectangle ...` is elided in both E and the given identity. If the
arguments — **including the `Set.Finite` proof term consumed by `.toFinset`** —
are not syntactically defeq, E is a *different statement* and the chain breaks
silently at `rw`. **Pin them to a shared `def`/`abbrev` before writing either.**

---

## 9. REVISED STATUS

**Root statements: NOT FROZEN.** The set is incomplete (~4 of ~12), one intended
shape is false (top edge), one is unprovable as planned (B, fixable via η), and
four need renaming. Next iteration drafts the full set, then re-runs the gate.

**What the campaign gained today, before spending a single elaboration slot:** a
false target set refuted, a false lemma shape caught, an impossible certificate
plan corrected, a hard height ceiling established, a numerical-conditioning trap
identified, and the top edge shown to be mostly-already-proved rather than new
work.

**What it cost:** two subagent read-backs and three Python recon passes. No build
contention. Both machines stayed on C1 throughout.

---

*Chartered 2026-09-08. Root statements NOT frozen: set incomplete (~4 of ~12),
top-edge shape refuted, B unprovable as planned. No machine committed.
Public HEAD `96c71da7`. NO PUSH.*
