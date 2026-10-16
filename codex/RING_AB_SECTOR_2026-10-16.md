# Ring/AB sector: it splits in three. One closes conditionally, one has a refuted target, one is genuinely open.

**Date:** 2026-10-16 (Legion, compute on Acer). Conditional mathematics within
Madelung hydrodynamics. No Lean. Verification: `codex/ring_verify.py`.
Labels FACT / ARITHMETIC / JUDGEMENT / OPEN throughout.

**Framing, stated first and not buried.** This is a conditional result about the
**hydrodynamic formulation**. It is **not** a piece of a dynamics derivation —
that question is parked (`WALL1_MINMAX_PARKED_2026-10-16.md`, Pablo's decision).
Nothing here derives the Schrödinger equation, derives `ħ`, or revives the
Nelson route. What it does is finish mapping the one hole that
`WALLSTROM_NODAL_PARTIAL_POSITIVE_2026-10-16.md` §3d left open.

**Headline.** The "ring/AB sector" is not one sector. Separating it is the
result:

| sub-sector | status |
|---|---|
| **A.** excised region in `ℝⁿ` — annulus, ring, hole-in-the-plane | **CLOSED conditionally.** The hole is an idealisation; regularise it and the node returns at the excised point, where the nodal theorem applies. Needs `V = o(1/r²)`. |
| **B.** genuine gauge field — Aharonov–Bohm flux | **TARGET REFUTED.** What is quantized is the *canonical* circulation. `∮mv·dl ∈ 2πħℤ − qΦ/c`, a **shifted** lattice. `(ρ,v)` cannot contain `A`. |
| **C.** intrinsically compact configuration space — rigid rotor on `S¹`, `SO(3)` | **OPEN**, and A's mechanism is structurally unavailable. |

So Wallstrom's objection in this sector is one third repaired, one third
misstated, and one third genuinely open — and the open third is smaller and
much more specific than "the ring."

---

## 1. What the nodal note left open — recap

`NODAL.md` §3c proved: `ρ ∈ C^∞` across its own nodal set ⟹ `∮ m v·dl ∈ 2πħℤ`.
§3d conceded the hole: if `H¹` comes from the *domain geometry* with `ρ > 0`
throughout — a particle on a ring, an Aharonov–Bohm geometry — there is no
node, `ρ` is smooth and positive, and §3c says nothing. Non-integer circulation
is then unobstructed by anything in `(ρ, v)`.

That concession is correct **for the configuration space as given**. The
question is whether the configuration space is given.

## 2. Sub-sector A: the hole does not survive regularisation — the repair

### 2a. The mechanism — ARITHMETIC (verified)

Take the stationary axisymmetric radial equation, `f = √ρ`, circulation
parameter `ℓ := m∮v·dl/(2πħ)`:

  `f'' + f'/r − (ℓ²/r²)f = (2m/ħ²)(V−E)f`.

**With `V` bounded near `r = 0`** the right-hand side is subleading and the
general solution of the leading-order equation is `C₁r^{−ℓ} + C₂r^{ℓ}`
(verified). The regular branch is

  `f ∼ r^{|ℓ|}`,  so  **`ρ ∼ r^{2|ℓ|} = (x²+y²)^{|ℓ|}`**.

**So on a simply connected configuration space there IS a node at the origin
whenever `ℓ ≠ 0`** — the vortex core. And then `NODAL.md` §3c applies verbatim:
`(x²+y²)^a` is `C^∞` at the origin iff `a ∈ ℤ₊`, hence

> **`ρ ∈ C^∞` ⟹ `|ℓ| ∈ ℤ₊` ⟹ `∮ m v·dl ∈ 2πħℤ`.**

The physical reading: an annulus with *infinite* walls has no node because the
region containing the node has been deleted. Give the barrier any finite
height and the particle's density extends into it, the node reappears at the
centre, and the nodal theorem bites.

### 2b. Nothing weaker than smoothness will do it — ARITHMETIC (verified)

Checked by direct outward integration of the radial ODE with a finite barrier,
fitting `d log f / d log r` over a decade at `r ∼ 10⁻⁸`–`10⁻⁴`:

| `ℓ` | fitted exponent | error |
|---|---|---|
| 0.5 | 0.499986 | 1.4e−5 |
| 1.0 | 1.000000 | 4.4e−7 |
| 1.5 | 1.500000 | 3.5e−7 |
| 2.0 | 1.999998 | 2.2e−6 |
| 2.5 | 2.499993 | 6.8e−6 |
| 3.0 | 2.999987 | 1.3e−5 |

The exponent tracks `|ℓ|` for half-integers exactly as for integers. **The ODE
does not object to non-integer `ℓ`, and neither does normalisability or finite
energy** (`NODAL.md` §3b: both energy terms converge for any `a > 0`). The
obstruction is smoothness at the origin and nothing else. This matters because
it tells you precisely which hypothesis is load-bearing.

### 2c. The order-of-limits statement — JUDGEMENT (the argument), FACT (closedness of ℤ)

On a simply connected domain with `V = o(1/r²)`, every admissible **smooth**
state has `ℓ ∈ ℤ` (§2a + §2b). The annulus is the `V₀ → ∞` limit of such
problems. `ℤ` is closed in `ℝ`, so any convergent limit of integer-`ℓ` states
has integer `ℓ`.

> **Therefore the annulus's non-integer-circulation states are not limits of
> smooth finite-barrier states. They exist only if the excision is performed
> *before* the physics rather than as a limit of it.**

This is the repair of `NODAL.md` §3d for sub-sector A: the multiply-connected
configuration space with `ρ > 0` throughout is not a state of affairs that any
finite potential produces. It is an artefact of taking a limit first.

### 2d. Exactly where A breaks — ARITHMETIC (verified), and it is a real limit

Substituting `f = r^s` into the radial equation with `V = c/r²` gives the
indicial equation (derived by substitution, **not** from `dsolve`, which
returns a trivial answer here):

  `s² − ℓ² − 2mc/ħ² = 0`,  so  `s = ±√(ℓ² + 2mc/ħ²) =: ±ℓ_eff`.

Smoothness then forces **`ℓ_eff ∈ ℤ`, not `ℓ ∈ ℤ`**. A centrifugal core of
order `1/r²` or stronger shifts the exponent and the conclusion fails.

> **Exact hypothesis: `V = o(1/r²)` as `r → 0`.**

**Three further caveats, stated rather than buried.**

1. **The regularisation is a physical hypothesis, not a theorem of Madelung
   hydrodynamics.** A referee can legitimately say the annulus is a perfectly
   good configuration space in its own right and is not obliged to be a limit
   of anything. I think the hypothesis is the right one — real barriers are
   finite — but it *is* an added assumption, and the result must always be
   stated with it attached. **JUDGEMENT.**
2. The local analysis is for an axisymmetric straight core. At a generic
   excised region the leading local model should still be a power of the
   distance times a smooth positive factor, but that needs a local normal-form
   argument I have not done. **OPEN (technical)** — same gap as `NODAL.md` §3d
   caveat 1.
3. `ρ` vanishing to infinite order escapes the lemma, as before; plugging
   `f = e^{−1/2r}` into the radial ODE forces `V−E ∼ r^{−4}`, excluded by the
   `o(1/r²)` hypothesis. **Consistent, by inspection of the ODE.**

## 3. Sub-sector B: the target is wrong, not merely unproved — ARITHMETIC

With an electromagnetic field, Madelung's velocity is **gauge-covariant**:

  `v = (1/m)(∇S − (q/c)A)`.

Single-valuedness of `ψ = √ρ e^{iS/ħ}` constrains `S`, not `v`:
`∮∇S·dl = 2πħn`, `n ∈ ℤ`. Hence

  `∮(mv + (q/c)A)·dl = 2πħn`,  i.e.  **`∮ m v·dl = 2πħn − qΦ/c`**

with `Φ` the enclosed flux. So the circulation of `mv` lies in a `ℤ`-lattice
**shifted by `−qΦ/c`**, which for generic flux is **not** `2πħℤ`.

**Consequences, and this is the sharpest thing in the note.**

* The quantized object is the **canonical** circulation, which depends on `A`.
  `A` is not a function of `(ρ, v)`. So asking Madelung hydrodynamics to force
  `∮mv·dl ∈ 2πħℤ` in the presence of flux is asking it to produce something
  **false**. The sub-sector is not an unproved case; the target was misstated.
* The correct target — `∮(mv + (q/c)A)·dl ∈ 2πħℤ` — requires data outside the
  hydrodynamic pair. Any derivation in this sub-sector must take the gauge
  field as given, which is a different and weaker claim than the nodal result.
* This is also **why §2's regularisation move does not transfer here.** In AB
  the excluded region is where the solenoid is; letting the particle in means
  letting it into the field, which changes the problem rather than
  regularising it. Sub-sector B resists A's repair for a physical reason, not
  a technical one. **JUDGEMENT.**

**Flag:** the shifted-lattice fact is textbook (it is the Aharonov–Bohm effect).
What is new here is only the observation that it **refutes the target** the
nodal note had set for this sector. The mathematics is not mine.

## 4. Sub-sector C: intrinsically compact configuration space — OPEN

If the configuration space is compact and multiply connected *in its own
right* — the angle of a rigid rotor on `S¹`, or `SO(3)` — then:

* `ρ > 0`, no node, so §2a has nothing to act on;
* there is **no ambient simply connected space to fill in**, so §2c's
  order-of-limits argument is structurally unavailable, not merely harder;
* `H¹(S¹;ℤ) ≅ ℤ` is the right group, and `[θ]` is still an arbitrary point of
  `ℝ`.

So nothing in `(ρ, v)` forces `ℓ ∈ ℤ` here. **This is the genuine residual hole
of the whole Wallstrom lane.** It is much smaller than "the ring": it is
specifically the case of a configuration space that is compact and multiply
connected intrinsically rather than by excision.

**JUDGEMENT on where it would have to be attacked.** `SO(3)` is suggestive —
its double cover is where half-integer values genuinely *do* occur in nature,
so a treatment of this sub-sector would have to explain why half-integers are
admissible there and not elsewhere. That is a feature, not a bug, and it is
also a warning: an argument that forced `ℤ` universally would be *wrong* about
spin. **Not pursued** — flagged as the shape of the remaining question.

## 5. What this buys, and what it does not

**Buys:**
* `NODAL.md` §3d is repaired for the excised-region case, which is the textbook
  ring/annulus and was the headline hole.
* The one hypothesis doing the work is isolated and minimal: `ρ ∈ C^∞` plus
  `V = o(1/r²)` plus "the configuration space is simply connected before
  excision."
* It is now known that neither the ODE, nor normalisability, nor finite energy
  contributes — so there is no cheaper hypothesis to find (§2b).
* Sub-sector B's target is corrected, which prevents a future attempt at
  proving something false.
* The residual is reduced from "geometric `H¹`" to "intrinsically compact
  configuration spaces."

**Does not buy:**
* **Nothing about dynamics.** Gap 2 remains parked; this does not bear on
  wall 1, the Euclidean sign, or the derivation of the Schrödinger equation.
* No derivation of `ħ` — the lattice *spacing* `2πħ` is an input here exactly
  as it was in `WALLSTROM_BASE3_REFUTED` §3. A topological argument fixes the
  lattice, never its scale.
* Not a resolution of Wallstrom's objection in general: sub-sector C is open,
  and the §2 repair rests on a physical hypothesis a referee may decline.
* Nothing is formalised. None of this exists in mathlib and no Lean was
  written, per the order.

**JUDGEMENT on the lane as a whole.** With this note Wallstrom is mapped rather
than closed: conditional quantization in the nodal sector (`NODAL.md`) and in
the excised-region sector (§2), a corrected target in the gauge sector (§3),
and one genuinely open sub-sector (§4). That is a reasonable place to stop, and
I recommend stopping: the remaining sub-sector touches spin and is a different
problem.

---

## Label summary

* **FACT (classical):** the gauge-covariant Madelung velocity and the
  Aharonov–Bohm shifted lattice; `ℤ` closed in `ℝ`; `H¹(S¹;ℤ) ≅ ℤ`; that
  `SO(3)`'s double cover is where half-integers occur.
* **ARITHMETIC (computed here):** the indicial exponents `±ℓ` for bounded `V`;
  the indicial equation `s² − ℓ² − 2mc/ħ² = 0` and `ℓ_eff = √(ℓ² + 2mc/ħ²)`
  for `V = c/r²`, derived by substitution; the fitted exponents in §2b to
  5–6 digits for half-integer and integer `ℓ` alike.
* **JUDGEMENT (mine):** the three-way split of the sector; that regularisation
  of the barrier is the right hypothesis and that it is a hypothesis; the
  order-of-limits argument of §2c; that B resists A's repair for a physical
  reason; that C is the genuine residual and touches spin; the recommendation
  to stop.
* **NOT established:** that nothing forces `ℤ` in sub-sector C — §4 is an
  absence, not an impossibility theorem. Nor that the annulus is an
  illegitimate configuration space; §2 shows only that its non-integer states
  are not limits of regularised ones.
* **Attribution caution:** §2a's indicial analysis and §3's shifted lattice are
  standard (Madelung-hydrodynamics and Aharonov–Bohm literature respectively);
  the smoothness route to Wallstrom carries the same
  rediscovered-not-new flag as `NODAL.md` §3. Primary sources to check before
  any write-up: Wallstrom 1994 and responses; Takabayasi 1952; the
  Madelung vortex-quantization literature; Aharonov–Bohm 1959.

## Method note

The first run of §2b probed `f/r^{|ℓ|}` at `r ∼ 0.2`–`0.6`, where a finite
barrier makes `f` grow exponentially; the ratio climbed five orders of
magnitude and had nothing to do with the exponent, while the script printed
"ratio is finite and slowly varying" beside it. `f ∼ r^{|ℓ|}` is an `r → 0`
statement and must be tested there — the corrected check fits the log-log slope
near `10⁻⁸`. Separately, §2d's `dsolve` call returned the trivial `f = C₁`; the
exponent is obtained by substitution instead, and the script says so. **Third
instance in three days of a harness whose printed conclusion contradicted its
own numbers** — see `feedback_verification_harness_can_lie`. The recurring
error is probing in the wrong regime, which no amount of precision fixes.
