# Style charter — standalone Glimm/UHF formalization paper

Goal: a mainstream operator-algebra + formal-methods paper (target: ITP/CPP or
J. Automated Reasoning) that reads like it was written by one careful working
mathematician. The big goal: this paper is the credential stone — it must be
unimpeachable both mathematically and stylistically.

## Voice and structure
- Prose-first. Bullets only where a list is genuinely a list (e.g. the axiom
  triple, the file inventory). If a paragraph can carry it, a paragraph does.
- One narrator, consistent register: measured, concrete, slightly dry. "We"
  (editorial) is fine; enthusiasm is not. No "remarkably", "crucially",
  "notably", "interestingly", "elegant", "beautiful", "novel" as self-praise.
  The reader decides what is remarkable.
- Vary sentence length naturally. Kill any run of same-shaped sentences.
- No narration-of-the-paper padding ("In this section we will..."). One short
  roadmap paragraph at the end of the introduction, nothing else.
- Transitions earn their place: a new paragraph starts because the mathematics
  moves, not because a connective was available.

## The story IS the voice — keep these real beats, told plainly
1. Why faithfulness is the hard property (closed conditions transfer by
   density; an implication does not).
2. The false summit: the residual that turned out to be the goal restated
   (the TFAE), told as what it was — a wrong turn that produced the honest map.
3. Kadison–Schwarz avoided: the scalar 2-norm contraction fell to a three-line
   finite Cauchy–Schwarz once the target was scalar, not operator.
4. CP-map norm theory absent from mathlib — and unnecessary: the isometry
   decomposition E B = (1/3) Σ W_t* B W_t gives the operator-norm bound from
   submultiplicativity and the C*-identity alone.
5. The classical dependency inverted: faithfulness proved directly, simplicity
   obtained as the corollary — the opposite of the textbook order.

## Claims discipline (unchanged from the reviewed paper)
- Every mathematical claim maps to a named kernel-checked declaration or is
  explicitly classical-by-reference.
- E_k is a "level-k expectation map" (retraction properties only); the full
  conditional-expectation API (positivity, bimodularity, idempotence) is
  explicitly NOT formalized. "Conditional expectation" only as flagged shorthand.
- Priority: "to the best of our knowledge, after searching mathlib, the Coq
  opam archive, and the Isabelle AFP..." — once, in related work, with the
  non-exhaustive caveat. Do NOT repeat the priority claim verbatim elsewhere;
  restate weaker or not at all.
- Numbers (jobs, HEAD, axiom triple) only from verified builds.

## Provenance (integrity over concealment)
- Do not hide the origin; contain it. One matter-of-fact sentence, once, e.g.:
  "The formalization grew out of a larger exploratory project; the results
  presented here are self-contained and depend on none of that project's
  conjectural content. Lean identifiers retain their original names
  (e.g. `TimelessFieldCompletion` for the completion); these are names,
  nothing more."
- No PF framing anywhere else: no "substrate", no r-numbers in prose (cite
  Lean file/declaration names instead), no Millennium problems, no physics,
  no consciousness, no transfer-operator companion section.

## Anti-slop tells to actively avoid
- No em-dash chains; no "not X, but Y" rhetorical scaffolding more than once.
- No paragraph that ends by summarizing itself.
- No list of three where two or four are the truth.
- No "This demonstrates/showcases/highlights". State the fact.
- Acknowledgments: mathlib community, one line. No effusion.
- Title: plain and specific. e.g. "A machine-checked construction of the
  3^∞ UHF algebra with its unique faithful trace" — no colons-with-slogans.

## Mechanics
- amsart, abstract before \maketitle, \texorpdfstring for math in title,
  text-only short titles for any heading with math. Bibliography: only works
  actually cited; the operator-algebra classics (Glimm 1960, Bratteli 1972,
  Powers 1967, Davidson, Takesaki, Blackadar) + Lean/mathlib/ITP references.
- 10–14 pages. Shorter than the corpus paper; density over coverage.
