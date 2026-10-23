# Electric Plant separation pass — LITERATURE HALF

**Legion, 2026-10-23.** Assignment: `codex/CONNECT_THE_DOTS_2026-10-22.md`,
Legion item 1 — "from primary literature (not the launch coverage), establish
what plant electrophysiology actually demonstrates today — signal types, what
they coordinate, what decoding has been shown in peer review."

**This memo fills ONE of three columns.** The three-column fit — startup claims
/ literature / the book in 2025 — is deliberately **not** assembled here,
because the book column requires the Acer's verbatim P4 extraction, which is
still running on their side. Per the instruction, the columns are not merged.
Column 2 (literature) is below, graded. Column 1 (startup) is characterised
only as to its evidentiary status. Column 3 is left empty on purpose.

## Grading scheme used throughout

| grade | meaning |
|---|---|
| **ESTABLISHED** | multiple independent peer-reviewed primary sources, mechanism identified, replicated |
| **DEMONSTRATED (narrow)** | shown in peer review, in a specific system or condition, not generalised |
| **REPORTED** | peer-reviewed but single-lab / small-n / lab conditions; figures not independently replicated |
| **PREPRINT** | not peer reviewed; carries no weight in a fit |
| **UNSUPPORTED** | claim in circulation with no peer-reviewed evidence behind it |
| **CONTRADICTED** | a peer-reviewed argument stands against it |

## 1. Signal types — ESTABLISHED

Four electrical signal classes are distinguished in the review literature, by
trigger, propagation and shape:

| signal | trigger | behaviour |
|---|---|---|
| **Local electric potential (LEP)** | humidity, light, temperature change | sub-threshold, stays local, does **not** propagate |
| **Action potential (AP)** | non-damaging stimulus above threshold | all-or-nothing, self-propagating across tissues |
| **Slow wave / variation potential (SWP)** | severe tissue damage | ~7 cm/min through vascular connections; fast (<2 s) depolarisation, slow (>5 min) repolarisation; **magnitude decays with distance from the wound** |
| **System potential (SP)** | herbivore feeding | transient **hyper**polarisation; intensity scales with stimulus severity |

The taxonomy itself is settled. Note the SWP property that matters for any
information claim: **its magnitude decays with distance**, so it is not a
lossless carrier.

## 2. The molecular mechanism — ESTABLISHED

The wound-to-distal-tissue pathway is identified at gene and channel level, by
several independent groups:

- **GLUTAMATE RECEPTOR-LIKE channels are required.** The wound-induced
  electrical signal is *completely abolished* in distal leaves of the
  `glr3.3 glr3.6` double mutant, with consequent loss of jasmonate biosynthesis
  and defence-gene expression. GLR3.1/3.2/3.3/3.5/3.6 feature across the
  genetics.
- **Glutamate is the mobile trigger.** Wounding releases amino acids into the
  apoplast; these activate the Ca²⁺-permeable GLR3.3 as they pass, producing
  membrane depolarisation and a cytosolic Ca²⁺ wave through the plant.
- **Transport is diffusion plus bulk flow**, not an active "nerve."
- **Two glutamate- and pH-regulated Ca²⁺ channels** are required for systemic
  wound signalling; a **mechanosensitive anion channel** is interdependent with
  the GLRs in distal signalling.
- **There is negative feedback.** Ca²⁺/calmodulin-mediated desensitisation of
  GLR channels limits the signal; a CRISPR allele with impaired desensitisation
  shows *prolonged* systemic electrical signalling and Ca²⁺ waves.

**What this is:** a wound-triggered, chemically-gated, decrementing,
self-limiting electrochemical broadcast. **What it is not:** a channel with
addressing, modulation, or demonstrated information content beyond stimulus
class and intensity.

## 3. What the signals coordinate — ESTABLISHED (for defence)

Demonstrated downstream couplings: jasmonic acid accumulation in distal
tissues, proteinase-inhibitor expression, defence (PR) gene activation, and
Ca²⁺ waves. The function for which the pathway is established is **systemic
wound and anti-herbivore defence**. No peer-reviewed demonstration extends it
to a general-purpose signalling channel.

## 4. Discrete, computation-like behaviour — DEMONSTRATED (narrow)

*Dionaea muscipula* is the strongest case and it is genuinely striking:

- One trigger-hair touch fires an AP; the trap closes only when a **second** AP
  arrives **within ~30 s**. Past that window the first is "erased."
- Calcium imaging in transgenic Venus flytrap shows the mechanism: the AP is
  translated into a Ca²⁺ wave, and the closure threshold is only crossed when
  two APs sum in time. Further AP counts gate the digestive program (commonly
  described as counting to five).

**Strength:** a real demonstration of threshold-plus-decay temporal
integration — i.e. short-term state — without neurons. **Scope:** one
specialised organ in one carnivorous species, with the "memory" being Ca²⁺
decay kinetics. It does not generalise to plants at large, and the primary work
does not claim it does.

## 5. Decoding in peer review — REPORTED, and weaker than headline numbers suggest

This is the crux for separating the commercial claim from the science, so it
gets the most careful grading.

**Peer-reviewed classification work exists.** ML applied to plant electrical
recordings (electrome) has been published for abiotic stresses — drought,
salinity, temperature, ozone, osmotic, low light, nutrient deficiency — and
biotic ones including spider mites and caterpillars. Methods span SVM, random
forest, XGBoost, CNN and LSTM; MFCC and wavelet features carry most of the
discriminative weight, with the 0.1–20 Hz band most informative.

**Reported accuracies span an enormous range**, and that range is the finding:

| reported | context |
|---|---|
| 99.29% / 99.19% | stress detection, random forest, best-case single study |
| 90.67% | cold stress (SVM) |
| 80.71% / 80.97% | low light / osmotic stress |
| **70.98%** | **average across all stimuli in that same study** |

A 99% headline and a 71% cross-stimulus average coexist in this literature. Any
claim resting on the former without the latter is cherry-picked.

**Three limits that the fit must carry:**

1. **Classification is not decoding.** What is shown is that recordings
   *separate* by imposed stimulus class under controlled conditions. No
   peer-reviewed work demonstrates recovery of semantic content, or a signal
   vocabulary, from plant electrical activity.
2. **Several hits in this area are preprints, not peer review** (arXiv items on
   ozone phytosensing, water-stress irrigation, "green monitoring systems").
   Graded **PREPRINT**: they carry no weight here.
3. **At least one circulating item is an overclaim marker**: a paper on
   "Environmental and **Emotional** State Classification" from plant
   bioelectrical signals. Plants have no demonstrated affective states; a
   classifier label named "emotional" is an interpretive leap, not a result.
   Graded **UNSUPPORTED** and flagged, not cited as support.

## 6. What the literature does NOT support — and what contradicts it

Two findings here matter more than any positive result, because the corpus's
own standing rules say a failed fit is a result.

**Plant consciousness — CONTRADICTED.** Taiz et al. (*Trends in Plant Science*,
2019) argue plants neither possess nor require consciousness: no neurons, no
brain, and no evolutionary advantage conferred, with physiological function
fully accounted for by genetic and epigenetic adaptation. This is a review
opinion, not an experiment — but it is the peer-reviewed state of the
argument, and nothing in the electrophysiology above requires consciousness as
an explanation.

**"Mother trees signalling offspring through mycorrhizal networks" —
UNSUPPORTED, with a quantified citation pathology.** Karst, Jones & Hoeksema
(*Nature Ecology & Evolution* 7:501–511, Feb 2023) found:

- claims that common mycorrhizal networks are widespread in forests, and that
  resource transfer through them improves seedling performance, are
  **insufficiently supported** — field results vary too widely, admit
  alternative explanations, or are too limited to generalise;
- the claim that mature trees **preferentially** send resources and defence
  signals to offspring has **no peer-reviewed published evidence**;
- **unsupported claims about CMNs have doubled in the past 25 years**, with a
  positive-citation bias obscuring the actual structure and function.

This is directly load-bearing for the pass. The single most culturally
available "plants communicate as a network" claim is, in the primary
literature, an identified *misinformation* pattern — and the mechanism of that
pattern is positive citation bias, which is exactly the failure mode the
program's own grading discipline exists to prevent. **A fit that leaned on the
"wood wide web" would be fitting to a documented artefact.**

## 7. Column 1 (startup) — evidentiary status only

Electric Plant / "Bombadil," Oct 2026: a startup reading plant electrical
signals with ML. Already graded **watch item** on 2026-10-21. Nothing in this
memo changes that: the commercial claims are unverified and no peer-reviewed
output from them is in hand. The separation the assignment asks for is
precisely that **the underlying electrophysiology (§1–4, ESTABLISHED) is not
evidence for any specific product claim**, and the published decoding work
(§5, REPORTED) does not reach semantic decoding.

## 8. Column 3 (the book, 2025) — DELIBERATELY EMPTY

Pending the Acer's P4 verbatim extraction, specifically whether the manuscript
makes claims about communication in plants at all — and the instruction is
explicit that if it does not, that is recorded as "not present" rather than
inferred. I will not grade a fit against a claim I have not read verbatim.

## 9. Standing caution for whoever completes the fit

The honest literature position is narrow and should not be widened in the
fitting:

> Plants have ESTABLISHED electrochemical long-distance signalling, with
> identified channels and genes, that is wound-triggered, decrementing,
> self-limiting, and demonstrated to coordinate defence. One specialised organ
> shows threshold-and-decay temporal integration. Classification of imposed
> stimulus classes is REPORTED with accuracies from 71% to 99%. Semantic
> decoding is **not** demonstrated. Consciousness is argued against in peer
> review. The best-known network claim is a documented citation artefact.

A fit graded against that paragraph can hold. A fit graded against the popular
version of it cannot.

## Sources

Primary and review literature consulted for this memo:

- [Glutamate triggers long-distance, calcium-based plant defense signalling (*Science*)](https://www.science.org/doi/10.1126/science.aat7744)
- [New roles for GLUTAMATE RECEPTOR-LIKE 3.3, 3.5 and 3.6 as on/off switches of wound-induced systemic electrical signals (PubMed)](https://pubmed.ncbi.nlm.nih.gov/26966923)
- [Two glutamate- and pH-regulated Ca²⁺ channels are required for systemic wound signalling in Arabidopsis (*Science Signaling*)](https://www.science.org/doi/10.1126/scisignal.aba1453)
- [Interdependence of a mechanosensitive anion channel and glutamate receptors in distal wound signalling (*Science Advances*)](https://www.science.org/doi/10.1126/sciadv.abg4298)
- [Diffusion and bulk flow of amino acids mediate calcium waves in plants (*Science Advances*)](https://www.science.org/doi/10.1126/sciadv.abo6693)
- [Ca²⁺/calmodulin-mediated desensitisation of glutamate receptors shapes plant systemic wound signalling and anti-herbivore defence (*Nature Plants*)](https://www.nature.com/articles/s41477-023-01578-8)
- [Electrical and calcium signalling in plant systemic defense: from local wounds to global responses (*New Phytologist*, 2025)](https://nph.onlinelibrary.wiley.com/doi/10.1111/nph.70301)
- [Wound-induced systemic responses and their coordination by electrical signals (*Frontiers in Plant Science*)](https://www.frontiersin.org/journals/plant-science/articles/10.3389/fpls.2022.880680/full)
- [Calcium dynamics during trap closure visualised in transgenic Venus flytrap (*Nature Plants*)](https://www.nature.com/articles/s41477-020-00773-1)
- [Positive citation bias and overinterpreted results lead to misinformation on common mycorrhizal networks in forests (*Nature Ecology & Evolution*)](https://www.nature.com/articles/s41559-023-01986-1)
- [Plants neither possess nor require consciousness (*Trends in Plant Science*)](https://plantae.org/opinion-plants-neither-possess-nor-require-consciousness-tips/)
- [Classifying plant electrical signals in response to external stimuli using machine learning (Taylor & Francis)](https://www.tandfonline.com/doi/full/10.1080/27685241.2025.2534470)
- [Common bean under different water availability reveals classifiable stimuli-specific signatures in plant electrome (PMC)](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC10984121/)
- [Machine learning distinguishes plant bioelectric recordings with and without nearby human movement (*Biomimetics*)](https://doi.org/10.3390/biomimetics10110776)
