#!/usr/bin/env python3
"""Generate UNIFIED_THEORY_DEPENDENCY_LEDGER.md from the JSON.

Directive §3: "Human-readable generated from machine-readable."

The markdown is a VIEW. Do not hand-edit it - edit the JSON and re-run:

    python3 scripts/gen_dependency_ledger.py \
        codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.json \
        codex/UNIFIED_THEORY_DEPENDENCY_LEDGER.md
"""
import json, sys, datetime

CLASS_ORDER = ["C1", "C2", "C3", "C4", "C5", "C6", "C7", "BLOCKER"]


def esc(x):
    return str(x).replace("|", "\\|").replace("\n", " ")


def flags_of(n):
    f = list(n.get("flags", []))
    for k in ("circular", "vacuous"):
        if n.get(k) and k not in f:
            f.append(k)
    return f


def main(src, dst):
    d = json.load(open(src, encoding="utf-8"))
    L, cls = [], d["classification_scheme"]["classes"]
    conf = d.get("section3_conformance", {})

    L.append("# UNIFIED THEORY DEPENDENCY LEDGER")
    L.append("")
    L.append(f"**GENERATED FILE — do not hand-edit.** Produced from "
             f"`{src.split('/')[-1]}` by `{conf.get('generator','(generator)')}` "
             f"on {datetime.date.today().isoformat()}.")
    L.append("Edit the JSON and re-run the generator. Directive §3 requires the "
             "human-readable ledger to be generated from the machine-readable one.")
    L.append("")
    L.append(f"- **Central theorem status:** {d['central_theorem_status']}")
    L.append(f"- **Branch:** `{d['branch']}` · **Public HEAD must remain** "
             f"`{d['public_head_must_remain']}` · **NO PUSH**")
    L.append(f"- **Directive:** `codex/UNIFIED_THEORY_PROOF_DIRECTIVE_2026-09-07.md`")
    L.append(f"- **Program:** `{d['program']}` · **Charter:** `{d.get('charter','-')}`")
    L.append("")
    L.append("---")
    L.append("")
    L.append("## CLASSIFICATION — directive §3, seven classes")
    L.append("")
    L.append("| key | class |")
    L.append("|---|---|")
    for k in CLASS_ORDER:
        if k in cls:
            L.append(f"| **{k}** | {cls[k]} |")
    L.append("")
    L.append("Two orthogonal flags travel alongside the class, because they are "
             "defects rather than provenance: `circular` (premise restates or "
             "contains its conclusion) and `vacuous` (conclusion holds by "
             "construction). A node can be both a legitimate open conjecture and "
             "used circularly; one field cannot carry both facts.")
    L.append("")

    # --- §3 conformance ---
    if conf:
        L.append("### §3 field conformance")
        L.append("")
        L.append(f"Required per node: {', '.join('`'+f+'`' for f in conf['required_fields'])}.")
        L.append("")
        L.append(f"- nodes: **{conf['nodes_total']}**")
        L.append(f"- nodes with at least one `unverified` required field: "
                 f"**{conf['nodes_with_unverified_required_field']}** — each is a "
                 f"blocker per §3")
        L.append("")
        L.append(conf["note"])
        L.append("")
    L.append("---")
    L.append("")

    # --- nodes by layer ---
    for lk, lname in d["layers"].items():
        rows = [n for n in d["nodes"] if n.get("layer") == lk]
        if not rows:
            continue
        L.append(f"## LAYER {lk[-1]} — {lname.upper()}")
        L.append("")
        L.append("| id | node | class | flags | file | axioms | closed term | rebuilt | note |")
        L.append("|---|---|---|---|---|---|---|---|---|")
        for n in rows:
            fl = ", ".join(f"**{x}**" for x in flags_of(n)) or ""
            L.append("| {} | {} | **{}** | {} | {} | {} | {} | {} | {} |".format(
                n["id"], esc(n.get("name", "")), n.get("class", "?"), fl,
                f"`{esc(n['file'])}`" if n.get("file") else "—",
                esc(n.get("axioms", "unverified")),
                esc(n.get("closed_term", "unverified")),
                esc(n.get("rebuilt_from_source", "unverified")),
                esc(n.get("note", ""))))
        L.append("")

    # --- joins ---
    L.append("---")
    L.append("")
    L.append("## MISSING JOINS")
    L.append("")
    L.append("| id | from → to | status | note |")
    L.append("|---|---|---|---|")
    for j in d.get("missing_joins", []):
        L.append(f"| {j['id']} | {j['from']} → {j['to']} | **{j['status']}** | "
                 f"{esc(j.get('note',''))} |")
    L.append("")

    # --- credit ---
    if d.get("credit"):
        L.append("---")
        L.append("")
        L.append("## CREDIT COLUMN")
        L.append("")
        L.append("Recording what the corpus got right. A ledger that tallies only "
                 "defects misrepresents the project.")
        L.append("")
        L.append("| # | credit | evidence |")
        L.append("|---|---|---|")
        for c in d["credit"]:
            L.append(f"| **{c['id']}** | {esc(c['claim'])} | {esc(c['evidence'])} |")
        L.append("")

    # --- blockers ---
    L.append("---")
    L.append("")
    L.append("## BLOCKERS")
    L.append("")
    L.append("| id | status | description | owner |")
    L.append("|---|---|---|---|")
    for b in sorted(d.get("blockers", []), key=lambda x: x.get("status") != "OPEN"):
        L.append(f"| {b['id']} | **{b.get('status','OPEN')}** | {esc(b['desc'])} | "
                 f"{b.get('owner','—')} |")
    L.append("")

    # --- risks ---
    if d.get("countermodel_risks"):
        L.append("---")
        L.append("")
        L.append("## COUNTERMODEL RISKS")
        L.append("")
        L.append("Full treatment: `codex/UNIFICATION_COUNTERMODEL_LEDGER.md` (directive §8).")
        L.append("")
        L.append("| id | risk | status |")
        L.append("|---|---|---|")
        for r in d["countermodel_risks"]:
            L.append(f"| {r['id']} | {esc(r['desc'])} | **{r.get('status','LIVE')}** |")
        L.append("")

    # --- tally, recomputed ---
    L.append("---")
    L.append("")
    L.append("## TALLY (recomputed at generation)")
    L.append("")
    counts = {}
    for n in d["nodes"]:
        counts[n.get("class", "?")] = counts.get(n.get("class", "?"), 0) + 1
    nflag = {"circular": 0, "vacuous": 0}
    for n in d["nodes"]:
        for f in flags_of(n):
            if f in nflag:
                nflag[f] += 1
    L.append("| class | name | count |")
    L.append("|---|---|---|")
    for k in CLASS_ORDER:
        if counts.get(k):
            L.append(f"| **{k}** | {cls.get(k,'')} | {counts[k]} |")
    for k, v in sorted(counts.items()):
        if k not in CLASS_ORDER:
            L.append(f"| {k} | (unmapped) | {v} |")
    L.append("")
    L.append(f"Flags: `circular` **{nflag['circular']}**, `vacuous` **{nflag['vacuous']}**.")
    L.append("")
    if d.get("tally", {}).get("note"):
        L.append(d["tally"]["note"])
        L.append("")
    L.append("---")
    L.append("")
    L.append("*Generated from the machine-readable ledger. Nothing in this file "
             "modifies a `.lean` file. Public HEAD `96c71da7`. NO PUSH.*")

    open(dst, "w", encoding="utf-8", newline="\n").write("\n".join(L) + "\n")
    print(f"wrote {dst}: {len(L)} lines, {len(d['nodes'])} nodes")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
