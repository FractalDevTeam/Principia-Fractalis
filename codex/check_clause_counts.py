#!/usr/bin/env python3
"""Depth-aware top-level conjunct counter for Lean theorem statements.

A naive `grep -c '∧'` cannot tell a top-level join from a wedge nested inside a
parenthesised clause, so a 7-clause bracket bundle (each clause `lo < x ∧ x < hi`)
reads as 13 wedges. This counts ∧ only at bracket depth 0 of the statement.
"""
import pathlib, re, subprocess, sys

BT = pathlib.Path("/home/xluxx/pf-legion-20261120/PF_Lean4_Code")

CLAIMS = [
    ("α_skeleton_master_layer_capstone", 45, "appK:526"),
    ("unified_minimal_forces_tower_of_power", 30, "appK:690"),
    ("moment_sum_hierarchy_capstone", 8, "appK:790"),
    ("framework_empirical_anchor_sharp_bundle", 6, "appK:813"),
    ("α_Hodge_power_tower_ultra_sharp_bundle", 7, "appK:837"),
    ("α_skeleton_log_layer", 8, "appK:458"),
    ("α_Hodge_fibonacci_tower", 8, "appK:559"),
    ("α_NP_Q_phi_tower", 6, "appK:584"),
    ("α_skeleton_scalar_fingerprint_bundle", 7, "appK:675"),
    ("α_skeleton_full_29_identity_locus", 29, "appK:437"),
    ("hodge_six_substrate_classes_all_discharged", 6, "appK:120"),
    ("substrate_rigidity_end_to_end_meta_capstone", 12, "appK:708"),
    ("moment_sum_hierarchy_sharp_capstone", 6, "appK:944"),
    ("tower_of_power_capstone", 30, "appK:616"),
]


def strip_comments(s: str) -> str:
    """Drop nesting /- -/ blocks and -- line comments."""
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        out.append(s[i]); i += 1
    return "".join(out)


def find_decl(name: str):
    """Locate `theorem|lemma|def <name>` and return (relpath, statement text)."""
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
                     r"(theorem|lemma|def|abbrev)\s+" + re.escape(name) + r"\b")
    for f in BT.glob("PF/**/*.lean"):
        try:
            raw = f.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        if name not in raw:
            continue
        src = strip_comments(raw)
        lines = src.split("\n")
        for idx, ln in enumerate(lines):
            if pat.match(ln):
                # statement runs from here to the `:=` that closes it at depth 0
                buf, depth = [], 0
                for ln2 in lines[idx:]:
                    buf.append(ln2)
                    for k, ch in enumerate(ln2):
                        if ch in "([{⟨":
                            depth += 1
                        elif ch in ")]}⟩":
                            depth -= 1
                        elif ch == ":" and depth == 0 and k + 1 < len(ln2) and ln2[k + 1] == "=":
                            return str(f.relative_to(BT)), "\n".join(buf)
                    if len(buf) > 200:
                        break
                return str(f.relative_to(BT)), "\n".join(buf)
    return None, None


def top_level_wedges(stmt: str) -> int:
    """Count ∧ at bracket depth 0, after the statement's leading `:`."""
    # cut the binder/name prefix: start after the first depth-0 ':'
    depth, start = 0, 0
    for i, ch in enumerate(stmt):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == ":" and depth == 0:
            nxt = stmt[i + 1] if i + 1 < len(stmt) else ""
            if nxt != "=":
                start = i + 1
                break
    depth, n = 0, 0
    for ch in stmt[start:]:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "∧" and depth == 0:
            n += 1
    return n


print("   %-44s %-7s %-9s %-9s %s" % ("THEOREM", "CLAIMED", "TOP-LEVEL", "VERDICT", "FILE"))
print("   %-44s %-7s %-9s %-9s %s" % ("-" * 44, "-" * 7, "-" * 9, "-" * 9, "-" * 20))
bad = []
for name, claimed, where in CLAIMS:
    rel, stmt = find_decl(name)
    if stmt is None:
        print("   %-44s %-7s %-9s %-9s %s" % (name[:44], claimed, "-", "NOT FOUND", "-"))
        bad.append((name, claimed, None, where))
        continue
    w = top_level_wedges(stmt)
    conj = w + 1
    ok = (conj == claimed)
    print("   %-44s %-7s %-9s %-9s %s"
          % (name[:44], claimed, conj, "OK" if ok else "MISMATCH", rel.replace("PF/", "")[:30]))
    if not ok:
        bad.append((name, claimed, conj, where))

print("")
if bad:
    print("   === %d to adjudicate by hand:" % len(bad))
    for name, claimed, conj, where in bad:
        print("      %s  (%s claims %s, counter says %s)" % (name, where, claimed, conj))
else:
    print("   === every clause count in appK is CORRECT.")
