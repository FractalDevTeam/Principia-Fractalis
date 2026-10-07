#!/usr/bin/env python3
# -*- coding: utf-8 -*-
r"""Semantic hygiene gate -- inspects CONCLUSIONS and DEFINITION BODIES.

PF/Audit/PremiseAudit.lean and pristine_gate criterion (d2) police HYPOTHESES:
dead, contained, vacuous premises. Neither looks at what a theorem CONCLUDES. So
a theorem with live hypotheses and a `Prop := True` conclusion is kernel-clean,
gate-green, and says nothing. This gate closes that gap.

DIAGNOSTIC, NOT JUDICIAL. Every finding class carries a REPAIR line naming what
to look for and what the intended theorem probably is. A finding means "the
formalization does not yet say what was intended" -- it is NEVER evidence that
the intended mathematics is false. Nothing is deleted, renamed, quarantined or
downgraded by this tool.

FINDING CLASSES

  hard (block the gate):
    TRUE_BODY            Prop body is definitionally True
    FALSE_BODY           Prop body is definitionally False
    UNIT_CARRIER         quantifies over Unit -- a placeholder domain
    REFLEXIVE            body is `x = x`
    NUMERIC_TAUT         body is a closed numeric identity
    TRICHOTOMY           body is an exhaustive tautology over an order
    ALL_BINDERS_DEAD     every binder underscore-prefixed
    PROOF_IS_OWN_INPUT   proof term is a projection of its own hypothesis
    MODUS_PONENS_SELF    proof applies one hypothesis field to another
    EXTERNAL_NAME_TRIV   named after published mathematics, body trivial

  soft (reported, do not block):
    IFF_RFL_ALIAS        an equivalence closed only by Iff.rfl -- one Prop twice
    DUPLICATE_PROP_BODY  several Props with byte-identical bodies
    CONCL_IGNORES_BIND   conclusion never mentions a bound parameter
    TRUE_VIA_ALIAS       body resolves through a TRUE_BODY definition

PARSING. Declarations are SPLIT first, then parsed one at a time. An earlier
version used a single regex with a DOTALL binder group; it spanned declarations
and misattributed a finding at line 76 to `fractalResonanceTerm` while printing
a body from line 115. Splitting first makes attribution exact.

MODES
  --module PF.X.Y   gate one module; exit 1 on any hard finding
  (default)         whole import closure of PF.lean, summary + detail
  --all-files       every .lean under PF/, in or out of the closure

Read-only. Never modifies anything.

Author: Pablo Cohen + Claude Opus 5. 2026-10-06.
"""
import argparse
import io
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = "/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/PF_Lean4_Code"

NL = chr(10)
OPENERS = "([{" + chr(0x27E8)
CLOSERS = ")]}" + chr(0x27E9)
FORALL = chr(0x2200)
LE = chr(0x2264)
GE = chr(0x2265)
OR = chr(0x2228)
IFF = chr(0x2194)

# Set once per file by the driver; lets TRUE_BODY see whether a
# marker's discharge cites anything (ANCHORED) or not (FLOATING).
_WHOLE_SRC = []

REPAIR = {
    "TRUE_BODY":
        "locate the intended predicate; the name records an intent the body does "
        "not. Two real routes. (1) Replace True with the intended statement -- "
        "this changes what the marker ASSERTS, so it is a theory-meaning decision, "
        "not a mechanical edit. (2) ANCHOR it: make its discharge cite the real "
        "theorem by name, `have _ := <Module>.<capstone>`, so the marker cannot "
        "outlive the content it is named for. Anchoring does NOT clear this "
        "finding -- the body is still True and the marker still asserts nothing -- "
        "it removes the separate defect of resting on nothing at all. An earlier "
        "version of this text offered a third route, declaring the def a "
        "placeholder in its docstring. That was withdrawn 2026-10-07: it was never "
        "implemented (docstrings are stripped before parsing, and the check fires "
        "unconditionally), and a caveat is scaffolding with a removal condition, "
        "not a resolution.",
    "FALSE_BODY":
        "a False body makes every theorem over it vacuous. Either the predicate is "
        "mis-stated (check sign, direction, domain) or it is a deliberate "
        "impossibility marker -- say which in the docstring.",
    "UNIT_CARRIER":
        "Unit is a placeholder domain. Replace with the intended carrier type; if "
        "that carrier does not exist yet, this finding locates the formalization "
        "work required.",
    "REFLEXIVE":
        "an x = x conclusion carries no information. Find the intended two distinct "
        "objects -- usually one side was meant to be an independently defined "
        "quantity.",
    "NUMERIC_TAUT":
        "a closed numeric identity proves arithmetic, not the named claim. Recover "
        "the intended relation between non-identical quantities.",
    "TRICHOTOMY":
        "an exhaustive order tautology. Recover the intended estimate -- usually a "
        "bound with a specific constant was meant.",
    "ALL_BINDERS_DEAD":
        "the statement is not parametric in anything it binds. Either state the "
        "conclusion about the bound parameter's fields, or drop the binders and "
        "admit the theorem is about globals.",
    "PROOF_IS_OWN_INPUT":
        "the theorem returns one of its own hypotheses, so it carries no "
        "information about the framework. Find the intended derivation, or restate "
        "it as the definitional equality it actually is.",
    "MODUS_PONENS_SELF":
        "the hypothesis bundle contains both A and A -> C while the conclusion is "
        "C. Supply A -> C from framework content instead of assuming it.",
    "EXTERNAL_NAME_TRIV":
        "a definition named after published mathematics with a trivial body reads "
        "as a citation of that result. Either formalize the cited statement or "
        "rename so it does not assert it.",
    "IFF_RFL_ALIAS":
        "both sides are the same Prop, so the equivalence closes by Iff.rfl. If an "
        "equivalence between genuinely different formulations was intended, the two "
        "sides need independent definitions.",
    "DUPLICATE_PROP_BODY":
        "several named Props share one body, so theorems relating them are "
        "definitional. If the names are meant to denote different mathematics, they "
        "need different statements.",
    "CONCL_IGNORES_BIND":
        "the conclusion does not mention this parameter, so the hypotheses cannot "
        "be constraining it. Check whether a stronger parametric conclusion was "
        "intended.",
    "TRUE_VIA_ALIAS":
        "resolves through a Prop := True definition. Repair the upstream definition "
        "and this follows.",
}

HARD = {"TRUE_BODY", "FALSE_BODY", "UNIT_CARRIER", "REFLEXIVE", "NUMERIC_TAUT",
        "TRICHOTOMY", "ALL_BINDERS_DEAD", "PROOF_IS_OWN_INPUT",
        "MODUS_PONENS_SELF", "EXTERNAL_NAME_TRIV"}

EXTERNAL = ("Wiles", "Glimm", "Jaffe", "Wightman", "Osterwalder", "Schrader",
            "Coates", "Kolyvagin", "Hardy", "Odlyzko", "Perelman", "Fefferman",
            "Mayer", "Connes", "BerryKeating", "BostConnes", "Voisin",
            "Deligne", "Elliott", "Brun", "Selberg", "Mertens", "Chebyshev",
            "FujitaKato", "BealeKatoMajda", "Leray", "Hopf", "Titchmarsh",
            "Bombieri", "Riemann", "Dirichlet", "Platt", "Buckmaster",
            "StreaterWightman", "GlimmJaffe", "Noether", "Skolem")


def strip_comments(s):
    """Strip Lean block comments (nestable, including docstrings) and line comments.

    Known limitation, measured: a `+/-` inside a string literal opens a phantom
    block comment (1 file in 6373). The failure mode is OVER-stripping, which can
    only hide findings, never invent them -- so counts are a floor.
    """
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if s.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if s[i] == NL:
                out.append(NL)
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find(NL, i)
            if j == -1:
                break
            i = j
            continue
        out.append(s[i])
        i += 1
    return "".join(out)


def module_to_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


IMPORT_RE = re.compile(r"^import\s+(PF(?:\.[A-Za-z0-9_" + chr(39) + r"]+)*)\s*$",
                       re.MULTILINE)


def closure_of(entry="PF"):
    seen, stack = set(), [entry]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        p = module_to_path(mod)
        if not os.path.exists(p):
            continue
        try:
            s = io.open(p, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        for m in IMPORT_RE.finditer(strip_comments(s)):
            stack.append(m.group(1))
    return seen


DECL_START = re.compile(
    r"^(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*"
    r"(def|abbrev|theorem|lemma|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_" + chr(39) + r".]*)",
    re.MULTILINE)


def _depth_scan_for(text, target):
    """Index of the first occurrence of `target` at bracket depth 0, else None."""
    depth, j, n = 0, 0, len(text)
    tl = len(target)
    while j <= n - tl:
        ch = text[j]
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
        elif depth == 0 and text[j:j + tl] == target:
            return j
        j += 1
    return None


def _last_colon_at_depth0(text):
    depth, found = 0, None
    for j, ch in enumerate(text):
        if ch in OPENERS:
            depth += 1
        elif ch in CLOSERS:
            depth -= 1
        elif depth == 0 and ch == ":":
            found = j
    return found


def split_decls(code):
    """Yield (kind, name, line, binders, type_part, body) for each declaration."""
    starts = [(m.start(), m.group(1), m.group(2))
              for m in DECL_START.finditer(code)]
    for i, (pos, kind, name) in enumerate(starts):
        end = starts[i + 1][0] if i + 1 < len(starts) else len(code)
        block = code[pos:end]
        line = code[:pos].count(NL) + 1
        idx = block.find(name)
        after = block[idx + len(name):] if idx >= 0 else block
        cut = _depth_scan_for(after, ":=")
        if cut is None:
            sig, body = after, ""
        else:
            sig, body = after[:cut], after[cut + 2:]
        colon = _last_colon_at_depth0(sig)
        if colon is None:
            binders, typ = sig, ""
        else:
            binders, typ = sig[:colon], sig[colon + 1:]
        yield kind, name, line, binders, typ, body


def norm(s):
    return " ".join(s.split()).strip()


TRICH = [
    re.compile(r"^" + FORALL + r"[^,]*,\s*0\s*" + LE + r"\s*(\w+)\s*" + OR +
               r"\s*\1\s*<\s*0$"),
    re.compile(r"^" + FORALL + r"[^,]*,\s*(\w+)\s*<\s*0\s*" + OR +
               r"\s*0\s*" + LE + r"\s*\1$"),
    re.compile(r"^" + FORALL + r"[^,]*,\s*0\s*" + LE + r"\s*(\w+)\s*" + OR +
               r"\s*0\s*>\s*\1$"),
]

BINDER_NAME = re.compile(r"[({\[]\s*([A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)"
                         r"(?:\s+[A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)*\s*:")
UNIT_QUANT = re.compile(r"[" + FORALL + chr(0x2203) + r"]\s*\(?[^,:()]*:\s*Unit\b")
REFL_RE = re.compile(r"([A-Za-z_][A-Za-z0-9_" + chr(39) + r".]*"
                     r"(?:\s+[A-Za-z0-9_" + chr(39) + r".]+)*)\s*=\s*\1$")
NUM_ID = re.compile(r"^\(?\s*-?[\d/.\s()]+\s*\)?\s*=\s*\(?\s*-?[\d/.\s()]+\s*\)?$")
PROJ_ONLY = re.compile(r"^([A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)"
                       r"((?:\.(?:\w+|[12]))*)$")
MP_SELF = re.compile(r"^([A-Za-z_][A-Za-z0-9_" + chr(39) + r"]*)\.(\w+)\s+\1\.(\w+)$")


def check_prop_def(name, binders, body, true_names):
    b, hits = norm(body), []
    short = name.split(".")[-1]
    if b == "True":
        # ANCHORED vs FLOATING: does anything that discharges this marker
        # depend on content outside this module? Both stay HARD -- the body is
        # True either way -- but the distinction says whether deleting the named
        # content would break the build. Every Wave-family marker was FLOATING
        # before 2026-10-07.
        _anch = re.search(
            r"theorem\s+" + re.escape(name) + r"_holds\b[\s\S]{0,400}?"
            r"have\s+_\s*:=\s*_?root_?\.?[A-Za-z]"
            r"|:= by\n\s+have\s+_\s*:=\s*_?root_?\.?[A-Za-z][\s\S]{0,200}?"
            r"unfold\s+" + re.escape(name) + r"\b",
            _WHOLE_SRC[0] if _WHOLE_SRC else "")
        hits.append(("TRUE_BODY",
                     "body := True (%s)" % ("ANCHORED" if _anch else "FLOATING")))
    if b == "False":
        hits.append(("FALSE_BODY", "body := False"))
    if UNIT_QUANT.search(b) or re.search(r":\s*Unit\b", b):
        hits.append(("UNIT_CARRIER", b[:120]))
    if REFL_RE.search(b):
        hits.append(("REFLEXIVE", b[:120]))
    for rx in TRICH:
        if rx.match(b):
            hits.append(("TRICHOTOMY", b[:120]))
            break
    if NUM_ID.match(b):
        lhs, _, rhs = b.partition("=")
        if lhs.strip() == rhs.strip():
            hits.append(("NUMERIC_TAUT", b[:120]))
    bn = BINDER_NAME.findall(binders or "")
    if bn and all(x.startswith("_") for x in bn):
        hits.append(("ALL_BINDERS_DEAD", "binders: " + ",".join(bn)))
    if any(e in name for e in EXTERNAL) and b in ("True", "False"):
        hits.append(("EXTERNAL_NAME_TRIV", short + " := " + b))
    toks = b.split()
    if toks:
        bare = toks[0].split(".")[-1].strip("()")
        if bare and bare in true_names and b != "True":
            hits.append(("TRUE_VIA_ALIAS", "resolves through " + bare))
    return hits


def check_theorem(name, binders, concl, body):
    c, p, hits = norm(concl), norm(body), []
    bnames = BINDER_NAME.findall(binders or "")

    m = PROJ_ONLY.match(p)
    if m and m.group(1) in bnames:
        hits.append(("PROOF_IS_OWN_INPUT", "proof := " + p))

    if MP_SELF.match(p):
        hits.append(("MODUS_PONENS_SELF", "proof := " + p))

    # An equivalence whose proof contains nothing but Iff.rfl (possibly several,
    # under a refine) is one Prop named twice. Detect by removing every
    # structural token and checking that only Iff.rfl occurrences remain.
    if (IFF in c or "<->" in c) and "Iff.rfl" in p:
        residue = p.replace("Iff.rfl", "")
        for tok in ("refine", "exact", "constructor", "by", "and_iff_left",
                    "Iff.intro"):
            residue = residue.replace(tok, "")
        residue = re.sub(r"[\s?_,;" + chr(0x2022) + chr(0x27E8) + chr(0x27E9) +
                         r"<>()\[\]" + chr(0x3008) + chr(0x3009) + r"]", "",
                         residue)
        if residue == "":
            hits.append(("IFF_RFL_ALIAS", c[:120]))

    # A theorem every one of whose binders is underscore-prefixed is not
    # parametric in anything it binds. This check was originally applied only to
    # Prop definitions, which is why MinimalRigidityForcesAlphaSkeletonMaster-
    # Capstone -- six underscore binders, conclusion about globals -- passed.
    if bnames and all(x.startswith("_") for x in bnames):
        hits.append(("ALL_BINDERS_DEAD", "binders: " + ",".join(bnames)))

    # CONCL_IGNORES_BIND applies only to DATA binders. A first version flagged
    # every binder and fired on 3248 of 14708 theorems -- 22%, not discriminating
    # -- because a HYPOTHESIS binder legitimately does not appear in the
    # conclusion; that is what a hypothesis is. Restricting to data binders (type
    # carries no relation symbol, name is not h-prefixed) makes it meaningful: a
    # theorem that binds an object and then says nothing about it is suspicious.
    RELSYM = ("=", LE, GE, "<", ">", chr(0x2208), chr(0x2227), chr(0x2228),
              chr(0x00AC), IFF, chr(0x2192), "->", chr(0x2260), "Prop")
    for grp in re.finditer(r"\(\s*([A-Za-z_][A-Za-z0-9_" + chr(39) +
                           r"\s]*?)\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)",
                           binders or ""):
        names, btype = grp.group(1).split(), grp.group(2)
        if any(sym in btype for sym in RELSYM):
            continue
        for bn in names:
            if bn.startswith("_") or bn.lower().startswith("h"):
                continue
            if not re.search(r"\b" + re.escape(bn) + r"\b", c):
                hits.append(("CONCL_IGNORES_BIND",
                             "data binder " + bn + " : " + norm(btype)[:40] +
                             " absent from conclusion"))
                return hits
    return hits


def gather(paths):
    true_names = set()
    body_owners = defaultdict(list)
    for mod, full in paths:
        try:
            code = strip_comments(io.open(full, encoding="utf-8").read())
            _WHOLE_SRC[:] = [code]
        except (OSError, UnicodeDecodeError):
            continue
        for kind, name, line, binders, typ, body in split_decls(code):
            if kind in ("def", "abbrev") and norm(typ) == "Prop":
                nb = norm(body)
                if nb == "True":
                    true_names.add(name.split(".")[-1])
                if nb and nb not in ("True", "False") and len(nb) > 30:
                    body_owners[nb].append((mod, line, name))
    dupes = dict((b, o) for b, o in body_owners.items() if len(o) > 1)
    return true_names, dupes


def scan(paths):
    true_names, dupes = gather(paths)
    records, nprop, nthm = [], 0, 0
    for mod, full in paths:
        try:
            code = strip_comments(io.open(full, encoding="utf-8").read())
            _WHOLE_SRC[:] = [code]
        except (OSError, UnicodeDecodeError):
            continue
        for kind, name, line, binders, typ, body in split_decls(code):
            if kind in ("def", "abbrev") and norm(typ) == "Prop":
                nprop += 1
                hs = check_prop_def(name, binders, body, true_names)
                nb = norm(body)
                if nb in dupes:
                    others = [o[2].split(".")[-1] for o in dupes[nb]
                              if o[2] != name]
                    if others:
                        hs.append(("DUPLICATE_PROP_BODY",
                                   "byte-identical to " + ", ".join(others[:4])))
                if hs:
                    records.append((mod, line, name, hs))
            elif kind in ("theorem", "lemma"):
                nthm += 1
                hs = check_theorem(name, binders, typ, body)
                if hs:
                    records.append((mod, line, name, hs))
    return records, nprop, nthm


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--module")
    ap.add_argument("--all-files", action="store_true")
    ap.add_argument("--limit", type=int, default=60)
    # --ledger dumps EVERY finding as TSV. The summary mode caps detail at five
    # per class, which is right for reading and wrong for repair work: a ledger
    # whose purpose is to make each finding locatable must be complete.
    ap.add_argument("--ledger", action="store_true")
    a = ap.parse_args()

    if a.module:
        p = module_to_path(a.module)
        if not os.path.exists(p):
            print("semantic_hygiene_gate: module not found: " + a.module)
            return 2
        paths = [(a.module, p)]
    else:
        cl = closure_of()
        allf = []
        for dp, _dn, fns in os.walk(os.path.join(ROOT, "PF")):
            for f in fns:
                if f.endswith(".lean"):
                    full = os.path.join(dp, f)
                    mod = os.path.relpath(full, ROOT)[:-5].replace(os.sep, ".")
                    mod = mod.replace("/", ".")
                    allf.append((mod, full))
        paths = allf if a.all_files else [(m, f) for m, f in allf if m in cl]

    records, nprop, nthm = scan(paths)
    hard_recs = [r for r in records if any(k in HARD for k, _ in r[3])]

    if a.module:
        print("semantic_hygiene_gate: " + a.module)
        print("  inspected %d Prop definitions, %d theorems" % (nprop, nthm))
        if not records:
            print("  PASS  (f) no conclusion-level or definition-body findings")
            return 0
        for mod, line, nm, hs in records:
            for k, d in hs:
                tag = "FAIL" if k in HARD else "WARN"
                print("  %s  (f) %-19s %s:%d  %s"
                      % (tag, k, mod.split(".")[-1], line, nm.split(".")[-1]))
                print("        " + d[:150])
                print("        REPAIR: " + REPAIR.get(k, ""))
        print("  %s  (f) %d hard, %d soft"
              % ("FAIL" if hard_recs else "PASS",
                 len(hard_recs), len(records) - len(hard_recs)))
        return 1 if hard_recs else 0

    if a.ledger:
        tab = chr(9)
        print(tab.join(["severity", "class", "module", "line", "declaration",
                        "detail"]))
        for mod, line, nm, hs in sorted(records, key=lambda r: (r[0], r[1])):
            for k, d in hs:
                print(tab.join(["HARD" if k in HARD else "soft", k, mod,
                                str(line), nm, norm(d)[:200]]))
        return 0

    cls = Counter()
    for _m, _l, _n, hs in records:
        for k, _d in hs:
            cls[k] += 1

    bar = "=" * 78
    print(bar)
    print("SEMANTIC HYGIENE GATE -- conclusions and definition bodies")
    print(bar)
    print("  modules scanned              %6d" % len(paths))
    print("  Prop definitions inspected   %6d" % nprop)
    print("  theorems inspected           %6d" % nthm)
    print("  declarations with findings   %6d  (%d with a hard finding)"
          % (len(records), len(hard_recs)))
    print("")
    print("BY CLASS")
    for k, n in cls.most_common():
        print("  %-20s %5d   %s" % (k, n, "HARD" if k in HARD else "soft"))
    print("")
    print("DETAIL, grouped by class, hardest first")
    bycls = defaultdict(list)
    for mod, line, nm, hs in records:
        for k, d in hs:
            bycls[k].append((mod, line, nm, d))
    shown = 0
    for k in sorted(bycls, key=lambda x: (x not in HARD, -len(bycls[x]))):
        print("  --- %s (%d) %s" % (k, len(bycls[k]), "HARD" if k in HARD else "soft"))
        print("      REPAIR: " + REPAIR.get(k, ""))
        for mod, line, nm, d in bycls[k][:5]:
            print("        %-50s %s:%d" % (nm.split(".")[-1][:50],
                                           mod.split(".")[-1], line))
            print("            " + d[:120])
            shown += 1
        if len(bycls[k]) > 5:
            print("        ... %d more" % (len(bycls[k]) - 5))
        if shown >= a.limit:
            break
    return 0


sys.exit(main())
