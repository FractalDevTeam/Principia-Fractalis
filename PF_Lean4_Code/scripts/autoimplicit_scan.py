#!/usr/bin/env python3
"""Detect silent autoImplicit capture of project constants.

A Lean file that mentions a project constant whose declaring namespace it neither
opens nor matches, and does not qualify the name, does not get the constant: with
autoImplicit on (the default, and PF does not disable it) Lean binds the identifier
as a fresh implicit variable. The statement then quantifies over an arbitrary value
of that type while the theorem's NAME goes on claiming the constant.

`PF/YangMillsPerelmanTemplateY1Y4Discharge.lean` was exactly this, and surfaced only
because `unfold alpha_YM_H3U` happened to fail. Where the proof does not unfold, the
file compiles and the defect is invisible. This scan finds those.

Read-only. No builds.
"""
import os, re, sys, json, collections

ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
os.chdir(ROOT)

# Constants worth checking: the alpha family and the H3 Coxeter data. These are the
# ones the framework's numeric claims rest on.
INTEREST = re.compile(r'^(alpha_[A-Za-z0-9_]+|a_[A-Za-z0-9_]+|H3_[A-Za-z0-9_]+|'
                      r'[A-Za-z0-9_]*_H3U|framework_alpha)$')

DECL = re.compile(r'^\s*(?:noncomputable\s+)?(?:protected\s+)?'
                  r'(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_\']*)', re.M)
NS   = re.compile(r'^namespace\s+([A-Za-z0-9_.]+)', re.M)
ENDNS= re.compile(r'^end\s+([A-Za-z0-9_.]+)', re.M)
OPEN = re.compile(r'^open\s+(?:scoped\s+)?(.+)$', re.M)
IMPORT = re.compile(r'^import\s+([A-Za-z0-9_.]+)', re.M)

def strip_comments(s):
    s = re.sub(r'/-.*?-/', ' ', s, flags=re.S)   # block and doc comments
    s = re.sub(r'--[^\n]*', ' ', s)              # line comments
    return s

files = []
for dp, _, fns in os.walk('PF'):
    if 'RiemannXiBox' in dp and 'Panels' in dp:
        continue                                  # panel tier: generated, no constants
    for fn in fns:
        if fn.endswith('.lean'):
            files.append(os.path.join(dp, fn).replace('\\', '/'))

raw = {}
for p in files:
    try:
        raw[p] = open(p, encoding='utf-8', errors='replace').read()
    except OSError:
        pass

# ---- index: constant name -> set of declaring namespaces ---------------------
declared = collections.defaultdict(set)
for p, s in raw.items():
    body = strip_comments(s)
    # track namespace nesting as we scan declarations in order
    stack = []
    for line in body.split('\n'):
        m = NS.match(line)
        if m:
            stack.append(m.group(1)); continue
        m = ENDNS.match(line)
        if m:
            if stack: stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(1)
            if INTEREST.match(name):
                declared[name].add('.'.join(stack))

# ---- per-file resolution check ----------------------------------------------
findings = []
for p, s in raw.items():
    body = strip_comments(s)
    mod = p[:-5].replace('/', '.')
    own_ns = set()
    for m in NS.finditer(body):
        own_ns.add(m.group(1))
    opens = set()
    for m in OPEN.finditer(body):
        for tok in m.group(1).split():
            if re.match(r'^[A-Za-z0-9_.]+$', tok):
                opens.add(tok)
    imports = set(IMPORT.findall(body))

    # unqualified uses of interesting constants
    used = set()
    for m in re.finditer(r'(?<![A-Za-z0-9_.\'])([A-Za-z_][A-Za-z0-9_\']*)', body):
        n = m.group(1)
        if INTEREST.match(n):
            used.add(n)

    for n in sorted(used):
        homes = declared.get(n)
        if not homes:
            continue
        if any(h == '' for h in homes):
            continue                       # declared at root: always resolves
        if n in [d for d in DECL.findall(body)]:
            continue                       # declared in this very file
        # does any declaring namespace resolve here?
        ok = False
        for h in homes:
            if h in opens:
                ok = True; break
            for o in own_ns:
                if o == h or o.startswith(h + '.') or h.startswith(o + '.'):
                    ok = True; break
            if ok: break
        if ok:
            continue
        # qualified somewhere in the file? then the bare uses may still be fine
        qualified = bool(re.search(r'[A-Za-z0-9_.]+\.' + re.escape(n) + r'\b', body))
        findings.append({
            'file': p, 'const': n, 'declared_in': sorted(homes),
            'file_namespaces': sorted(own_ns), 'opens': sorted(opens),
            'also_qualified_in_file': qualified,
        })

print("files scanned (non-panel): %d" % len(raw))
print("interesting constants indexed: %d" % len(declared))
print("potential silent-capture sites: %d" % len(findings))
print()
by_file = collections.Counter(f['file'] for f in findings)
for p, c in by_file.most_common(40):
    consts = sorted({f['const'] for f in findings if f['file'] == p})
    print("%-72s %2d  %s" % (p, c, ", ".join(consts[:6])))
json.dump(findings, open('/tmp/autoimplicit_findings.json', 'w'), indent=1)
print("\nfull findings -> /tmp/autoimplicit_findings.json")
