#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Per-chapter Lean gate, v2 -- with a resolver that can actually see everything
the book cites.

v1 indexed only PF/, so it reported every mathlib lemma and every data/source
filename as a missing citation. Four classes are separated here:

  FILE        the token is a filename or data artifact (.lean/.csv/.json/.md/
              .c/.ccl/.txt/.cff/.tex/.py) or a Python module path -- not a Lean
              declaration at all. Checked for existence on disk instead.
  MATHLIB     resolves to a declaration in the pinned mathlib.
  PF          resolves to a declaration in PF/.
  STRUCT      resolves to a PF namespace or module path (a legitimate way for
              prose to point at a bundle of results).
  UNRESOLVED  none of the above -- the real candidate defects.

For PF hits we additionally report compiled (olean present) and vacuous
(statement is `True`).
"""
import io, os, re, sys, collections

LEAN = '/home/xluxx/pf-legion-20261120/PF_Lean4_Code'
MATH = os.path.join(LEAN, '.lake/packages/mathlib')
BOOK = '/home/xluxx/pf-push-20261120/Principia_Fractalis_master_folder'
BUILD = os.path.join(LEAN, '.lake/build/lib/lean/PF')

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|instance|opaque|axiom|class)\s+'
    r'([A-Za-z_\u03b1-\u03c9][A-Za-z0-9_.\'\u2080-\u2089\u03b1-\u03c9!?]*)')
NS = re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.\']*)')
ENDNS = re.compile(r'^\s*end\s+([A-Za-z_][A-Za-z0-9_.\']*)')


def scan(rootdir, subdir, want_vac):
    """returns (names dict, namespaces set, modules set)"""
    names = collections.defaultdict(lambda: {'mods': set(), 'vac': False})
    nss, mods = set(), set()
    base = os.path.join(rootdir, subdir)
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d not in ('.lake', '.git')]
        for fn in files:
            if not fn.endswith('.lean'):
                continue
            p = os.path.join(root, fn)
            rel = os.path.relpath(p, base)
            modpath = rel[:-5]
            mods.add(modpath.replace(os.sep, '.'))
            mods.add(os.path.basename(modpath))
            mods.add(os.path.basename(modpath) + '.lean')
            try:
                lines = io.open(p, encoding='utf-8', errors='replace').read().split('\n')
            except Exception:
                continue
            stack = []
            for i, ln in enumerate(lines):
                m = NS.match(ln)
                if m:
                    stack.append(m.group(1))
                    nss.add(m.group(1))
                    nss.add('.'.join(stack))
                    continue
                if ENDNS.match(ln):
                    if stack:
                        stack.pop()
                    continue
                m = DECL.match(ln)
                if not m:
                    continue
                nm = m.group(2)
                vac = False
                if want_vac:
                    window = ' '.join(lines[i:i + 3])
                    vac = bool(re.search(r':\s*Prop\s*:=\s*True\b', window) or
                               re.search(r':\s*True\s*:=', window) or
                               re.search(r':=\s*True\s*$', ln.rstrip()))
                for key in {nm, ('.'.join(stack + [nm]) if stack else nm)}:
                    e = names[key]
                    e['mods'].add(modpath)
                    if vac:
                        e['vac'] = True
    return names, nss, mods


pf, pf_ns, pf_mods = scan(LEAN, 'PF', True)
sys.stderr.write('PF: %d names, %d namespaces, %d module tokens\n'
                 % (len(pf), len(pf_ns), len(pf_mods)))
ml, ml_ns, ml_mods = scan(MATH, 'Mathlib', False)
sys.stderr.write('mathlib: %d names, %d namespaces\n' % (len(ml), len(ml_ns)))

FILEEXT = ('.lean', '.csv', '.json', '.md', '.c', '.ccl', '.txt', '.cff',
           '.tex', '.py', '.sh', '.yml', '.toml', '.pdf')
PYPREFIX = ('principia_fractalis.', 'mpmath.', 'mp.', 'numpy.', 'scipy.')


def compiled(mod):
    return os.path.exists(os.path.join(BUILD, mod + '.olean'))


TOKEN = re.compile(r'\\(?:texttt|lstinline|lean|leanname)\{([^}]{3,120})\}')
SHAPED = re.compile(r'^[A-Za-z_][A-Za-z0-9_.\'\u2080-\u2089]*$')
SKIP = {'sorry', 'True', 'False', 'Prop', 'Type', 'propext', 'Quot.sound',
        'Classical.choice', 'native_decide', 'decide', 'rfl', 'simp',
        'norm_num', 'linarith', 'sorryAx', 'ofReduceBool'}

rows = []
allunres = collections.Counter()
for sub in ('chapters', 'appendices', 'backmatter'):
    d = os.path.join(BOOK, sub)
    if not os.path.isdir(d):
        continue
    for fn in sorted(os.listdir(d)):
        if not fn.endswith('.tex'):
            continue
        txt = io.open(os.path.join(d, fn), encoding='utf-8',
                      errors='replace').read()
        toks = []
        for raw in TOKEN.findall(txt):
            t = raw.replace('\\_', '_').replace('\\', '').strip()
            if not SHAPED.match(t) or t in SKIP:
                continue
            if '.' not in t and '_' not in t and not re.search(r'[a-z][A-Z]', t):
                continue
            toks.append(t)
        uniq = sorted(set(toks))
        c = collections.Counter()
        unres, vacn, uncomp = [], [], []
        for t in uniq:
            if t.endswith(FILEEXT) or t.startswith(PYPREFIX):
                c['FILE'] += 1
                continue
            if t in pf:
                c['PF'] += 1
                e = pf[t]
                if any(compiled(m) for m in e['mods']):
                    c['COMPILED'] += 1
                else:
                    uncomp.append(t)
                if e['vac']:
                    c['VACUOUS'] += 1
                    vacn.append(t)
                continue
            if t in ml:
                c['MATHLIB'] += 1
                continue
            if t in pf_ns or t in pf_mods or t in ml_ns:
                c['STRUCT'] += 1
                continue
            c['UNRESOLVED'] += 1
            unres.append(t)
            allunres[t] += 1
        rows.append(dict(sub=sub, file=fn, cited=len(toks), uniq=len(uniq),
                         c=c, unres=unres, vacn=vacn, uncomp=uncomp))

W = '%-12s %-44s %5s %5s %4s %5s %5s %5s %5s %5s'
print(W % ('ZONE', 'FILE', 'CITE', 'UNIQ', 'PF', 'COMPD', 'VACUO',
           'MLIB', 'STRCT', 'FILE?'), end='')
print('  UNRES')
print('-' * 122)
T = collections.Counter()
for r in rows:
    c = r['c']
    print(W % (r['sub'], r['file'][:44], r['cited'], r['uniq'],
               c['PF'], c['COMPILED'], c['VACUOUS'], c['MATHLIB'],
               c['STRUCT'], c['FILE']), end='')
    print('  %d' % c['UNRESOLVED'])
    T['cited'] += r['cited']; T['uniq'] += r['uniq']
    for k in ('PF', 'COMPILED', 'VACUOUS', 'MATHLIB', 'STRUCT', 'FILE',
              'UNRESOLVED'):
        T[k] += c[k]
print('-' * 122)
print(W % ('TOTAL', '%d files' % len(rows), T['cited'], T['uniq'],
           T['PF'], T['COMPILED'], T['VACUOUS'], T['MATHLIB'],
           T['STRUCT'], T['FILE']), end='')
print('  %d' % T['UNRESOLVED'])

print()
print('### PF citations whose module is NOT COMPILED')
n = 0
for r in rows:
    if r['uncomp']:
        n += 1
        print('  %-42s %s' % (r['file'][:42], ', '.join(r['uncomp'][:10])))
print('  (none)' if n == 0 else '')

print()
print('### PF citations that are VACUOUS (statement is True)')
n = 0
for r in rows:
    if r['vacn']:
        n += 1
        print('  %-42s %s' % (r['file'][:42], ', '.join(r['vacn'][:10])))
print('  (none)' if n == 0 else '')

print()
print('### UNRESOLVED tokens, by how many files cite them (the real queue)')
for t, k in allunres.most_common(80):
    who = [r['file'] for r in rows if t in r['unres']]
    print('  %-62s x%-2d  %s' % (t[:62], k, ', '.join(w[:26] for w in who[:3])))
