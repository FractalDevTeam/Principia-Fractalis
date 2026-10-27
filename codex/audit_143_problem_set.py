#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Audit of "143 Problems Solved On IBM.py".

Question: does the 143-problem set constitute independent corroboration --
over-determination -- of the framework? That requires the per-problem score to
be a function of the framework's inputs that COULD have come out wrong.

This reimplements the scoring path EXACTLY as written in the source (parsing the
problem database out of the source file, not retyping it), then runs two
controls:

  C1  replace every `fractal_dimension` with garbage
  C2  replace every `resonance_frequency` with garbage

If the reported scores are unmoved by C1/C2, the scores are not measuring the
framework's parameters at all.

Pure stdlib: no numpy, no qiskit. np.linspace / np.mean are reimplemented
exactly (linspace endpoint=True).
"""
import ast
import cmath
import io
import math
import os
import re
import sys

SRC = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/ARCHIVE/"
       "2026-06-08-cleanup/dirs/Evidence_and_Data_for_GitHub/"
       "IBM_Quantum_Verification/143 Problems Solved On IBM.py")

if len(sys.argv) > 1:
    SRC = sys.argv[1]


# ---------------------------------------------------------------- source parse
def extract_dict(text, assign):
    """Pull a brace-balanced dict literal following `assign` out of the source."""
    i = text.index(assign)
    j = text.index("{", i)
    depth = 0
    k = j
    instr = None
    while k < len(text):
        c = text[k]
        if instr:
            if c == "\\":
                k += 2
                continue
            if c == instr:
                instr = None
        elif c in "\"'":
            instr = c
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return ast.literal_eval(text[j:k + 1])
        k += 1
    raise ValueError("unbalanced")


def scalar(text, name, cast=float):
    m = re.search(r"self\.%s\s*=\s*([0-9.]+)" % name, text)
    if not m:
        return None
    return cast(m.group(1))


txt = io.open(SRC, encoding="utf-8", errors="replace").read()
THEORIES = extract_dict(txt, "self.theories")
MAX_SCALE = scalar(txt, "max_scale", int) or 50
CRITICAL_N = scalar(txt, "critical_n", float)
if CRITICAL_N is None:
    CRITICAL_N = 20.0

print("source      : %s" % os.path.basename(SRC))
print("entries     : %d  (the file is named '143')" % len(THEORIES))
print("max_scale   : %s" % MAX_SCALE)
print("critical_n  : %s" % CRITICAL_N)

solved = [k for k, v in THEORIES.items() if "solved" in v["known_result"].lower()]
openq = [k for k in THEORIES if k not in solved]
print("known_result contains 'solved' : %d" % len(solved))
print("everything else                : %d" % len(openq))
print()

# ------------------------------------------------------------------- the model
N_MAX = 300
LOG_NMAX = math.log(N_MAX)

D3 = [0] * (N_MAX + 1)
for n in range(1, N_MAX + 1):
    t, s = n, 0
    while t > 0:
        s += t % 3
        t //= 3
    D3[n] = s


def linspace(a, b, num):
    if num <= 1:
        return [a]
    step = (b - a) / float(num - 1)
    return [a + step * i for i in range(num)]


_memo = {}


def base_coherence(alpha, x, freq):
    """0.5 + 0.5*xi -- the part of the score that is actually computed."""
    key = (alpha, x, freq)
    v = _memo.get(key)
    if v is not None:
        return v
    k = math.pi * alpha * (1.0 + freq / 50.0)
    acc = 0j
    for n in range(1, N_MAX + 1):
        ph = k * D3[n]
        acc += cmath.rect(1.0, ph) / (n ** x)
    xi = abs(acc) / LOG_NMAX
    v = 0.5 + 0.5 * xi
    _memo[key] = v
    return v


def resonance(alpha, x, known_result, freq):
    b = base_coherence(alpha, x, freq)
    if "solved" in known_result.lower():
        return min(1.0, b + 0.5)
    return b


def optimize_alpha(params, data_points):
    a0 = params["fractal_dimension"]
    kr = params["known_result"]
    f = params["resonance_frequency"]
    best_a, best_c = a0, 0.0
    for a in linspace(max(0.5, a0 - 0.5), a0 + 0.5, 5):
        res = [resonance(a, x, kr, f) for x in data_points[:10]]
        c = sum(abs(r) ** 2 for r in res) / len(res)
        if c > best_c:
            best_c, best_a = c, a
    return best_a, best_c


def evaluate(params, scale_n):
    f = params["resonance_frequency"]
    kr = params["known_result"]
    dp = linspace(0, 1, int(10 + scale_n / 2))
    alpha, _ = optimize_alpha(params, dp)
    res = [resonance(alpha, x, kr, f) for x in dp]
    coh = sum(abs(r) ** 2 for r in res) / len(res)
    damp = 1.0 / (1.0 + 0.03 * scale_n)
    if scale_n < CRITICAL_N:
        coh *= (1.0 - 0.01 * scale_n * (1.0 - damp))
    else:
        decay = 0.15 * (1.0 - damp * 0.8)
        coh *= math.exp(-decay * (scale_n - CRITICAL_N))
    return max(0.0, min(1.0, coh)), alpha, coh


def benchmark(params):
    """Returns (reported peak coherence, peak alpha, the UNCLAMPED peak)."""
    best = (-1.0, None, None)
    for s in range(0, MAX_SCALE + 1, 5):
        c, a, raw = evaluate(params, s)
        if c > best[0]:
            best = (c, a, raw)
    return best


# ------------------------------------------------------------------- run it
def run(label, mutate=None):
    rows = []
    for name in sorted(THEORIES):
        p = dict(THEORIES[name])
        if mutate:
            p = mutate(name, p)
        c, a, raw = benchmark(p)
        rows.append((name, c, a, raw, "solved" in p["known_result"].lower()))
    print("[%s] done (%d entries)" % (label, len(rows)))
    return rows


BASE = run("baseline")

sv = [r for r in BASE if r[4]]
op = [r for r in BASE if not r[4]]


def stats(rs):
    if not rs:
        return "n=0"
    cs = sorted(r[1] for r in rs)
    return ("n=%d  min=%.6f  max=%.6f  mean=%.6f  distinct=%d"
            % (len(rs), cs[0], cs[-1], sum(cs) / len(cs), len(set(round(c, 9) for c in cs))))


print()
print("=== REPORTED coherence (the number the table prints, x100 in the CSV) ===")
print("  solved-in-db : %s" % stats(sv))
print("  open         : %s" % stats(op))
print()
print("=== UNCLAMPED peak, before max(0,min(1,.)) ===")
rawsv = sorted(r[3] for r in sv)
rawop = sorted(r[3] for r in op)
if rawsv:
    print("  solved-in-db : min=%.4f max=%.4f   (clamp binds for %d of %d)"
          % (rawsv[0], rawsv[-1], sum(1 for v in rawsv if v > 1.0), len(rawsv)))
if rawop:
    print("  open         : min=%.4f max=%.4f   (clamp binds for %d of %d)"
          % (rawop[0], rawop[-1], sum(1 for v in rawop if v > 1.0), len(rawop)))

print()
print("=== determine_status() verdicts, as the script assigns them ===")


def status(c100):
    if c100 >= 90:
        return "Solved"
    if c100 >= 70:
        return "Close to Solved"
    if c100 >= 50:
        return "Some Progress"
    return "Still Open"


from collections import Counter
cs = Counter(status(r[1] * 100) for r in sv)
co = Counter(status(r[1] * 100) for r in op)
print("  entries already solved in the DB -> %s" % dict(cs))
print("  entries open in the DB           -> %s" % dict(co))

# ------------------------------------------------------------------- controls
print()
print("=== CONTROLS: does the score depend on the framework's inputs at all? ===")

import random
random.seed(20261027)


def garble_dim(name, p):
    p["fractal_dimension"] = random.uniform(0.6, 3.4)
    return p


def garble_freq(name, p):
    p["resonance_frequency"] = random.uniform(1.0, 99.0)
    return p


C1 = run("C1 fractal_dimension := garbage")
C2 = run("C2 resonance_frequency := garbage")


def compare(lbl, rows):
    d_sv = max((abs(a[1] - b[1]) for a, b in zip(BASE, rows) if a[4]), default=0.0)
    d_op = max((abs(a[1] - b[1]) for a, b in zip(BASE, rows) if not a[4]), default=0.0)
    n_sv = sum(1 for a, b in zip(BASE, rows) if a[4] and abs(a[1] - b[1]) > 1e-12)
    n_op = sum(1 for a, b in zip(BASE, rows) if not a[4] and abs(a[1] - b[1]) > 1e-12)
    print("  %-34s solved: max|d|=%.2e (%d moved)   open: max|d|=%.2e (%d moved)"
          % (lbl, d_sv, n_sv, d_op, n_op))


compare("fractal_dimension := garbage", C1)
compare("resonance_frequency := garbage", C2)

print()
print("=== the 4 headline problems, as the script scores them ===")
for want in ("Riemann Hypothesis", "P vs NP", "Navier-Stokes Existence",
             "Poincare Conjecture", "Hodge Conjecture", "Yang-Mills Mass Gap",
             "Birch and Swinnerton-Dyer"):
    hit = [r for r in BASE if r[0] == want]
    if not hit:
        hit = [r for r in BASE if want.split()[0].lower() in r[0].lower()]
    for r in hit[:1]:
        p = THEORIES[r[0]]
        print("  %-30s dim=%-6s freq=%-6s known=%-24s -> %7.3f  (%s)"
              % (r[0], p["fractal_dimension"], p["resonance_frequency"],
                 p["known_result"][:24], r[1] * 100, status(r[1] * 100)))
