#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Run PABLO'S OWN CODE, verbatim. No reimplementation by me.

The point of this harness: my earlier audit reimplemented the scoring path, so
its result was only as good as my reading. This runs the author's actual bytes.

`FractalResonanceFramework` (the class that computes every number in the
"143 problems / 100% coherence" claim) spans the source from
`class FractalResonanceFramework:` to just before `# === Problem Database ===`.
Those bytes are exec'd UNMODIFIED. The only thing this harness supplies is the
module-level imports the class needs -- np, math, time, datetime, fft -- which
are present on this machine. qiskit/ipywidgets are absent here and are NOT
needed: the class never references them. (That itself is the point of item (iii)
of the 2026-10-08 correction -- the quantum result does not enter the score.)

Then it calls the author's own `run_benchmark` on every entry in the author's
own database and prints the author's own `coherence`, with the author's own
`determine_status` thresholds applied.

If my audit was right, this prints 100.000 for all of them. If my audit was
wrong, this is where that shows up.
"""
import hashlib
import io
import math
import sys
import time
from datetime import datetime

import numpy as np
from scipy.fft import fft

SRC = ("/Storage 2TB/home/xluxx/Principia-Fractalis-ACTIVE/ARCHIVE/"
       "2026-06-08-cleanup/dirs/Evidence_and_Data_for_GitHub/"
       "IBM_Quantum_Verification/143 Problems Solved On IBM.py")

raw = io.open(SRC, "rb").read()
print("source sha256 : %s" % hashlib.sha256(raw).hexdigest())
print("source bytes  : %d" % len(raw))

text = raw.decode("utf-8", errors="replace")

START = "class FractalResonanceFramework:"
END = "# === Problem Database ==="
i = text.index(START)
j = text.index(END)
block = text[i:j]
print("exec'd slice  : offset %d..%d  (%d bytes, %d lines) -- UNMODIFIED"
      % (i, j, len(block), block.count("\n")))
print("slice sha256  : %s" % hashlib.sha256(block.encode("utf-8")).hexdigest())
print("contains 'class FractalResonanceFramework' : %s" % (START in block))
print("contains 'def run_benchmark'               : %s" % ("def run_benchmark" in block))
print("contains 'def fractal_resonance_function'  : %s"
      % ("def fractal_resonance_function" in block))
print("qiskit referenced in the slice?            : %s"
      % ("qiskit" in block or "AerSimulator" in block or "QuantumCircuit" in block))
print()

ns = {
    "np": np, "math": math, "time": time, "datetime": datetime, "fft": fft,
    "__name__": "pf_original",
}
exec(compile(block, "143 Problems Solved On IBM.py (author slice)", "exec"), ns)

F = ns["FractalResonanceFramework"]
fw = F()
print("author's database entries : %d" % len(fw.theories))
print("author's max_scale        : %s" % fw.max_scale)
print("author's critical_n       : %s" % fw.critical_n)
print()


# the author's own thresholds, from display_results.determine_status
def determine_status(coh100):
    if coh100 >= 90:
        return "Solved"
    if coh100 >= 70:
        return "Close to Solved"
    if coh100 >= 50:
        return "Some Progress"
    return "Still Open"


import contextlib

rows = []
t0 = time.time()
buf = io.StringIO()
with contextlib.redirect_stdout(buf):          # the author's code prints a lot
    for name in sorted(fw.theories):
        r = fw.run_benchmark(name)
        rows.append((name, r["coherence"], r["peak_alpha"],
                     fw.theories[name]["known_result"]))
print("ran author's run_benchmark on %d entries in %.1fs" % (len(rows), time.time() - t0))
print()

c100 = [r[1] * 100 for r in rows]
solved_db = [r for r in rows if "solved" in r[3].lower()]
open_db = [r for r in rows if "solved" not in r[3].lower()]

print("=== AUTHOR'S OWN coherence, x100 ===")
print("  all entries      n=%-4d min=%.6f  max=%.6f  distinct values=%d"
      % (len(c100), min(c100), max(c100), len(set(round(v, 9) for v in c100))))
if solved_db:
    v = [r[1] * 100 for r in solved_db]
    print("  'solved' in db   n=%-4d min=%.6f  max=%.6f" % (len(v), min(v), max(v)))
if open_db:
    v = [r[1] * 100 for r in open_db]
    print("  open in db       n=%-4d min=%.6f  max=%.6f" % (len(v), min(v), max(v)))

from collections import Counter
print()
print("=== AUTHOR'S OWN determine_status verdicts ===")
print("  entries open in the database   -> %s"
      % dict(Counter(determine_status(r[1] * 100) for r in open_db)))
print("  entries already solved in db   -> %s"
      % dict(Counter(determine_status(r[1] * 100) for r in solved_db)))

print()
print("=== the Millennium entries, by the author's own code ===")
for want in ("Riemann Hypothesis", "P vs NP", "Navier-Stokes Existence",
             "Hodge Conjecture", "Yang-Mills Mass Gap",
             "Birch-Swinnerton-Dyer", "Poincare Conjecture"):
    for r in [x for x in rows if x[0] == want][:1]:
        print("  %-28s -> %8.4f   status=%-8s  (db says: %s)"
              % (r[0], r[1] * 100, determine_status(r[1] * 100), r[3][:28]))

print()
uniq = set(round(v, 9) for v in c100)
if len(uniq) == 1:
    print("VERDICT: the author's own code returns the SINGLE value %.6f for all %d"
          % (list(uniq)[0], len(c100)))
    print("         entries. Confirmed against the author's bytes, not a reimplementation.")
else:
    print("VERDICT: the author's own code returns %d DISTINCT values." % len(uniq))
    print("         My earlier audit's saturation claim is WRONG and must be retracted.")
    for v in sorted(uniq)[:12]:
        print("           %.6f  x%d" % (v, sum(1 for y in c100 if round(y, 9) == v)))
