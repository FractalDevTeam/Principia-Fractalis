#!/usr/bin/env python3
"""Does appC's logistic transform reconcile appH's raw ch2 values with appC's
clinical bands? Compute the mapping; read appC's definition in full context."""
import pathlib
from mpmath import mp, mpf, exp

mp.dps = 25
BK = pathlib.Path("/home/xluxx/pf-push-20261120/Principia_Fractalis_master_folder")
C = (BK / "appendices/appC_clinical.tex").read_text(encoding="utf-8").split("\n")

print("########## appC's ch2 definition in context (lines 205-255)")
for i in range(204, 255):
    if i < len(C):
        print("   %4d  %s" % (i + 1, C[i][:124]))

print()
print("########## appC bands (transformed scale)")
BANDS = [("Fully conscious", 0.95, 1.00, "Normal care"),
         ("Minimally conscious", 0.75, 0.94, "Enhanced monitoring"),
         ("Vegetative state", 0.50, 0.74, "PALLIATIVE CONSULTATION"),
         ("Coma/unconscious", 0.00, 0.49, "Intensive support")]
for nm, lo, hi, act in BANDS:
    print("   %-22s %.2f - %.2f   %s" % (nm, lo, hi, act))


def band(x):
    for nm, lo, hi, act in BANDS:
        if lo - 1e-12 <= x <= hi + 1e-12:
            return nm, act
    return "OUT OF RANGE", "-"


def sigmoid(raw):
    return 1 / (1 + exp(-10 * (mpf(raw) - mpf("0.5"))))


print()
print("########## appH's five states: raw -> transformed -> appC band")
APPH = [("General Anesthesia", "0.1", "< 0.1, unconscious"),
        ("Sleep (NREM)", "0.3", "~ 0.3"),
        ("Normal Waking", "0.6", "~ 0.6"),
        ("Focused Attention", "0.8", "~ 0.8"),
        ("Meditative States", "0.95", ">= 0.95, crystallization")]
print("   %-20s %-7s %-12s %-22s %s" % ("STATE", "RAW", "SIGMOID", "appC BAND", "ACTION"))
print("   %-20s %-7s %-12s %-22s %s" % ("-"*20, "-"*7, "-"*12, "-"*22, "-"*22))
rows = []
for nm, raw, _lbl in APPH:
    s = sigmoid(raw)
    b, act = band(float(s))
    rows.append((nm, raw, s, b, act))
    print("   %-20s %-7s %-12s %-22s %s" % (nm, raw, mp.nstr(s, 6), b, act))

print()
print("########## what the RAW value would have to be to reach each boundary")
# invert: raw = 0.5 - ln(1/y - 1)/10
from mpmath import log
for nm, lo, hi, act in BANDS:
    if lo <= 0:
        continue
    raw_lo = mpf("0.5") - log(1/mpf(str(lo)) - 1) / 10
    print("   to reach %-22s (>= %.2f transformed) needs raw >= %s"
          % (nm, lo, mp.nstr(raw_lo, 6)))

print()
print("########## THE RESIDUAL — what the transform does NOT fix")
nw = sigmoid("0.6")
print("   Normal Waking raw 0.60 -> transformed %s" % mp.nstr(nw, 8))
print("   appC 'Minimally conscious' floor      = 0.75")
print("   shortfall                             = %s" % mp.nstr(mpf("0.75") - nw, 6))
print("   so normal waking still lands in       = %s -> %s" % band(float(nw)))
raw_needed = mpf("0.5") - log(1/mpf("0.75") - 1) / 10
print("   raw needed to clear the vegetative band = %s (appH says 0.6)" % mp.nstr(raw_needed, 6))
print()
print("   Rows the transform DOES reconcile:")
for nm, raw, s, b, act in rows:
    tag = "reconciled" if b in ("Fully conscious", "Coma/unconscious") else "RESIDUAL"
    print("      %-20s raw %-5s -> %-9s %-22s %s" % (nm, raw, mp.nstr(s, 5), b, tag))
