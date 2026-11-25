#!/usr/bin/env python3
"""ch30 prints a confusion matrix AND a set of diagnostic metrics. Do they
agree? And do appC's metrics agree with ch30's? Compute, do not assume."""
from fractions import Fraction as F

# ch30's confusion matrix, verbatim from ch30:286-296
#                      Gold: Unconscious   Gold: Conscious    Total
# Predicted Unconscious        402                9             411
# Predicted Conscious           14              422             436
# Total                        416              431             847
TN, FN, pred_unc = 402, 9, 411
FP, TP, pred_con = 14, 422, 436
gold_unc, gold_con, N = 416, 431, 847

print("=" * 76)
print("A. does ch30's matrix add up?")
print("=" * 76)
print("   row 1 : %d + %d = %d   printed %d   %s" % (TN, FN, TN+FN, pred_unc, TN+FN == pred_unc))
print("   row 2 : %d + %d = %d   printed %d   %s" % (FP, TP, FP+TP, pred_con, FP+TP == pred_con))
print("   col 1 : %d + %d = %d   printed %d   %s" % (TN, FP, TN+FP, gold_unc, TN+FP == gold_unc))
print("   col 2 : %d + %d = %d   printed %d   %s" % (FN, TP, FN+TP, gold_con, FN+TP == gold_con))
print("   grand : %d           printed %d   %s" % (TN+FN+FP+TP, N, TN+FN+FP+TP == N))

print()
print("=" * 76)
print("B. metrics FROM the matrix, vs what ch30's THEOREM states")
print("=" * 76)
acc  = F(TP+TN, N)
sens = F(TP, gold_con)          # detect consciousness
spec = F(TN, gold_unc)          # detect unconsciousness
ppv  = F(TP, pred_con)
npv  = F(TN, pred_unc)
THM = {"Accuracy": 97.3, "Sensitivity": 96.8, "Specificity": 97.8,
       "PPV": 97.4, "NPV": 97.2}
CALC = {"Accuracy": acc, "Sensitivity": sens, "Specificity": spec,
        "PPV": ppv, "NPV": npv}
print("   %-13s %-14s %-12s %-12s %s" % ("metric", "from matrix", "ch30 thm", "delta (pts)", "verdict"))
print("   %-13s %-14s %-12s %-12s %s" % ("-"*13, "-"*14, "-"*12, "-"*12, "-"*18))
for k in ("Accuracy", "Sensitivity", "Specificity", "PPV", "NPV"):
    c = 100*float(CALC[k]); t = THM[k]; d = c - t
    v = "agrees" if abs(d) < 0.1 else "** DISAGREES **"
    print("   %-13s %-14.4f %-12.1f %-+12.4f %s" % (k, c, t, d, v))

print()
print("   Are sensitivity and specificity TRANSPOSED in the theorem?")
print("      matrix sens %.4f  vs thm spec %.1f   -> delta %+.4f"
      % (100*float(sens), THM["Specificity"], 100*float(sens)-THM["Specificity"]))
print("      matrix spec %.4f  vs thm sens %.1f   -> delta %+.4f"
      % (100*float(spec), THM["Sensitivity"], 100*float(spec)-THM["Sensitivity"]))
print("      matrix ppv  %.4f  vs thm npv  %.1f   -> delta %+.4f"
      % (100*float(ppv), THM["NPV"], 100*float(ppv)-THM["NPV"]))
print("      matrix npv  %.4f  vs thm ppv  %.1f   -> delta %+.4f"
      % (100*float(npv), THM["PPV"], 100*float(npv)-THM["PPV"]))
print()
print("   ch30's own proof block states: Sens 98.0, Spec 96.6, PPV 0.968, NPV 0.978")
print("   -- which ARE the matrix values. So the THEOREM's four numbers are the")
print("      proof's four numbers with sens<->spec and ppv<->npv exchanged.")
print("      ch30:308 'Note: Slight rounding adjustments for consistency with")
print("      empirical data.' is the acknowledgement, and it is not rounding.")

print()
print("=" * 76)
print("C. appC's metrics vs ch30's -- same study?")
print("=" * 76)
APPC = {"Sensitivity": 97.3, "Specificity": 95.8, "PPV": 96.4, "NPV": 96.9, "Accuracy": 96.6}
print("   appC says N = 412 patients;  ch30 says N = 847.  ratio %.3f" % (847/412))
print()
print("   %-13s %-10s %-10s %-10s %s" % ("metric", "appC", "ch30 thm", "matrix", "appC == ch30?"))
print("   %-13s %-10s %-10s %-10s %s" % ("-"*13, "-"*10, "-"*10, "-"*10, "-"*14))
for k in ("Accuracy", "Sensitivity", "Specificity", "PPV", "NPV"):
    print("   %-13s %-10.1f %-10.1f %-10.4f %s"
          % (k, APPC[k], THM[k], 100*float(CALC[k]),
             "yes" if abs(APPC[k]-THM[k]) < 0.05 else "NO"))
print()
print("   appC's 'Sensitivity 97.3' equals ch30's ACCURACY 97.3 -- the one figure")
print("   the matrix does support. Consistent with a row being read across.")

print()
print("=" * 76)
print("D. ch30's cohort breakdown -- does it reach 847?")
print("=" * 76)
groups = {"VS/UWS": 267, "MCS-": 189, "MCS+": 156, "EMCS": 92}
s = sum(groups.values())
for k, v in groups.items():
    print("   %-8s %d" % (k, v))
print("   sum of the four listed groups      = %d" % s)
print("   confusion-matrix total             = %d" % N)
print("   unlisted remainder                 = %d" % (N - s))
print("   (ch30's objectives mention locked-in syndrome as a fifth group;")
print("    the breakdown as printed does not include it, so %d patients are" % (N-s))
print("    unaccounted for in the listed groups.)")

print()
print("=" * 76)
print("E. the McNemar figure")
print("=" * 76)
beh = 519
print("   behavioural accuracy 519/847 = %.4f   printed 61.4%%   delta %+.4f"
      % (100*beh/N, 100*beh/N - 61.4))
print("   improvement 97.3 - 61.4 = %.1f pts   printed 35.9   %s"
      % (97.3-61.4, abs((97.3-61.4)-35.9) < 0.05))
