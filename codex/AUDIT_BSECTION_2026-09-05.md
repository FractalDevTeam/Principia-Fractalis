# Release gate section B — audit record, 2026-09-05

Run from committed state on branch r331b-provenance. Verdicts read from
`#print axioms` output filtered to each module s own file, per gate item B0.

```
=== B1-B4: per-box bridge audits ===
PF.Analytic.RiemannXiBox0BridgeAudit                 RC=0  audits=31   clean
PF.Analytic.RiemannXiBox100BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox2BridgeAudit                 RC=0  audits=19   clean
PF.Analytic.RiemannXiBox102BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox103BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox104BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox105BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox106BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox107BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox108BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox109BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox110BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox111BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox112BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox113BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox114BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox115BridgeAudit               RC=0  audits=19   clean
PF.Analytic.RiemannXiBox116BridgeAudit               RC=0  audits=19   clean
=== B5: union ===
PF.Analytic.RiemannXiTopUnionAudit                   RC=0  audits=21   clean
=== B6: endgame ===
PF.Analytic.RiemannXiT15Endgame                      RC=0  audits=3    clean
=== B7-B10: consumed boundary chain ===
PF.Analytic.RiemannXiBoundaryT15_r328                RC=0  audits=8    clean
PF.Analytic.RiemannXiBottomEdgeUnconditional_r329b   RC=0  audits=6    clean
PF.Analytic.RiemannXiRectangleCount_r327             RC=0  audits=3    clean
PF.Analytic.RiemannXiThetaBoxEnclosure_r331a         RC=0  audits=11   clean
=== SUMMARY ===
  targets:      24
  RC != 0:      0
  NON-CLEAN:    0
  zero-audit:   0
```

Integrity: `lake build --no-build PF.Analytic.RiemannXiT15Endgame` -> RC=0,
"All targets up-to-date (8727 jobs)" — every committed source matches its
built olean; nothing stale, nothing missing.
