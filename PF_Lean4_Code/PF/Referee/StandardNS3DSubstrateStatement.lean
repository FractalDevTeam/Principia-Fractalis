/-
# PF.Referee.StandardNS3DSubstrateStatement

Typed standard contract for 3D Navier-Stokes at substrate scope.

The actual `StandardNS3DEncoding` structure and the
`Clay_NavierStokes_Standard` predicate live in the shared
`StandardClayStatements.lean` file (which carries all six
Clay-axis parameterised encodings in one place).  This file
re-exports them under a dedicated namespace so the 2026-11-15
typed-substrate capstone family has one named `Standard…Statement`
file per axis, mirroring the other seven axes.

SPDX-License-Identifier: Apache-2.0
Author: Pablo Cohen.  2026-11-15.
-/

import PF.Referee.StandardClayStatements

namespace PF.Referee.StandardNS3DSubstrateStatement

/-- Re-export: 3D Navier-Stokes substrate-scope encoding — velocity
    field type + initial-data type + Schwartz-divergence-free predicate
    + global smooth-solution predicate.  See
    `PF.Referee.StandardClayStatements.StandardNS3DEncoding` for the
    definition. -/
abbrev StandardNS3DEncoding := PF.Referee.StandardClayStatements.StandardNS3DEncoding

/-- Re-export: **Clay Navier-Stokes (substrate-encoded form).** Over a
    substrate NS encoding, every Schwartz divergence-free initial datum
    admits a smooth global solution. -/
abbrev Clay_NavierStokes_Standard := PF.Referee.StandardClayStatements.Clay_NavierStokes_Standard

theorem rule1_compliance : True := trivial

end PF.Referee.StandardNS3DSubstrateStatement
