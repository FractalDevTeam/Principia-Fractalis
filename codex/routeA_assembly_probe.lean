import Mathlib
open MeasureTheory
-- The corrected instantiation needs: a submodule of L², its inclusion as a
-- linear ISOMETRY (so IsUniformInducing is free), and a range submodule.
#check @Submodule.subtypeₗᵢ
#check @Submodule.subtypeL
#check @LinearIsometry.isUniformInducing
#check @LinearMap.range
#check @ContinuousLinearMap.range
#check @Submodule.topologicalClosure
#check @Submodule.dense_iff_topologicalClosure_eq_top
#check @Submodule.topologicalClosure_eq_top_iff
-- and the operator must become a CLM on the subspace
#check @ContinuousLinearMap.comp
#check @ContinuousLinearMap.domRestrict
#check @Submodule.subtypeₗᵢ_norm
import Mathlib
open MeasureTheory
#check @LinearIsometry.isometry
#check @Isometry.isUniformInducing
#check @Submodule.subtypeₗᵢ
#check @SchwartzMap.injective_toLp
#check @Submodule.coe_subtypeL
