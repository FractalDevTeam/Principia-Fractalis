/-
Route A verification probe — NOT a build artifact, a diagnostic.

Each `#check @X` reports X's type if it exists and errors if it does not.
Each command elaborates independently, so one pass gives the whole picture.
`@` is used throughout so nothing has to be inferred from context.

Near-miss candidates are probed alongside each name, so that a declaration
absent *as named* can still be reported as present *under another name*.
-/
import Mathlib

set_option maxHeartbeats 1000000

open MeasureTheory SchwartzMap

section ShouldExist

-- 1-4. SchwartzMap → Lp
#check @SchwartzMap.toLp
#check @SchwartzMap.memLp
#check @SchwartzMap.norm_toLp
#check @SchwartzMap.injective_toLp

-- 5. simple functions dense in Lp
#check @MeasureTheory.Lp.simpleFunc.dense

-- 6-7. Fourier transform on Schwartz space
#check @SchwartzMap.fourierTransformCLM
#check @SchwartzMap.fourierTransformCLE

-- 8. completion extension
#check @UniformSpace.Completion.extension
#check @UniformSpace.Completion.extension_unique
#check @UniformSpace.Completion.denseInducing_coe

-- 9. orthogonal projection
#check @Submodule.orthogonalProjection
#check @orthogonalProjection
#check @Submodule.starProjection

-- 10. convolution
#check @MeasureTheory.convolution
#check @convolution

end ShouldExist

section MustFail

-- 11. the suspected phantom
#check @SchwartzMap.denseRange_toLp

-- 12-13. the extension phantoms
#check @LinearMap.extendOfNorm
#check @ContinuousLinearMap.extend

end MustFail

section Verify

-- 14. is Lp ℂ 2 volume an inner product space over ℂ?
#synth InnerProductSpace ℂ (MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : Measure ℝ))

-- 15. Young-type inequality for convolution, candidate names
#check @MeasureTheory.eLpNorm_convolution_le
#check @MeasureTheory.enorm_convolution_le
#check @MeasureTheory.convolution_mem_Lp
#check @MeasureTheory.MemLp.convolution
#check @MeasureTheory.eLpNorm_convolution_le_eLpNorm_mul_eLpNorm

end Verify

section NearMisses

-- alternative spellings worth knowing about if the primaries fail
#check @SchwartzMap.toLpCLM
#check @SchwartzMap.coeHom
#check @MeasureTheory.Lp.simpleFunc.denseRange
#check @MeasureTheory.Lp.simpleFunc.isDenseEmbedding
#check @ContinuousLinearMap.extendTo𝕜
#check @DenseInducing.extend
#check @IsDenseInducing.extend
#check @LinearIsometry.extend

end NearMisses
