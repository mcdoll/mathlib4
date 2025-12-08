/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Distribution.FourierSchwartz
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public noncomputable section

section FourierTransform

variable
  {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

open SchwartzMap MeasureTheory FourierTransform ComplexInnerProductSpace

open scoped ZeroAtInfty Filter Topology BoundedContinuousFunction ENNReal

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (V E) in
/-- The Fourier transform on `L1` as a linear isometry equivalence. -/
def Lp.fourierTransformCLM : (Lp (α := V) E 1) →L[ℂ] C₀(V, E) :=
  (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap.extendOfNorm
    (toLpCLM ℂ (E := V) E 1)

variable (V E μ) in
/-- Schwartz functions are dense in `Lp`. -/
theorem denseRange_toLpCLM {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp' : Fact (1 ≤ p)] {μ : Measure V} [hμ : μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] :
    DenseRange (SchwartzMap.toLpCLM ℝ E p μ) := by sorry

@[simp]
theorem Lp.fourierTransformCLM_toLp_one_apply (f : 𝓢(V, E)) (x : V) :
    Lp.fourierTransformCLM V E (f.toLp 1) x = 𝓕 f x := by
  have lhs :
      (toZeroAtInftyCLM ℂ V E ∘L (SchwartzMap.fourierTransformCLM ℂ)).toLinearMap f x = 𝓕 f x := by
    simp
  have rhs : toLpCLM ℂ (E := V) E 1 volume f = f.toLp 1 := by simp
  rw [← lhs, ← rhs]
  congr 1
  apply LinearMap.extendOfNorm_eq
  · apply denseRange_toLpCLM
    norm_num
  use 1
  simpa using norm_fourier_toBoundedContinuousFunction_top_leq_toLp_one

theorem Lp.fourierTransformCLM_apply_apply (f : Lp (α := V) E 1) (x : V) :
    Lp.fourierTransformCLM V E f x = 𝓕 (f : V → E) x := by
  apply DenseRange.induction_on (p := fun f ↦ ((fourierTransformCLM V E) f) x = 𝓕 (f : V → E) x)
    (denseRange_toLpCLM V E (by norm_num)) f
  · refine isClosed_eq ((fourierTransformCLM V E).continuous.eval_const x) ?_

    sorry
  intro f
  simpa using Real.fourier_congr_ae (coeFn_toLp f 1 volume).symm x

theorem riemann_lebesgue (f : V → E) (hf : MemLp f 1) :
    Filter.Tendsto (𝓕 f) (Filter.cocompact V) (𝓝 0) := by
  have : Lp.fourierTransformCLM V E hf.toLp = 𝓕 f := by
    ext x
    rw [Lp.fourierTransformCLM_apply_apply hf.toLp]
    apply Real.fourier_congr_ae hf.coeFn_toLp
  rw [← this]
  apply zero_at_infty
