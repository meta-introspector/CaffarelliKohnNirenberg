-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.CompactnessSlice
public import CKN.Foundation.Measure.SliceProductMeasurability
public import CKN.Foundation.Measure.SliceGradientBumps
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

open MeasureTheory Filter
open CKN.Foundation.Parabolic

set_option autoImplicit false

namespace CKN.Leray

/-- Successive limits of spatial mollifications define a field at every
space-time point. -/
noncomputable def compactnessMollifiedLimit
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ) :
    Vec3 × ℝ → Vec3 := fun z i =>
  limUnder atTop (fun m : ℕ =>
    limUnder atTop (fun k : ℕ =>
      CKN.mollify (fun y : Vec3 => u (σ k) (y,z.2) i)
        (CKN.sliceRadius m) (CKN.sliceRadius_pos m) z.1))

/-- The mollified limit is jointly measurable for every sequence of jointly
measurable fields. -/
theorem measurable_compactnessMollifiedLimit
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (hu : ∀ n, Measurable (u n)) :
    Measurable (compactnessMollifiedLimit u σ) := by
  classical
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (fun z : Vec3 × ℝ =>
    limUnder atTop (fun m : ℕ =>
      limUnder atTop (fun k : ℕ =>
        CKN.mollify (fun y : Vec3 => u (σ k) (y,z.2) i)
          (CKN.sliceRadius m) (CKN.sliceRadius_pos m) z.1)))
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro m
  apply StronglyMeasurable.limUnder
  intro k
  have hP : StronglyMeasurable
      (fun z : Vec3 × ℝ => u (σ k) z i) := by
    have h : Measurable (fun z : Vec3 × ℝ => u (σ k) z i) := by
      fun_prop
    exact h.stronglyMeasurable
  have hK : Continuous
      (CKN.mollifier (d := 3) (CKN.sliceRadius m)
        (CKN.sliceRadius_pos m)) :=
    (CKN.mollifier_contDiff (d := 3) (n := 0)
      (CKN.sliceRadius_pos m)).continuous
  have hm := CKN.stronglyMeasurable_slice_kernel_integral hK hP
  simpa only [CKN.mollify, MeasureTheory.convolution,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hm

end CKN.Leray
