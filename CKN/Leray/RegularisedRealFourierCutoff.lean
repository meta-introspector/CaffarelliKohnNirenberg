-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.FourierRealification
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real-valued finite-frequency approximation

Complex Fourier restriction followed by coordinatewise real part supplies a
real spatial L² approximation for the Galerkin argument in `thm:regularised`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace CKN.Leray

/-- Taking real parts after complexification recovers a real spatial L²
field. -/
theorem realPartVectorL2_complexifyVectorL2 (f : RealVectorL2) :
    realPartVectorL2 (complexifyVectorL2 f) = f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (L := realPartValue) (p := 2) (μ := volume) (complexifyVectorL2 f),
    ContinuousLinearMap.coeFn_compLpL
      (L := complexifyValue) (p := 2) (μ := volume) f]
      with x hxReal hxComplex
  change ((realPartValue.compLpL 2 volume) (complexifyVectorL2 f)) x = f x
  rw [hxReal]
  change realPartValue (((complexifyValue.compLpL 2 volume) f) x) = f x
  rw [hxComplex]
  apply PiLp.ext
  intro i
  simp [realPartValue, realPartValueLinear,
    complexifyValue, complexifyValueLinear, complexifyFrequency]

end CKN.Leray

end
