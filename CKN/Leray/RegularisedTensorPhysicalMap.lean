-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedTensorPhysicalBilinear

/-!
# The bounded physical regularized tensor map

The Schwartz bilinear estimate selects a continuous tensor map on two
complex spatial L² fields.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- A finite nonnegative bound for the complex physical tensor map. -/
def regularisedTensorPhysicalConstant
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) : ℝ :=
  Classical.choose (regularisedSchwartzTensorBilinear_L2_extension ρ ε hε)

/-- The bounded complex bilinear regularized tensor on physical L² data. -/
def regularisedTensorPhysicalMap
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    ComplexVectorL2 →L[ℂ] ComplexVectorL2 →L[ℂ] ComplexTensorL2 :=
  Classical.choose
    (Classical.choose_spec
      (regularisedSchwartzTensorBilinear_L2_extension ρ ε hε)).2

/-- The chosen physical tensor map has its uniform operator bound. -/
theorem regularisedTensorPhysicalMap_norm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ regularisedTensorPhysicalConstant ρ ε hε ∧
      ‖regularisedTensorPhysicalMap ρ ε hε‖ ≤
        regularisedTensorPhysicalConstant ρ ε hε := by
  constructor
  · exact (Classical.choose_spec
      (regularisedSchwartzTensorBilinear_L2_extension ρ ε hε)).1
  · exact (Classical.choose_spec
      (Classical.choose_spec
        (regularisedSchwartzTensorBilinear_L2_extension ρ ε hε)).2).1

/-- On Schwartz data, the physical tensor map equals the original
regularized Schwartz tensor L² class. -/
theorem regularisedTensorPhysicalMap_schwartz
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g f : 𝓢(L2Vec3, ComplexVec3)) :
    regularisedTensorPhysicalMap ρ ε hε (g.toLp 2) (f.toLp 2) =
      (regularisedSchwartzTensorBilinear ρ ε hε g f).toLp 2 :=
  (Classical.choose_spec
    (Classical.choose_spec
      (regularisedSchwartzTensorBilinear_L2_extension ρ ε hε)).2).2 g f

end CKN.Leray

end
