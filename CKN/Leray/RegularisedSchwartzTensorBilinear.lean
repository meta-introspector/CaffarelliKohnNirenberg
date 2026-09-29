-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedSchwartzTensor

/-!
# Bilinear regularized Schwartz tensors

Keeping the mollified and unmollified velocity fields distinct makes the
quadratic tensor difference an exact two-term bilinear identity.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The regularized tensor with separate mollified and unmollified
Schwartz velocity fields. -/
def regularisedSchwartzTensorBilinear
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g f : 𝓢(L2Vec3, ComplexVec3)) :
    𝓢(L2Vec3, ComplexTensor3) :=
  SchwartzMap.pairing regularisedComplexTensorOuterCLM
    (regularisedSchwartzMollify ρ ε hε g) f

/-- The bilinear Schwartz tensor is the expected pointwise product. -/
theorem regularisedSchwartzTensorBilinear_apply
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (g f : 𝓢(L2Vec3, ComplexVec3)) (x : L2Vec3) :
    regularisedSchwartzTensorBilinear ρ ε hε g f x =
      regularisedComplexTensorOuter
        (regularisedSchwartzMollify ρ ε hε g x) (f x) := rfl

end CKN.Leray

end
