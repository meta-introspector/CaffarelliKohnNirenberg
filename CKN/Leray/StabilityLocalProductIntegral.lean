-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.ParabolicMeasure

@[expose] public section

open MeasureTheory
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- A local-box scalar integral in CKN coordinates equals its ordinary
product-measure integral. -/
theorem stability_setIntegral_localBox_eq_prod
    {Ω' : Set Vec3} {J : Set ℝ} (F : ParabolicPoint → ℝ) :
    (∫ z in CKN.spaceTimeSet Ω' J, F z ∂volume) =
      ∫ z : Vec3 × ℝ, F (z.1, z.2)
        ∂((volume.restrict Ω').prod (volume.restrict J)) := by
  rw [setIntegral_parabolic_to_product]
  rw [Measure.prod_restrict,
    ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  rfl

end CKN
