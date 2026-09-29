-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.StabilityLocalProductLp

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- Local `Lᵖ` membership agrees in CKN and product coordinates. -/
theorem stability_memLp_localBox_prod
    {E : Type*} [NormedAddCommGroup E]
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J)
    {r : ℝ≥0∞} {f : ParabolicPoint → E}
    (hf : MemLp f r (volume.restrict (CKN.spaceTimeSet Ω' J))) :
    MemLp (fun z : Vec3 × ℝ => f (z.1, z.2)) r
      ((volume.restrict Ω').prod (volume.restrict J)) := by
  have hS : MeasurableSet (CKN.spaceTimeSet Ω' J) :=
    hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
  have hpre : parabolicHomeomorph.symm ⁻¹' CKN.spaceTimeSet Ω' J =
      Ω' ×ˢ J := by ext z; rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hS
  rw [hpre] at hmp
  have h := hf.comp_measurePreserving hmp
  change MemLp (fun z : Vec3 × ℝ => f (z.1, z.2)) r
    (volume.restrict (Ω' ×ˢ J)) at h
  rw [Measure.prod_restrict,
    ← MeasureTheory.Measure.volume_eq_prod Vec3 ℝ]
  exact h

end CKN
