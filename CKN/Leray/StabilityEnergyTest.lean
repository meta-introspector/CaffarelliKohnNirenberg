-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.StabilityTestBounds

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- A smooth compactly supported energy test is essentially bounded on
each local box. -/
theorem stability_energyTest_memLp_top
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I) :
    MemLp (fun z : ParabolicPoint => ψ z) ∞
      (volume.restrict (spaceTimeSet Ω' J)) := by
  obtain ⟨C, hC⟩ := exists_bound_of_mem_spaceTimeTestFunction hψ
  have hcont : Continuous (fun z : ParabolicPoint => ψ z) :=
    hψ.1.continuous.comp parabolicHomeomorph.continuous
  exact memLp_top_of_bound hcont.aestronglyMeasurable C
    (Eventually.of_forall fun z => hC (parabolicHomeomorph z))

end CKN
