-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

open Set

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Fields continuous on complementary measurable regions define a measurable
piecewise field, as used for extensions in `prop:leray-limit`. -/
theorem lerayLimit_measurableOn_extension
    {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (s : Set α)
    [∀ x : α, Decidable (x ∈ s)] (hs : MeasurableSet s)
    (f g : α → β) (hf : ContinuousOn f s) (hg : ContinuousOn g sᶜ) :
    Measurable (s.piecewise f g) := by
  classical
  exact hf.measurable_piecewise hg hs

end CKN.Leray

end
