-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.StabilityWeightedGradientScalar

@[expose] public section

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false
noncomputable section

namespace CKN

/-- The product of two `L²` fields, weighted by a bounded scalar function,
is integrable. -/
theorem stability_weighted_product_integrable
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f g ψ : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hψ : MemLp ψ ∞ μ) :
    Integrable (fun x => f x * g x * ψ x) μ := by
  have hfg : MemLp (fun x => f x * g x) 1 μ := by
    have h : MemLp (f * g) 1 μ := hf.mul hg
    have heq : f * g = (fun x => f x * g x) := by funext x; rfl
    rwa [heq] at h
  exact stability_integrable_mul_bounded_test μ (by norm_num) hfg hψ

end CKN
