-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedBesselShiftedStokesIntegral
public import CKN.Leray.RegularisedBesselStokesPhysical

/-!
# Physical realization of the shifted complete Stokes integrand

The complete Sobolev shifted Stokes integrand represents the physical
complex L² shifted Stokes integrand at every pair of times.
-/

@[expose] public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- Taking the physical realization commutes pointwise with the
shifted complete Sobolev Stokes integrand. -/
theorem regularisedBesselShiftedStokesIntegrand_physical
    (k : ℕ)
    (F : ℝ → BesselPotentialSpace L2Vec3 ComplexTensor3 ((2 * k : ℕ) : ℝ) 2)
    (t τ : ℝ) :
    regularisedBesselSobolevToL2CLM ((2 * k : ℕ) : ℝ) (by positivity)
      (regularisedBesselShiftedStokesIntegrand k F t τ) =
    if h : 0 < τ ∧ τ < t then
      stokesL2Operator h.1
        (regularisedTensorBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
          (by positivity) (F (t - τ)))
    else 0 := by
  by_cases h : 0 < τ ∧ τ < t
  · simp only [regularisedBesselShiftedStokesIntegrand, dite_eq_left h]
    exact regularisedBesselStokesOperator_physical h.1 k (F (t - τ))
  · simp only [regularisedBesselShiftedStokesIntegrand, dite_eq_right h,
      map_zero]

end CKN.Leray

end
