-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRealSpacetime

/-!
# Complete real-radius Helmholtz test-field lemma

The decomposition, all-order decay, compact cutoff tests, and the three
real-parameter limits are collected in one result.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section
namespace CKN.Leray

/-- The complete test-field decomposition, all-order decay, real-radius
cutoff tests, and cutoff limits in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzTestField_real_full
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    (∀ z, associatedPressureHelmholtzScalarPotential φ z =
        associatedPressureNewtonianPotential (associatedPressureTestDivergence φ) z ∧
      ∀ j, associatedPressureHelmholtzVectorPotential φ z j =
        -associatedPressureNewtonianPotential
          (associatedPressureTestCurlComponent φ j) z) ∧
    (ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzScalarPotential φ) ∧
      ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzVectorPotential φ)) ∧
    (∀ z, CKN.spatialLaplacian
        (fun x : Vec3 => associatedPressureHelmholtzScalarPotential φ (x, z.2)) z.1 =
      associatedPressureTestDivergence φ z) ∧
    (∀ z,
      associatedPressureTestDivergence
          (fun q => φ q - associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) q) z = 0 ∧
        (fun q => φ q - associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotential φ) q) z =
            associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) z) ∧
    (∀ k, ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
      |associatedPressureSpatialMultiPartial k w
          (associatedPressureHelmholtzScalarPotential φ) z| +
        |associatedPressureSpatialMultiPartial k w
          (fun q => CKN.timePartial
            (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φ) q) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) ∧
    (∀ k, ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
      ∑ j : Fin 3,
        (|associatedPressureSpatialMultiPartial k w
            (fun q => associatedPressureHelmholtzVectorPotential φ q j) z| +
          |associatedPressureSpatialMultiPartial k w
            (fun q => CKN.timePartial (show ParabolicPoint → ℝ from
              fun y : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ y j) q) z|) ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) ∧
    (∀ (R : ℝ) (hR : 1 ≤ R),
      associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) ∈
          CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) ∧
        ∀ z, associatedPressureTestDivergence
          (associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR)) z = 0) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ i : Fin 3,
      Tendsto (fun R : ℝ => ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0)) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun R : ℝ => ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ)) atTop (nhds 0)) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun R : ℝ => ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0)) := by
  rcases associatedPressureHelmholtzTestField_full hφ with
    ⟨hformulas, hsmooth, hlaplacian, hdecomposition, hscalarDecay,
      hvectorDecay, _, _, _, _⟩
  refine ⟨hformulas, hsmooth, hlaplacian, hdecomposition, hscalarDecay,
    hvectorDecay, ?_, ?_, ?_, ?_⟩
  · intro R hR
    constructor
    · exact associatedPressureHelmholtzCutoffCurlReal_mem_spaceTimeTestFunction
        hφ R hR
    · intro z
      simpa [associatedPressureTestDivergence, associatedPressureTestPartial,
        CKN.spatialPartialProd] using associatedPressureTestCurl_divergence
          (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
            hφ R hR).1 z
  · exact associatedPressureHelmholtzCutoffCurlReal_timePartial_L1tL2x_tendsto_zero hφ
  · exact associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L2tx_tendsto_zero hφ
  · exact associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L1tLinf_tendsto_zero hφ

end CKN.Leray

end
