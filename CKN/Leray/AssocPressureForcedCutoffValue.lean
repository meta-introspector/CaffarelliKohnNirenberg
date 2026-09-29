-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureProviderBounds

/-!
# Values of the Helmholtz cutoff tests

The force residual is paired with the test value, so its cutoff limit uses a
uniform spatial profile for the Helmholtz tests themselves.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The Helmholtz cutoff fields have a common spatial profile bound, including
for their values. -/
theorem associatedPressureHelmholtzTestCutoff_value_profile_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo 0 T ∧
      ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3),
        |associatedPressureHelmholtzTestCutoff φ n z i| ≤
          C * associatedPressureSpatialProfile K 2 z := by
  let ψ := associatedPressureHelmholtzScalarPotential φ
  let A := associatedPressureHelmholtzVectorPotential φ
  let K : Set ℝ := (tsupport φ).image Prod.snd
  have hK : IsCompact K := hφ.2.1.isCompact.image continuous_snd
  have hKsub : K ⊆ Ioo 0 T := by
    rintro t ⟨z, hz, rfl⟩
    exact hφ.2.2 hz |>.2
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hψdecay : RieszPressurePotentialDecay ψ :=
    associatedPressureHelmholtzScalarPotential_decay hφ
  have hzeroψ : ∀ t ∉ K, ∀ x, ψ (x, t) = 0 := by
    intro t ht x
    exact (associatedPressureHelmholtzPotentials_zero_off_time_support
      (by simpa [K] using ht) x).1
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hAdecay (k : Fin 3) : RieszPressurePotentialDecay (fun q => A q k) :=
    (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1
  have hzeroA (k : Fin 3) (t : ℝ) (ht : t ∉ K) (x : Vec3) : A (x, t) k = 0 := by
    have h := associatedPressureHelmholtzPotentials_zero_off_time_support
      (by simpa [K] using ht) x
    exact congrArg (fun v : Vec3 => v k) h.2
  let Dψ : ℝ := Classical.choose hψdecay.gradient_bound +
    CKN.cutoffGradientConstant * Classical.choose hψdecay.value_bound
  let DA : Fin 3 → ℝ := fun k =>
    Classical.choose (hAdecay k).gradient_bound +
      CKN.cutoffGradientConstant * Classical.choose (hAdecay k).value_bound
  have hcutDirScalar (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3) :
      |CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i z| ≤
        Dψ * associatedPressureSpatialProfile K 2 z := by
    have hcut : associatedPressureHelmholtzScalarPotentialCutoff φ n =
        rieszPressurePotentialCutoffTest ψ n := rfl
    have hdir : rieszPressureJointDirection
        (rieszPressurePotentialCutoffTest ψ n) i z =
        CKN.spatialPartialProd (rieszPressurePotentialCutoffTest ψ n) i z :=
      (rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTest_contDiff hψ n) i z).symm
    rw [hcut]
    rw [← hdir]
    exact associatedPressurePotentialCutoff_direction_profile_bound
      hψ hzeroψ hψdecay i n z
  have hcutDirA (n : ℕ) (z : Vec3 × ℝ) (k l : Fin 3) :
      |CKN.spatialPartialProd
        (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z| ≤
        DA k * associatedPressureSpatialProfile K 2 z := by
    have hcut : (fun q : Vec3 × ℝ =>
        associatedPressureHelmholtzCutoffVectorPotential φ n q k) =
        rieszPressurePotentialCutoffTest (fun q => A q k) n := by
      funext q
      rfl
    have hdir : rieszPressureJointDirection
        (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z =
        CKN.spatialPartialProd
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z :=
      (rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n) l z).symm
    rw [hcut, ← hdir]
    exact associatedPressurePotentialCutoff_direction_profile_bound
      (hAcomp k) (hzeroA k) (hAdecay k) l n z
  have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
    have hg := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    have h := le_trans (CKN.vecEuclideanNorm_nonneg _) hg
    simpa using h
  have hDψ : 0 ≤ Dψ := by
    dsimp [Dψ]
    exact add_nonneg
      (Classical.choose_spec hψdecay.gradient_bound).1
      (mul_nonneg hGradC
        (Classical.choose_spec hψdecay.value_bound).1)
  have hDA (k : Fin 3) : 0 ≤ DA k := by
    dsimp [DA]
    exact add_nonneg
      (Classical.choose_spec (hAdecay k).gradient_bound).1
      (mul_nonneg hGradC
        (Classical.choose_spec (hAdecay k).value_bound).1)
  have hprofile (z : Vec3 × ℝ) : 0 ≤ associatedPressureSpatialProfile K 2 z := by
    by_cases ht : z.2 ∈ K
    · simp [associatedPressureSpatialProfile, ht]
      positivity
    · simp [associatedPressureSpatialProfile, ht]
  let Ccurl : ℝ := 2 * ∑ k : Fin 3, DA k
  have hCcurl : 0 ≤ Ccurl := by
    dsimp [Ccurl]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun k hk => hDA k)
  have hDAle (k : Fin 3) : DA k ≤ ∑ m : Fin 3, DA m :=
    Finset.single_le_sum (fun m _ => hDA m) (Finset.mem_univ k)
  have hcurlBound (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3) :
      |associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z i| ≤
        Ccurl * associatedPressureSpatialProfile K 2 z := by
    fin_cases i
    · change |associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 0| ≤ _
      rw [associatedPressureTestCurl_zero]
      rw [associatedPressureTestPartial_eq_spatialPartial,
        associatedPressureTestPartial_eq_spatialPartial]
      calc
        |CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 1 z -
          CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 2 z| ≤
          |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 1 z| +
            |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 2 z| :=
          associatedPressureAbs_sub_le _ _
        _ ≤ (DA 2 + DA 1) * associatedPressureSpatialProfile K 2 z := by
          calc
            _ ≤ DA 2 * associatedPressureSpatialProfile K 2 z +
                DA 1 * associatedPressureSpatialProfile K 2 z :=
              add_le_add (hcutDirA n z 2 1) (hcutDirA n z 1 2)
            _ = _ := by ring
        _ ≤ Ccurl * associatedPressureSpatialProfile K 2 z := by
          have hcoeff : DA 2 + DA 1 ≤ 2 * ∑ k : Fin 3, DA k := by
            calc
              _ ≤ (∑ k : Fin 3, DA k) + ∑ k : Fin 3, DA k :=
                add_le_add (hDAle 2) (hDAle 1)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hcoeff (hprofile z)
    · change |associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 1| ≤ _
      rw [associatedPressureTestCurl_one]
      rw [associatedPressureTestPartial_eq_spatialPartial,
        associatedPressureTestPartial_eq_spatialPartial]
      calc
        |CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 2 z -
          CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 0 z| ≤
          |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 2 z| +
            |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 0 z| :=
          associatedPressureAbs_sub_le _ _
        _ ≤ (DA 0 + DA 2) * associatedPressureSpatialProfile K 2 z := by
          calc
            _ ≤ DA 0 * associatedPressureSpatialProfile K 2 z +
                DA 2 * associatedPressureSpatialProfile K 2 z :=
              add_le_add (hcutDirA n z 0 2) (hcutDirA n z 2 0)
            _ = _ := by ring
        _ ≤ Ccurl * associatedPressureSpatialProfile K 2 z := by
          have hcoeff : DA 0 + DA 2 ≤ 2 * ∑ k : Fin 3, DA k := by
            calc
              _ ≤ (∑ k : Fin 3, DA k) + ∑ k : Fin 3, DA k :=
                add_le_add (hDAle 0) (hDAle 2)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hcoeff (hprofile z)
    · change |associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 2| ≤ _
      rw [associatedPressureTestCurl_two]
      rw [associatedPressureTestPartial_eq_spatialPartial,
        associatedPressureTestPartial_eq_spatialPartial]
      calc
        |CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 0 z -
          CKN.spatialPartialProd
            (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 1 z| ≤
          |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 0 z| +
            |CKN.spatialPartialProd
              (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 1 z| :=
          associatedPressureAbs_sub_le _ _
        _ ≤ (DA 1 + DA 0) * associatedPressureSpatialProfile K 2 z := by
          calc
            _ ≤ DA 1 * associatedPressureSpatialProfile K 2 z +
                DA 0 * associatedPressureSpatialProfile K 2 z :=
              add_le_add (hcutDirA n z 1 0) (hcutDirA n z 0 1)
            _ = _ := by ring
        _ ≤ Ccurl * associatedPressureSpatialProfile K 2 z := by
          have hcoeff : DA 1 + DA 0 ≤ 2 * ∑ k : Fin 3, DA k := by
            calc
              _ ≤ (∑ k : Fin 3, DA k) + ∑ k : Fin 3, DA k :=
                add_le_add (hDAle 1) (hDAle 0)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_right hcoeff (hprofile z)
  refine ⟨K, hK, hKsub, Ccurl + Dψ, add_nonneg hCcurl hDψ, ?_⟩
  intro n z i
  have hsum : associatedPressureHelmholtzTestCutoff φ n z i =
      associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z i +
        CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) i z := by
    rfl
  rw [hsum]
  calc
    |associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z i +
      CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) i z| ≤
      |associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z i| +
        |CKN.spatialPartialProd
          (associatedPressureHelmholtzScalarPotentialCutoff φ n) i z| := abs_add_le _ _
    _ ≤ (Ccurl + Dψ) * associatedPressureSpatialProfile K 2 z := by
      calc
        _ ≤ Ccurl * associatedPressureSpatialProfile K 2 z +
            Dψ * associatedPressureSpatialProfile K 2 z :=
          add_le_add (hcurlBound n z i) (hcutDirScalar n z i)
        _ = _ := by ring

end CKN.Leray

end
