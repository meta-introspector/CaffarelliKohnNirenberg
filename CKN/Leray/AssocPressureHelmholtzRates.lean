-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRateBase

/-!
# Helmholtz cutoff convergence rates

Pointwise bounds for the solenoidal cutoff field in `lem:helmholtz-test`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Each component of the solenoidal Helmholtz cutoff error is bounded by the
same cubic spatial decay profile, uniformly in the cutoff scale. -/
theorem associatedPressureHelmholtzCutoffCurl_component_error_profile
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3),
      |associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z i -
        associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) z i| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let A := associatedPressureHelmholtzVectorPotential φ
  let D : Fin 3 → ℝ := fun k =>
    CKN.cutoffGradientConstant * (28 / 13 : ℝ) *
        Classical.choose (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound +
      2 * Classical.choose (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound
  let C : ℝ := 2 * ∑ k : Fin 3, D k
  have hCG : 0 ≤ CKN.cutoffGradientConstant := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hD (k : Fin 3) : 0 ≤ D k := by
    dsimp [D]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hCG (by norm_num))
        (Classical.choose_spec
          (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound).1)
      (mul_nonneg (by norm_num)
        (Classical.choose_spec
          (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound).1)
  have hsum : 0 ≤ ∑ k : Fin 3, D k := Finset.sum_nonneg fun k hk => hD k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAle (k : Fin 3) : D k ≤ ∑ l : Fin 3, D l :=
    Finset.single_le_sum (fun l hl => hD l) (Finset.mem_univ k)
  refine ⟨C, hC, ?_⟩
  intro n z i
  have hAcont : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hAcont
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
    rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z = _
    rw [← hjoint]
    rfl
  have hbasePartial (k l : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) l z =
        rieszPressureJointDirection (fun q => A q k) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    change CKN.spatialPartialProd (fun q => A q k) l z = _
    rw [← hjoint]
    rfl
  have hdirErr (k l : Fin 3) :
      |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z -
        rieszPressureJointDirection (fun q => A q k) l z| ≤
        D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    have hdecay := (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1
    have h := associatedPressurePotentialCutoff_direction_error_bound
      (hAcomp k) hdecay l n z
    simpa [D, A] using h
  have hbase : 0 ≤ 1 + vec3EuclideanNorm z.1 := by
    have hn := vec3EuclideanNorm_nonneg z.1
    linarith only [hn]
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg hbase _
  have hpair (k l m p : Fin 3) :
      |(associatedPressureTestPartial
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z -
        associatedPressureTestPartial
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q m) p z) -
       (associatedPressureTestPartial (fun q => A q k) l z -
        associatedPressureTestPartial (fun q => A q m) p z)| ≤
      (D k + D m) * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    rw [hcutPartial, hcutPartial, hbasePartial, hbasePartial]
    calc
      _ ≤ |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z -
            rieszPressureJointDirection (fun q => A q k) l z| +
          |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTest (fun q => A q m) n) p z -
            rieszPressureJointDirection (fun q => A q m) p z| :=
        associatedPressureAbs_sub_sub_le _ _ _ _
      _ ≤ _ := by
        calc
          _ ≤ D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
              D m * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
            add_le_add (hdirErr k l) (hdirErr m p)
          _ = _ := by ring
  have hcoeff (k m : Fin 3) : D k + D m ≤ C := by
    calc
      D k + D m ≤ (∑ l : Fin 3, D l) + ∑ l : Fin 3, D l :=
        add_le_add (hAle k) (hAle m)
      _ = C := by dsimp [C]; ring
  fin_cases i
  · change |associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z 0 -
        associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) z 0| ≤ _
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero]
    exact (hpair 2 1 1 2).trans
      (mul_le_mul_of_nonneg_right (hcoeff 2 1) hprofile)
  · change |associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z 1 -
        associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) z 1| ≤ _
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one]
    exact (hpair 0 2 2 0).trans
      (mul_le_mul_of_nonneg_right (hcoeff 0 2) hprofile)
  · change |associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) z 2 -
        associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) z 2| ≤ _
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two]
    exact (hpair 1 0 0 1).trans
      (mul_le_mul_of_nonneg_right (hcoeff 1 0) hprofile)


/-- The solenoidal Helmholtz cutoff agrees with the full solenoidal field on
its inner spatial ball. -/
theorem associatedPressureHelmholtzCutoffCurl_eq_of_inner
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n)) :
    associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z =
      associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z := by
  let A := associatedPressureHelmholtzVectorPotential φ
  have hAcont : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hAcont
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
    rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z = _
    rw [← hjoint]
    rfl
  have hbasePartial (k l : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) l z =
        rieszPressureJointDirection (fun q => A q k) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    change CKN.spatialPartialProd (fun q => A q k) l z = _
    rw [← hjoint]
    rfl
  have hdirEq (k l : Fin 3) :
      rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z =
        rieszPressureJointDirection (fun q => A q k) l z :=
    associatedPressurePotentialCutoff_direction_eq_of_inner (hAcomp k) l n z hx
  ext i
  fin_cases i
  · change associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 0 =
      associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z 0
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 1 =
      associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z 1
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z 2 =
      associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z 2
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]

end CKN.Leray
