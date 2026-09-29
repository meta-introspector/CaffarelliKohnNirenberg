-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedCutoffValue

/-!
# Quantitative Helmholtz cutoff estimates

Uniform pointwise decay bounds for derivatives of the cutoff potentials used
in `lem:helmholtz-test`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Absolute values of differences are subadditive under subtraction of
two terms. -/
theorem associatedPressureAbs_sub_sub_le (a b c d : ℝ) :
    |(a - b) - (c - d)| ≤ |a - c| + |b - d| := by
  calc
    |(a - b) - (c - d)| = |(a - c) - (b - d)| := by congr 1; ring
    _ ≤ |a - c| + |b - d| := associatedPressureAbs_sub_le _ _

/-- The first derivative of a cutoff decaying potential differs from its
uncut derivative by a uniform cubic spatial decay bound, as used in
`lem:helmholtz-test`. -/
theorem associatedPressurePotentialCutoff_direction_error_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ)
    (i : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
    |rieszPressureJointDirection (rieszPressurePotentialCutoffTest ψ n) i z -
      rieszPressureJointDirection ψ i z| ≤
      (CKN.cutoffGradientConstant *
        (28 / 13) * Classical.choose hdecay.value_bound +
        2 * Classical.choose hdecay.gradient_bound) *
        (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let s := rieszPressurePotentialCutoffScale n
  let η := rieszPressurePotentialCutoff n
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let CG := CKN.cutoffGradientConstant
  have hs1 : 1 ≤ s := by simpa [s] using rieszPressurePotentialCutoffScale_ge_one n
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hC0 : 0 ≤ C0 := (Classical.choose_spec hdecay.value_bound).1
  have hC1 : 0 ≤ C1 := (Classical.choose_spec hdecay.gradient_bound).1
  have hCG : 0 ≤ CG := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hv := (Classical.choose_spec hdecay.value_bound).2 z
  have hgrad := (Classical.choose_spec hdecay.gradient_bound).2 i z
  have hηbound := rieszPressurePotentialCutoff_bounds n z.1
  have hηgrad := rieszPressurePotentialCutoff_gradient_bound n i z.1
  have hscale := rieszPressurePotentialCutoff_outer n
  have houterRadius : 3 * rieszPressurePotentialCutoffRadius n / 4 =
      (15 / 13 : ℝ) * s := by
    calc
      3 * rieszPressurePotentialCutoffRadius n / 4 =
          15 * rieszPressurePotentialCutoffScale n / 13 := hscale
      _ = (15 / 13 : ℝ) * s := by simp [s]; ring
  have hformula :
      rieszPressureJointDirection (rieszPressurePotentialCutoffTest ψ n) i z =
        CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 * ψ z +
          rieszPressurePotentialCutoff n z.1 * rieszPressureJointDirection ψ i z := by
    rw [← rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTest_contDiff hψ n) i z,
      ← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
    have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoff n) :=
      CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
    have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
      hψ.comp (contDiff_id.prodMk contDiff_const)
    have hprod := CKN.spatialDeriv_mul
      ((hη.differentiable (by simp)) z.1)
      ((hψslice.differentiable (by simp)) z.1) i
    simpa [rieszPressurePotentialCutoffTest] using hprod
  by_cases hinner : z.1 ∈ CKN.euclideanBall 0 s
  · have hclosed : z.1 ∈ CKN.euclideanClosedBall 0 s := by
      apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (le_trans (by norm_num) hs1)).2
      exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hspos).1 hinner |>.le
    have hηone := rieszPressurePotentialCutoff_eq_one n hinner
    have hderivzero := rieszPressurePotentialCutoff_derivatives_zero_on_inner n hclosed
    have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
      change CKN.classicalGradient η z.1 i = 0
      rw [hderivzero.1]
      simp
    rw [hformula, hηgradzero, hηone]
    simp only [zero_mul, one_mul]
    simp
    have hcoeff : 0 ≤ CG * (28 / 13) * C0 + 2 * C1 := by positivity
    have hbase : 0 ≤ 1 + vec3EuclideanNorm z.1 := by
      have hn := vec3EuclideanNorm_nonneg z.1
      linarith only [hn]
    have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
      Real.rpow_nonneg hbase _
    simpa [CG, C0, C1] using mul_nonneg hcoeff hprof
  · have hvnorm : 0 < 1 + vec3EuclideanNorm z.1 := by
      have hn := vec3EuclideanNorm_nonneg z.1
      linarith only [hn]
    by_cases hout : z.1 ∈ CKN.euclideanBall 0
        (3 * rieszPressurePotentialCutoffRadius n / 4)
    · have houtnorm : vec3EuclideanNorm z.1 < (15 / 13 : ℝ) * s := by
        rw [← houterRadius]
        have houterpos : 0 < 3 * rieszPressurePotentialCutoffRadius n / 4 := by
          rw [houterRadius]
          positivity
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using
          (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt houterpos).1 hout
      have hrel : 1 + vec3EuclideanNorm z.1 ≤ (28 / 13 : ℝ) * s := by
        nlinarith only [houtnorm, hs1]
      have hrelInv : 1 / s ≤ (28 / 13 : ℝ) /
          (1 + vec3EuclideanNorm z.1) := by
        rw [div_le_div_iff₀ hspos hvnorm]
        nlinarith only [hrel]
      rw [hformula]
      have hfirst :
          |CKN.spatialDeriv η i z.1 * ψ z| ≤
            CG * (28 / 13) * C0 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
        rw [abs_mul]
        have hvalue' : |ψ z| ≤ C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ)) := hv
        have hgrad' : |CKN.spatialDeriv η i z.1| ≤ CG / s := hηgrad
        have hprod : |CKN.spatialDeriv η i z.1| * |ψ z| ≤
            (CG / s) * (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) :=
          mul_le_mul hgrad' hvalue' (abs_nonneg _) (by positivity)
        have hpower : (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ)) *
              (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) =
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          rw [← Real.rpow_add hvnorm]
          congr 1
          ring
        have hpowInv : (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) =
            1 / (1 + vec3EuclideanNorm z.1) := by
          rw [Real.rpow_neg hvnorm.le, Real.rpow_one]
          simp [div_eq_mul_inv]
        have hfactor : CG / s ≤ CG * (28 / 13) *
            (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) := by
          have hinv : 1 / s ≤ (28 / 13 : ℝ) *
              (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) := by
            simpa [hpowInv, div_eq_mul_inv] using hrelInv
          calc
            CG / s = CG * (1 / s) := by ring
            _ ≤ CG * ((28 / 13 : ℝ) *
                (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hinv hCG
            _ = _ := by ring
        calc
          _ ≤ (CG / s) * (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) := hprod
          _ ≤ (CG * (28 / 13) *
                (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ))) *
              (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_right hfactor (by positivity)
          _ = CG * (28 / 13) * C0 *
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
                rw [← hpower]
                ring
      have hetaMinus : |η z.1 - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith only [hηbound.1, hηbound.2]
      calc
        _ = |CKN.spatialDeriv η i z.1 * ψ z +
            (η z.1 - 1) * rieszPressureJointDirection ψ i z| := by
          congr 1
          ring
        _ ≤ |CKN.spatialDeriv η i z.1 * ψ z| +
            |(η z.1 - 1) * rieszPressureJointDirection ψ i z| := abs_add_le _ _
        _ = |CKN.spatialDeriv η i z.1 * ψ z| +
            |η z.1 - 1| * |rieszPressureJointDirection ψ i z| := by
              simp only [abs_mul]
        _ ≤ CG * (28 / 13) * C0 *
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
            C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          have hgrad' : |rieszPressureJointDirection ψ i z| ≤
              C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
            simpa [C1] using hgrad
          calc
            _ ≤ CG * (28 / 13) * C0 *
                  (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
                1 * |rieszPressureJointDirection ψ i z| :=
                  add_le_add hfirst
                    (mul_le_mul_of_nonneg_right hetaMinus (abs_nonneg _))
            _ ≤ _ := by
              calc
                _ = |rieszPressureJointDirection ψ i z| +
                    CG * (28 / 13) * C0 *
                      (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by ring
                _ ≤ C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
                    CG * (28 / 13) * C0 *
                      (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
                    add_le_add_left hgrad' _
                _ = _ := by ring
        _ ≤ (CG * (28 / 13) * C0 + 2 * C1) *
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
            Real.rpow_nonneg (by positivity) _
          have hcoeff : CG * (28 / 13) * C0 + C1 ≤
              CG * (28 / 13) * C0 + 2 * C1 := by
            nlinarith only [hC1]
          calc
            _ = (CG * (28 / 13) * C0 + C1) *
                (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hprof
    · have houterNotSupport : z.1 ∉ tsupport η := by
        intro hz
        have hsub := CKN.mollifiedBallCutoff_tsupport_subset_outer 0
          (rieszPressurePotentialCutoffRadius_pos n) hz
        exact hout (by simpa [η] using hsub)
      have hηzero : η z.1 = 0 := image_eq_zero_of_notMem_tsupport houterNotSupport
      have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
        rw [CKN.spatialDeriv]
        have hfd : fderiv ℝ η z.1 = 0 := fderiv_of_notMem_tsupport ℝ houterNotSupport
        rw [hfd]
        simp
      rw [hformula, hηgradzero]
      simp only [η, hηzero, zero_mul, zero_add]
      have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have hC : 0 ≤ CG * (28 / 13) * C0 + 2 * C1 := by positivity
      have hgrad' : |rieszPressureJointDirection ψ i z| ≤
          C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
        simpa [C1] using hgrad
      have hcoeff : C1 ≤ CG * (28 / 13) * C0 + 2 * C1 := by
        nlinarith only [hC0, hC1, hCG]
      simpa [η, CG, C0, C1, hηzero, hηgradzero] using
        hgrad'.trans (mul_le_mul_of_nonneg_right hcoeff hprof)


/-- The cutoff derivative agrees exactly with the original derivative on its
inner ball. -/
theorem associatedPressurePotentialCutoff_direction_eq_of_inner
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (n : ℕ) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0
      (rieszPressurePotentialCutoffScale n)) :
    rieszPressureJointDirection (rieszPressurePotentialCutoffTest ψ n) i z =
      rieszPressureJointDirection ψ i z := by
  let s := rieszPressurePotentialCutoffScale n
  let η := rieszPressurePotentialCutoff n
  have hs1 : 1 ≤ s := by simpa [s] using rieszPressurePotentialCutoffScale_ge_one n
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hclosed : z.1 ∈ CKN.euclideanClosedBall 0 s := by
    apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (le_trans (by norm_num) hs1)).2
    exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hspos).1 hx |>.le
  have hηone : η z.1 = 1 := by
    simpa [η, s] using rieszPressurePotentialCutoff_eq_one n hx
  have hderivzero := rieszPressurePotentialCutoff_derivatives_zero_on_inner n hclosed
  have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
    change CKN.classicalGradient η z.1 i = 0
    rw [hderivzero.1]
    simp
  have hcutone : rieszPressurePotentialCutoff n z.1 = 1 := by
    simpa [η] using hηone
  have hcutgrad : CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 = 0 := by
    simpa [η] using hηgradzero
  have hformula :
      rieszPressureJointDirection (rieszPressurePotentialCutoffTest ψ n) i z =
        CKN.spatialDeriv (rieszPressurePotentialCutoff n) i z.1 * ψ z +
          rieszPressurePotentialCutoff n z.1 * rieszPressureJointDirection ψ i z := by
    rw [← rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTest_contDiff hψ n) i z,
      ← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
    have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoff n) :=
      CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadius_pos n)
    have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
      hψ.comp (contDiff_id.prodMk contDiff_const)
    have hprod := CKN.spatialDeriv_mul
      ((hη.differentiable (by simp)) z.1)
      ((hψslice.differentiable (by simp)) z.1) i
    simpa [rieszPressurePotentialCutoffTest] using hprod
  rw [hformula, hcutgrad, hcutone]
  ring

end CKN.Leray
