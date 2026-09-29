-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRealCutoff

/-!
# Real-radius Helmholtz cutoff estimates

The cutoff errors and their spatial derivatives satisfy scale-uniform decay
bounds at every real radius at least one.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The cutoff derivative equals the uncut derivative on the inner ball. -/
theorem associatedPressurePotentialCutoffReal_direction_eq_of_inner
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 R) :
    rieszPressureJointDirection
        (rieszPressurePotentialCutoffTestReal ψ R hR) i z =
      rieszPressureJointDirection ψ i z := by
  let η := rieszPressurePotentialCutoffReal R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hclosed : z.1 ∈ CKN.euclideanClosedBall 0 R := by
    apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (le_trans (by norm_num) hR)).2
    exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 hx |>.le
  have hηone : η z.1 = 1 := by
    simpa [η] using rieszPressurePotentialCutoffReal_eq_one R hR hx
  have hηone' : rieszPressurePotentialCutoffReal R hR z.1 = 1 := by
    simpa [η] using hηone
  have hderivzero := rieszPressurePotentialCutoffReal_derivatives_zero_on_inner
    R hR hclosed
  have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
    change CKN.classicalGradient η z.1 i = 0
    rw [hderivzero.1]
    simp
  have hformula :
      rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal ψ R hR) i z =
        CKN.spatialDeriv η i z.1 * ψ z +
          η z.1 * rieszPressureJointDirection ψ i z := by
    rw [← rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTestReal_contDiff hψ R hR) i z,
      ← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
    have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η :=
      CKN.mollifiedBallCutoff_smooth 0
        (rieszPressurePotentialCutoffRadiusReal_pos R hR)
    have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
      hψ.comp (contDiff_id.prodMk contDiff_const)
    have hprod := CKN.spatialDeriv_mul
      ((hηsmooth.differentiable (by simp)) z.1)
      ((hψslice.differentiable (by simp)) z.1) i
    simpa [rieszPressurePotentialCutoffTestReal] using hprod
  have hηone' : η z.1 = 1 := hηone
  rw [hformula, hηgradzero, hηone']
  ring_nf

/-- The Hessian of a real-radius cutoff product obeys the spatial product
rule. -/
theorem rieszPressurePotentialCutoffTestReal_hessian_formula
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (R : ℝ) (hR : 1 ≤ R) (i j : Fin 3) (z : Vec3 × ℝ) :
    rieszPressureJointHessian
        (rieszPressurePotentialCutoffTestReal ψ R hR) i j z =
      CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j z.1 * ψ z +
      CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j z.1 *
        rieszPressureJointDirection ψ i z +
      CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i z.1 *
        rieszPressureJointDirection ψ j z +
      rieszPressurePotentialCutoffReal R hR z.1 *
        rieszPressureJointHessian ψ i j z := by
  let η := rieszPressurePotentialCutoffReal R hR
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR)
  have hψt : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
    hψ.comp (contDiff_id.prodMk contDiff_const)
  have hcutSlice := rieszPressure_sliceMixedSecond_eq_joint
    (rieszPressurePotentialCutoffTestReal_contDiff hψ R hR) i j z
  have hψSlice := rieszPressure_sliceMixedSecond_eq_joint hψ i j z
  have hdirI := rieszPressure_sliceSpatialDeriv_eq_joint hψ i z
  have hdirJ := rieszPressure_sliceSpatialDeriv_eq_joint hψ j z
  rw [← hcutSlice]
  change CKN.mixedSecond (fun x => η x * ψ (x, z.2)) i j z.1 = _
  rw [CKN.spatialSecondDeriv_mul_smooth hη hψt i j z.1]
  dsimp [η]
  rw [hψSlice, hdirI, hdirJ]

private theorem hp_abs_four_add_le (a b c d : ℝ) :
    |a + b + c + d| ≤ |a| + |b| + (|c| + |d|) := by
  calc
    |a + b + c + d| ≤ |a + b + c| + |d| := by
      rw [show a + b + c + d = (a + b + c) + d by ring_nf]
      exact abs_add_le _ _
    _ ≤ (|a + b| + |c|) + |d| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |a| + |b| + (|c| + |d|) := by
      calc
        _ = (|a + b| + |c|) + |d| := by ring_nf
        _ ≤ (|a| + |b| + |c|) + |d| := by
          gcongr
          exact abs_add_le _ _
        _ = |a| + |b| + (|c| + |d|) := by ring_nf

/-- The real-radius Hessian cutoff error is bounded by the fourth-order
spatial profile on a compact time support. -/
theorem rieszPressurePotentialHessianCutoffRealError_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ)
    (i j : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) :
    |rieszPressureJointHessian
        (rieszPressurePotentialCutoffTestReal ψ R hR) i j z -
      rieszPressureJointHessian ψ i j z| ≤
      (Classical.choose hdecay.hessian_bound +
        6 * CKN.cutoffGradientConstant * Classical.choose hdecay.gradient_bound +
        9 * CKN.cutoffSecondDerivativeConstant * Classical.choose hdecay.value_bound) *
      rieszPressurePotentialSpatialProfile Set.univ z := by
  classical
  let K : Set ℝ := Set.univ
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let C2 := Classical.choose hdecay.hessian_bound
  let CG := CKN.cutoffGradientConstant
  let CH := CKN.cutoffSecondDerivativeConstant
  have hspec0 := Classical.choose_spec hdecay.value_bound
  have hspec1 := Classical.choose_spec hdecay.gradient_bound
  have hspec2 := Classical.choose_spec hdecay.hessian_bound
  have hC0 : 0 ≤ C0 := hspec0.1
  have hC1 : 0 ≤ C1 := hspec1.1
  have hC2 : 0 ≤ C2 := hspec2.1
  have hconstG : 0 ≤ CG := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hconstH : 0 ≤ CH := by
    have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (norm_nonneg _) (by simpa using h)
  have hcoeff : 0 ≤ C2 + 6 * CG * C1 + 9 * CH * C0 := by positivity
  by_cases ht : z.2 ∈ K
  · let a : ℝ := 1 + ‖z.1‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hprofile : rieszPressurePotentialSpatialProfile K z =
        a ^ (-(4 : ℝ)) := by
      simp [rieszPressurePotentialSpatialProfile, K, a, ht]
    have hvalue : |ψ z| ≤ C0 * a ^ (-(2 : ℝ)) := by
      have hpow : (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ)) ≤
          (1 + ‖z.1‖) ^ (-(2 : ℝ)) := by
        have hnorm := norm_le_vec3EuclideanNorm z.1
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith only [hnorm]) (by norm_num)
      exact (hspec0.2 z).trans (mul_le_mul_of_nonneg_left hpow hC0)
    have hgradient (k : Fin 3) :
        |rieszPressureJointDirection ψ k z| ≤ C1 * a ^ (-(3 : ℝ)) := by
      have hpow : (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) ≤
          (1 + ‖z.1‖) ^ (-(3 : ℝ)) := by
        have hnorm := norm_le_vec3EuclideanNorm z.1
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith only [hnorm]) (by norm_num)
      exact (hspec1.2 k z).trans (mul_le_mul_of_nonneg_left hpow hC1)
    have hhessian (k l : Fin 3) :
        |rieszPressureJointHessian ψ k l z| ≤ C2 * a ^ (-(4 : ℝ)) := by
      have hpow : (1 + vec3EuclideanNorm z.1) ^ (-(4 : ℝ)) ≤
          (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
        have hnorm := norm_le_vec3EuclideanNorm z.1
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith only [hnorm]) (by norm_num)
      exact (hspec2.2 k l z).trans (mul_le_mul_of_nonneg_left hpow hC2)
    have hcutgrad (k : Fin 3) :
        |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) k z.1| ≤
          3 * CG * a⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoffReal_gradient_profile_bound R hR k z.1
    have hcuthess (k l : Fin 3) :
        |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) k l z.1| ≤
          9 * CH * (a ^ 2)⁻¹ := by
      simpa [a, div_eq_mul_inv, mul_assoc] using
        rieszPressurePotentialCutoffReal_hessian_profile_bound R hR k l z.1
    have heta := rieszPressurePotentialCutoffReal_bounds R hR z.1
    have heta' : |rieszPressurePotentialCutoffReal R hR z.1 - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith only [heta.1, heta.2]
    have hmain : |(rieszPressurePotentialCutoffReal R hR z.1 - 1) *
        rieszPressureJointHessian ψ i j z| ≤ C2 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        |rieszPressurePotentialCutoffReal R hR z.1 - 1| *
            |rieszPressureJointHessian ψ i j z| ≤
            1 * (C2 * a ^ (-(4 : ℝ))) :=
          mul_le_mul heta' (hhessian i j) (abs_nonneg _) (by norm_num)
        _ = C2 * a ^ (-(4 : ℝ)) := by ring_nf
    have hcross₁ :
        |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j z.1 *
          rieszPressureJointDirection ψ i z| ≤
          3 * CG * C1 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        _ ≤ (3 * CG * a⁻¹) * (C1 * a ^ (-(3 : ℝ)) ) :=
          mul_le_mul (hcutgrad j) (hgradient i) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hconstG)
              (inv_nonneg.mpr (le_of_lt ha)))
        _ = 3 * CG * C1 * a ^ (-(4 : ℝ)) := by
          calc
            _ = (3 * CG * C1) * (a⁻¹ * a ^ (-(3 : ℝ))) := by ring_nf
            _ = 3 * CG * C1 * a ^ (-(4 : ℝ)) := by
              rw [show a⁻¹ = a ^ (-(1 : ℝ)) by
                rw [Real.rpow_neg ha.le, Real.rpow_one, inv_eq_one_div]]
              rw [← Real.rpow_add ha]
              congr 1
              norm_num
    have hcross₂ :
        |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i z.1 *
          rieszPressureJointDirection ψ j z| ≤
          3 * CG * C1 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        _ ≤ (3 * CG * a⁻¹) * (C1 * a ^ (-(3 : ℝ)) ) :=
          mul_le_mul (hcutgrad i) (hgradient j) (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hconstG)
              (inv_nonneg.mpr (le_of_lt ha)))
        _ = 3 * CG * C1 * a ^ (-(4 : ℝ)) := by
          calc
            _ = (3 * CG * C1) * (a⁻¹ * a ^ (-(3 : ℝ))) := by ring_nf
            _ = 3 * CG * C1 * a ^ (-(4 : ℝ)) := by
              rw [show a⁻¹ = a ^ (-(1 : ℝ)) by
                rw [Real.rpow_neg ha.le, Real.rpow_one, inv_eq_one_div]]
              rw [← Real.rpow_add ha]
              congr 1
              norm_num
    have hcutvalue :
        |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j z.1 * ψ z| ≤
          9 * CH * C0 * a ^ (-(4 : ℝ)) := by
      rw [abs_mul]
      calc
        _ ≤ (9 * CH * (a ^ 2)⁻¹) * (C0 * a ^ (-(2 : ℝ))) :=
          mul_le_mul (hcuthess i j) hvalue (abs_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num) hconstH)
              (inv_nonneg.mpr (sq_nonneg a)))
        _ = 9 * CH * C0 * a ^ (-(4 : ℝ)) := by
          have hpow : (a⁻¹) ^ (2 : ℕ) = a ^ (-(2 : ℝ)) := by
            rw [Real.rpow_neg ha.le]
            calc
              _ = (a ^ (2 : ℕ))⁻¹ := inv_pow a 2
              _ = (a ^ (2 : ℝ))⁻¹ := by
                congr 1
                exact (Real.rpow_natCast a 2).symm
          calc
            _ = 9 * CH * C0 * ((a⁻¹) ^ (2 : ℕ) * a ^ (-(2 : ℝ))) := by ring_nf
            _ = 9 * CH * C0 * (a ^ (-(2 : ℝ)) * a ^ (-(2 : ℝ))) := by rw [hpow]
            _ = 9 * CH * C0 * a ^ (-(4 : ℝ)) := by
              rw [← Real.rpow_add ha]
              congr 1
              norm_num
    have herrFormula :
        rieszPressureJointHessian
            (rieszPressurePotentialCutoffTestReal ψ R hR) i j z -
          rieszPressureJointHessian ψ i j z =
        (rieszPressurePotentialCutoffReal R hR z.1 - 1) *
            rieszPressureJointHessian ψ i j z +
          CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j z.1 *
            rieszPressureJointDirection ψ i z +
          CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i z.1 *
            rieszPressureJointDirection ψ j z +
          CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j z.1 * ψ z := by
      rw [rieszPressurePotentialCutoffTestReal_hessian_formula hψ R hR i j z]
      ring_nf
    rw [herrFormula]
    rw [hprofile]
    calc
      _ ≤ |(rieszPressurePotentialCutoffReal R hR z.1 - 1) *
            rieszPressureJointHessian ψ i j z| +
          |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j z.1 *
            rieszPressureJointDirection ψ i z| +
          (|CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i z.1 *
            rieszPressureJointDirection ψ j z| +
            |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j z.1 * ψ z|) := by
        have habs := hp_abs_four_add_le
          ((rieszPressurePotentialCutoffReal R hR z.1 - 1) *
            rieszPressureJointHessian ψ i j z)
          (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j z.1 *
            rieszPressureJointDirection ψ i z)
          (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i z.1 *
            rieszPressureJointDirection ψ j z)
          (CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j z.1 * ψ z)
        simpa only [add_assoc] using habs
      _ ≤ C2 * a ^ (-(4 : ℝ)) +
          3 * CG * C1 * a ^ (-(4 : ℝ)) +
          (3 * CG * C1 * a ^ (-(4 : ℝ)) +
            9 * CH * C0 * a ^ (-(4 : ℝ))) := by
        simpa only [add_assoc] using add_le_add hmain
          (add_le_add hcross₁ (add_le_add hcross₂ hcutvalue))
      _ = (C2 + 6 * CG * C1 + 9 * CH * C0) * a ^ (-(4 : ℝ)) := by ring_nf
      _ = (C2 + 6 * CG * C1 + 9 * CH * C0) *
          (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by rfl
  · exact (ht (Set.mem_univ z.2)).elim

/-- A smooth vector field and its real-radius cutoff have equal curls on the
inner ball. -/
theorem associatedPressureHelmholtzCutoffCurlReal_eq_of_inner
    (A : Vec3 × ℝ → Vec3) (hAcont : ContDiff ℝ (⊤ : ℕ∞) A)
    (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 R) :
    associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z =
      associatedPressureTestCurl A z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => A q k) := (contDiff_apply ℝ ℝ k).comp hAcont
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) :=
    rieszPressurePotentialCutoffTestReal_contDiff (hAcomp k) R hR
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k)
          l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l z = _
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
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z =
        rieszPressureJointDirection (fun q => A q k) l z :=
    associatedPressurePotentialCutoffReal_direction_eq_of_inner (hAcomp k)
      l R hR z hx
  ext i
  fin_cases i
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 0 =
      associatedPressureTestCurl A z 0
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 1 =
      associatedPressureTestCurl A z 1
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 2 =
      associatedPressureTestCurl A z 2
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]

/-- The Hessian of a cutoff potential agrees with the original Hessian on the
closed inner ball. -/
theorem rieszPressurePotentialCutoffReal_hessian_eq_of_inner
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (i j : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 R)
    (hxClosed : z.1 ∈ CKN.euclideanClosedBall 0 R) :
    rieszPressureJointHessian
        (rieszPressurePotentialCutoffTestReal ψ R hR) i j z =
      rieszPressureJointHessian ψ i j z := by
  let η := rieszPressurePotentialCutoffReal R hR
  have hηone : η z.1 = 1 := by
    simpa [η] using rieszPressurePotentialCutoffReal_eq_one R hR hx
  have hηone' : rieszPressurePotentialCutoffReal R hR z.1 = 1 := by
    simpa [η] using hηone
  have hderivzero := rieszPressurePotentialCutoffReal_derivatives_zero_on_inner
    R hR hxClosed
  have hηgradzero (k : Fin 3) : CKN.spatialDeriv η k z.1 = 0 := by
    change CKN.classicalGradient η z.1 k = 0
    rw [hderivzero.1]
    simp
  have hηhesszero (k l : Fin 3) : CKN.mixedSecond η k l z.1 = 0 := by
    have hηsmooth : ContDiff ℝ (⊤ : ℕ∞) η :=
      CKN.mollifiedBallCutoff_smooth 0
        (rieszPressurePotentialCutoffRadiusReal_pos R hR)
    have hgrad : ContDiff ℝ (⊤ : ℕ∞) (CKN.classicalGradient η) := by
      rw [contDiff_pi]
      intro m
      change ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv η m)
      exact CKN.contDiff_spatialDeriv_smooth hηsmooth m
    change CKN.spatialDeriv (CKN.spatialDeriv η l) k z.1 = 0
    change (fderiv ℝ (fun y : Vec3 => CKN.classicalGradient η y l) z.1)
      (CKN.basisVec k) = 0
    rw [fderiv_apply (hgrad.differentiable (by norm_num) z.1) l,
      hderivzero.2]
    rfl
  rw [rieszPressurePotentialCutoffTestReal_hessian_formula hψ R hR i j z]
  rw [hηhesszero i j, hηgradzero j, hηgradzero i, hηone']
  simp

/-- A smooth vector field and its real-radius cutoff have equal curl
derivatives on the closed inner ball. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_eq_of_inner
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) (i j : Fin 3)
    (hx : z.1 ∈ CKN.euclideanBall 0 R)
    (hxClosed : z.1 ∈ CKN.euclideanClosedBall 0 R) :
    CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (fun w => rieszPressurePotentialCutoffReal R hR w.1 • A w) q i) j z =
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => rieszPressurePotentialCutoffReal R hR q.1 • A q) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR)).comp contDiff_fst |>.smul hA
  have hdouble (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    have hcutcomp : ContDiff ℝ (⊤ : ℕ∞)
        (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) :=
      rieszPressurePotentialCutoffTestReal_contDiff (hAcomp k) R hR
    have hcutId := rieszPressure_sliceMixedSecond_eq_joint hcutcomp j l z
    have hEq := rieszPressurePotentialCutoffReal_hessian_eq_of_inner
      (hAcomp k) j l R hR z hx hxClosed
    have hAId := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    change CKN.mixedSecond
        (fun x : Vec3 =>
          (rieszPressurePotentialCutoffReal R hR x • A (x, z.2)) k)
        j l z.1 = _
    exact hcutId.trans (hEq.trans hAId.symm)
  have hdouble' (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => rieszPressurePotentialCutoffReal R hR q.1 * A q k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hdouble k l
  have hpCurlFormula {B : Vec3 × ℝ → Vec3}
      (hB : ContDiff ℝ (⊤ : ℕ∞) B) (a b : Fin 3) (q : Vec3 × ℝ) :
      CKN.spatialPartialProd (fun y => associatedPressureTestCurl B y a) b q =
        match a with
        | 0 => CKN.spatialSecondPartialProd (fun y => B y 2) 1 b q -
            CKN.spatialSecondPartialProd (fun y => B y 1) 2 b q
        | 1 => CKN.spatialSecondPartialProd (fun y => B y 0) 2 b q -
            CKN.spatialSecondPartialProd (fun y => B y 2) 0 b q
        | 2 => CKN.spatialSecondPartialProd (fun y => B y 1) 0 b q -
            CKN.spatialSecondPartialProd (fun y => B y 0) 1 b q := by
    have hBcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => B y k) :=
      (contDiff_apply ℝ ℝ k).comp hB
    have hpart (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => associatedPressureTestPartial (fun w => B w k) l y) := by
      have h := CKN.spatialPartial_contDiff (hBcomp k) l
      convert h using 1
      funext y
      exact associatedPressureTestPartial_eq_spatialPartial (fun w => B w k) l y
    fin_cases a
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 2) 1 y -
          associatedPressureTestPartial (fun w => B w 1) 2 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 2 1).differentiable (by simp) q)
        ((hpart 1 2).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 0) 2 y -
          associatedPressureTestPartial (fun w => B w 2) 0 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 0 2).differentiable (by simp) q)
        ((hpart 2 0).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 1) 0 y -
          associatedPressureTestPartial (fun w => B w 0) 1 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 1 0).differentiable (by simp) q)
        ((hpart 0 1).differentiable (by simp) q) b]
      rfl
  rw [hpCurlFormula hcutA i j z, hpCurlFormula hA i j z]
  fin_cases i
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 2) 1 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 1) 2 j z =
      CKN.spatialSecondPartialProd (fun q => A q 2) 1 j z -
        CKN.spatialSecondPartialProd (fun q => A q 1) 2 j z
    simp [hdouble']
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 0) 2 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 2) 0 j z =
      CKN.spatialSecondPartialProd (fun q => A q 0) 2 j z -
        CKN.spatialSecondPartialProd (fun q => A q 2) 0 j z
    simp [hdouble']
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 1) 0 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 0) 1 j z =
      CKN.spatialSecondPartialProd (fun q => A q 1) 0 j z -
        CKN.spatialSecondPartialProd (fun q => A q 0) 1 j z
    simp [hdouble']

private theorem hp_cutoffCurlReal_spatial_error_profile
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (H : Fin 3 → ℝ) (hH : ∀ k, 0 ≤ H k)
    (hHessErr : ∀ (k l m : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ),
      |rieszPressureJointHessian
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l m z -
        rieszPressureJointHessian (fun q => A q k) l m z| ≤
        H k * (1 + ‖z.1‖) ^ (-(4 : ℝ))) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) (i j : Fin 3),
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (fun w => rieszPressurePotentialCutoffReal R hR w.1 • A w) q i) j z -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl A q i) j z| ≤
        C * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
  let C : ℝ := 2 * ∑ k : Fin 3, H k
  have hsum : 0 ≤ ∑ k : Fin 3, H k := Finset.sum_nonneg fun k hk => hH k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAle (k : Fin 3) : H k ≤ ∑ l : Fin 3, H l :=
    Finset.single_le_sum (fun l hl => hH l) (Finset.mem_univ k)
  refine ⟨C, hC, ?_⟩
  intro R hR z i j
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => rieszPressurePotentialCutoffReal R hR q.1 • A q) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR)).comp contDiff_fst |>.smul hA
  have hpCurlFormula {B : Vec3 × ℝ → Vec3}
      (hB : ContDiff ℝ (⊤ : ℕ∞) B) (a b : Fin 3) (q : Vec3 × ℝ) :
      CKN.spatialPartialProd (fun y => associatedPressureTestCurl B y a) b q =
        match a with
        | 0 => CKN.spatialSecondPartialProd (fun y => B y 2) 1 b q -
            CKN.spatialSecondPartialProd (fun y => B y 1) 2 b q
        | 1 => CKN.spatialSecondPartialProd (fun y => B y 0) 2 b q -
            CKN.spatialSecondPartialProd (fun y => B y 2) 0 b q
        | 2 => CKN.spatialSecondPartialProd (fun y => B y 1) 0 b q -
            CKN.spatialSecondPartialProd (fun y => B y 0) 1 b q := by
    have hBcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => B y k) :=
      (contDiff_apply ℝ ℝ k).comp hB
    have hpart (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => associatedPressureTestPartial (fun w => B w k) l y) := by
      have h := CKN.spatialPartial_contDiff (hBcomp k) l
      convert h using 1
      funext y
      exact associatedPressureTestPartial_eq_spatialPartial (fun w => B w k) l y
    fin_cases a
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 2) 1 y -
          associatedPressureTestPartial (fun w => B w 1) 2 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 2 1).differentiable (by simp) q)
        ((hpart 1 2).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 0) 2 y -
          associatedPressureTestPartial (fun w => B w 2) 0 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 0 2).differentiable (by simp) q)
        ((hpart 2 0).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 1) 0 y -
          associatedPressureTestPartial (fun w => B w 0) 1 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 1 0).differentiable (by simp) q)
        ((hpart 0 1).differentiable (by simp) q) b]
      rfl
  have hcutHess (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l j z =
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) j l z := by
    have hcutcomp := rieszPressurePotentialCutoffTestReal_contDiff (hAcomp k) R hR
    have hjoint := rieszPressure_sliceMixedSecond_eq_joint hcutcomp j l z
    change CKN.mixedSecond
        (fun x : Vec3 =>
          (rieszPressurePotentialCutoffReal R hR x • A (x, z.2)) k) j l z.1 = _
    exact hjoint
  have hbaseHess (k l : Fin 3) :
      CKN.spatialSecondPartialProd (fun q => A q k) l j z =
        rieszPressureJointHessian (fun q => A q k) j l z := by
    have hjoint := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    change CKN.mixedSecond (fun x : Vec3 => A (x, z.2) k) j l z.1 = _
    exact hjoint
  have hHessBound (k l : Fin 3) :
      |CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l j z -
        CKN.spatialSecondPartialProd (fun q => A q k) l j z| ≤
        H k * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    rw [hcutHess k l, hbaseHess k l]
    exact hHessErr k j l R hR z
  have hprofile : 0 ≤ (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hpair (k l m p : Fin 3) :
      |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) m) p j z) -
       (CKN.spatialSecondPartialProd (fun q => A q k) l j z -
        CKN.spatialSecondPartialProd (fun q => A q m) p j z)| ≤
      (H k + H m) * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    calc
      _ ≤ |CKN.spatialSecondPartialProd
            (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l j z -
            CKN.spatialSecondPartialProd (fun q => A q k) l j z| +
          |CKN.spatialSecondPartialProd
            (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) m) p j z -
            CKN.spatialSecondPartialProd (fun q => A q m) p j z| :=
        associatedPressureAbs_sub_sub_le _ _ _ _
      _ ≤ _ := by
        calc
          _ ≤ H k * (1 + ‖z.1‖) ^ (-(4 : ℝ)) +
              H m * (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
            add_le_add (hHessBound k l) (hHessBound m p)
          _ = _ := by ring_nf
  have hcoeff (k m : Fin 3) : H k + H m ≤ C := by
    calc
      H k + H m ≤ (∑ l : Fin 3, H l) + ∑ l : Fin 3, H l :=
        add_le_add (hAle k) (hAle m)
      _ = C := by dsimp [C]; ring_nf
  have hcurlSub :
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (fun w => rieszPressurePotentialCutoffReal R hR w.1 • A w) q i) j z -
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z| ≤
        C * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    rw [hpCurlFormula hcutA i j z, hpCurlFormula hA i j z]
    fin_cases i
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 2) 1 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 1) 2 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 2) 1 j z -
        CKN.spatialSecondPartialProd (fun q => A q 1) 2 j z)| ≤ _
      exact (hpair 2 1 1 2).trans
        (mul_le_mul_of_nonneg_right (hcoeff 2 1) hprofile)
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 0) 2 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 2) 0 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 0) 2 j z -
        CKN.spatialSecondPartialProd (fun q => A q 2) 0 j z)| ≤ _
      exact (hpair 0 2 2 0).trans
        (mul_le_mul_of_nonneg_right (hcoeff 0 2) hprofile)
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 1) 0 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) 0) 1 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 1) 0 j z -
        CKN.spatialSecondPartialProd (fun q => A q 0) 1 j z)| ≤ _
      exact (hpair 1 0 0 1).trans
        (mul_le_mul_of_nonneg_right (hcoeff 1 0) hprofile)
  exact hcurlSub

/-- Each spatial derivative of the real-radius cutoff curl has a fourth order
decay profile in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_error_profile
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) (i j : Fin 3),
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) j z -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j z| ≤
        C * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
  let A := associatedPressureHelmholtzVectorPotential φ
  let H : Fin 3 → ℝ := fun k =>
    Classical.choose
        (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.hessian_bound +
      6 * CKN.cutoffGradientConstant * Classical.choose
        (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound +
      9 * CKN.cutoffSecondDerivativeConstant * Classical.choose
        (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound
  have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hSecondC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
    have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (norm_nonneg _) (by simpa using h)
  have hH (k : Fin 3) : 0 ≤ H k := by
    have h0 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.hessian_bound).1
    have h1 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound).1
    have h2 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound).1
    dsimp [H]
    positivity
  have hHessErr (k l m : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) :
      |rieszPressureJointHessian
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l m z -
        rieszPressureJointHessian (fun q => A q k) l m z| ≤
        H k * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    have hAcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
      (contDiff_apply ℝ ℝ k).comp
        (associatedPressureHelmholtzVectorPotential_contDiff hφ)
    have h := rieszPressurePotentialHessianCutoffRealError_bound hAcomp
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1 l m R hR z
    simpa [H, rieszPressurePotentialSpatialProfile] using h
  obtain ⟨C, hC, hprofile⟩ := hp_cutoffCurlReal_spatial_error_profile
    A (associatedPressureHelmholtzVectorPotential_contDiff hφ) H hH hHessErr
  refine ⟨C, hC, ?_⟩
  intro R hR z i j
  change |CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (fun w => rieszPressurePotentialCutoffReal R hR w.1 •
          associatedPressureHelmholtzVectorPotential φ w) q i) j z -
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) q i) j z| ≤ _
  exact hprofile R hR z i j

private theorem hp_cutoffPotentialReal_timePartial
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (R : ℝ) (hR : 1 ≤ R) (i : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartial
      (fun w => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR w i) z =
      rieszPressurePotentialCutoffReal R hR z.1 *
        associatedPressureHelmholtzVectorPotentialTimePartial φ z i := by
  let A : Vec3 × ℝ → ℝ := fun q => associatedPressureHelmholtzVectorPotential φ q i
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    exact (contDiff_apply ℝ ℝ i).comp
      (associatedPressureHelmholtzVectorPotential_contDiff hφ)
  have htimeA : DifferentiableAt ℝ (fun t : ℝ => A (z.1, t)) z.2 := by
    exact ((hA.differentiable (by simp)).differentiableAt).comp z.2 (by fun_prop)
  have hcut : (fun t : ℝ =>
      associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR (z.1, t) i) =
      (fun _ : ℝ => rieszPressurePotentialCutoffReal R hR z.1) *
        (fun t => A (z.1, t)) := by
    funext t
    simp [A, associatedPressureHelmholtzCutoffVectorPotentialReal, smul_eq_mul]
  have hconst : DifferentiableAt ℝ
      (fun _ : ℝ => rieszPressurePotentialCutoffReal R hR z.1) z.2 :=
    differentiableAt_const _
  change (fderiv ℝ
      (fun t : ℝ => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR
        (z.1, t) i) z.2) 1 = _
  rw [hcut, fderiv_mul hconst htimeA]
  simp [A, CKN.timePartial, associatedPressureHelmholtzVectorPotentialTimePartial]

/-- The time derivative of the real-radius cutoff curl is the curl of the
cutoff vector-potential time derivative. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (R : ℝ) (hR : 1 ≤ R) (i : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) z =
      associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 •
          associatedPressureHelmholtzVectorPotentialTimePartial φ q) z i := by
  have hcut := associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
    hφ R hR
  have hcomm := associatedPressureTestCurl_timePartial hcut.1 i z
  have hcomponent (k : Fin 3) (q : Vec3 × ℝ) :=
    hp_cutoffPotentialReal_timePartial hφ R hR k q
  have hcomponent' (k : Fin 3) (q : Vec3 × ℝ) :
      associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR y k) q =
        rieszPressurePotentialCutoffReal R hR q.1 *
          associatedPressureHelmholtzVectorPotentialTimePartial φ q k := by
    change CKN.timePartial
      (fun y => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR y k) q = _
    exact hcomponent k q
  have hvec :
      (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR y k) q) =
      (fun q => rieszPressurePotentialCutoffReal R hR q.1 •
        associatedPressureHelmholtzVectorPotentialTimePartial φ q) := by
    funext q k
    exact hcomponent' k q
  have hcommProd :
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i)
          (parabolicHomeomorph.symm z) =
        associatedPressureTestCurl
          (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
            (fun y => associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR y k) q)
          z i := hcomm
  rw [hvec] at hcommProd
  simpa using hcommProd

/-- In the real cutoff's inner ball, the time derivatives of the cutoff curl
and the full Helmholtz curl agree. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_eq_of_inner
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (R : ℝ) (hR : 1 ≤ R) (i : Fin 3) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 R) :
    associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) z =
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i) z := by
  let A := associatedPressureHelmholtzVectorPotentialTimePartial φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    apply contDiff_pi.2
    intro k
    exact CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hcut := associatedPressureHelmholtzCutoffCurlReal_timePartial_eq hφ R hR i z
  have hbase := associatedPressureTestCurl_timePartial
    (associatedPressureHelmholtzVectorPotential_contDiff hφ) i z
  calc
    _ = associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z i := by
          simpa [A] using hcut
    _ = associatedPressureTestCurl A z i := by
      exact congrFun (associatedPressureHelmholtzCutoffCurlReal_eq_of_inner
        A hA R hR z hx) i
    _ = _ := by
      have hbaseVec :
          (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
            (fun y => associatedPressureHelmholtzVectorPotential φ y k) q) = A := by
        funext q k
        rfl
      rw [hbaseVec] at hbase
      exact hbase.symm

private theorem hp_cutoffCurlReal_error_profile
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (D : Fin 3 → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hdirErr : ∀ (k l : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ),
      |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z -
        rieszPressureJointDirection (fun q => A q k) l z| ≤
        D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) (i : Fin 3),
      |associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z i -
        associatedPressureTestCurl A z i| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let C : ℝ := 2 * ∑ k : Fin 3, D k
  have hsum : 0 ≤ ∑ k : Fin 3, D k := Finset.sum_nonneg fun k hk => hD k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAle (k : Fin 3) : D k ≤ ∑ l : Fin 3, D l :=
    Finset.single_le_sum (fun l hl => hD l) (Finset.mem_univ k)
  refine ⟨C, hC, ?_⟩
  intro R hR z i
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => A q k) := (contDiff_apply ℝ ℝ k).comp hA
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) :=
    rieszPressurePotentialCutoffTestReal_contDiff (hAcomp k) R hR
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l z = _
    rw [← hjoint]
    rfl
  have hbasePartial (k l : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) l z =
        rieszPressureJointDirection (fun q => A q k) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    change CKN.spatialPartialProd (fun q => A q k) l z = _
    rw [← hjoint]
    rfl
  have hbase : 0 ≤ 1 + vec3EuclideanNorm z.1 := by
    have hn := vec3EuclideanNorm_nonneg z.1
    linarith only [hn]
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg hbase _
  have hpair (k l m p : Fin 3) :
      |(associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) l z -
        associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) m) p z) -
       (associatedPressureTestPartial (fun q => A q k) l z -
        associatedPressureTestPartial (fun q => A q m) p z)| ≤
        (D k + D m) * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    rw [hcutPartial, hcutPartial, hbasePartial, hbasePartial]
    calc
      _ ≤ |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z -
            rieszPressureJointDirection (fun q => A q k) l z| +
          |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTestReal (fun q => A q m) R hR) p z -
            rieszPressureJointDirection (fun q => A q m) p z| :=
        associatedPressureAbs_sub_sub_le _ _ _ _
      _ ≤ _ := by
        calc
          _ ≤ D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
              D m * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
            add_le_add (hdirErr k l R hR z) (hdirErr m p R hR z)
          _ = _ := by ring_nf
  have hcoeff (k m : Fin 3) : D k + D m ≤ C := by
    calc
      D k + D m ≤ (∑ l : Fin 3, D l) + ∑ l : Fin 3, D l :=
        add_le_add (hAle k) (hAle m)
      _ = C := by dsimp [C]; ring_nf
  have hbound (j k m p : Fin 3) :
      |(associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) k) m z -
        associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoffReal R hR q.1 • A q) p) j z) -
       (associatedPressureTestPartial (fun q => A q k) m z -
        associatedPressureTestPartial (fun q => A q p) j z)| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
    (hpair k m p j).trans
      (mul_le_mul_of_nonneg_right (hcoeff k p) hprofile)
  fin_cases i
  · change |associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 0 -
      associatedPressureTestCurl A z 0| ≤ _
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero]
    exact hbound 2 2 1 1
  · change |associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 1 -
      associatedPressureTestCurl A z 1| ≤ _
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one]
    exact hbound 0 0 2 2
  · change |associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoffReal R hR q.1 • A q) z 2 -
      associatedPressureTestCurl A z 2| ≤ _
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two]
    exact hbound 1 1 0 0

/-- The real-radius time derivative error has a uniform cubic spatial decay
profile in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_error_profile
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) (i : Fin 3),
      |associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) z -
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) w i) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let A := associatedPressureHelmholtzVectorPotentialTimePartial φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    apply contDiff_pi.2
    intro k
    exact CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  let hdecay : ∀ k : Fin 3, RieszPressurePotentialDecay (fun q => A q k) :=
    fun k => (associatedPressureHelmholtzVectorPotential_component_decay hφ k).2
  let D : Fin 3 → ℝ := fun k =>
    3 * CKN.cutoffGradientConstant * Classical.choose (hdecay k).value_bound +
      2 * Classical.choose (hdecay k).gradient_bound
  have hCG : 0 ≤ CKN.cutoffGradientConstant := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hD (k : Fin 3) : 0 ≤ D k := by
    dsimp [D]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hCG)
        (Classical.choose_spec (hdecay k).value_bound).1)
      (mul_nonneg (by norm_num)
        (Classical.choose_spec (hdecay k).gradient_bound).1)
  have hdirErr (k l : Fin 3) (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) :
      |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal (fun q => A q k) R hR) l z -
        rieszPressureJointDirection (fun q => A q k) l z| ≤
        D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    have hAcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
      (contDiff_apply ℝ ℝ k).comp hA
    have h := associatedPressurePotentialCutoffReal_direction_error_bound
      hAcomp (hdecay k) l R hR z
    simpa [D] using h
  obtain ⟨C, hC, hprofile⟩ := hp_cutoffCurlReal_error_profile A hA D hD hdirErr
  refine ⟨C, hC, ?_⟩
  intro R hR z i
  have hcut := associatedPressureHelmholtzCutoffCurlReal_timePartial_eq hφ R hR i z
  have hbase := associatedPressureTestCurl_timePartial
    (associatedPressureHelmholtzVectorPotential_contDiff hφ) i z
  have hbaseVec :
      (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
        (fun y => associatedPressureHelmholtzVectorPotential φ y k) q) = A := by
    funext q k
    rfl
  rw [hbaseVec] at hbase
  rw [hcut, hbase]
  simpa [A] using hprofile R hR z i



end CKN.Leray

end
