-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzDecayAll

/-!
# Real-radius Helmholtz cutoffs

The compact solenoidal approximations in `lem:helmholtz-test` are defined at
every real radius at least one, using the same mollified ball profile.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The CKN cutoff radius corresponding to a real inner scale `R`. -/
def rieszPressurePotentialCutoffRadiusReal (R : ℝ) (_hR : 1 ≤ R) : ℝ :=
  20 * R / 13

/-- The spatial cutoff at real scale `R`, with the profile used for the
integer-indexed compact approximations. -/
def rieszPressurePotentialCutoffReal (R : ℝ) (hR : 1 ≤ R) : Vec3 → ℝ :=
  CKN.mollifiedBallCutoff 0
    (ρ := rieszPressurePotentialCutoffRadiusReal R hR) (by
      dsimp [rieszPressurePotentialCutoffRadiusReal]
      positivity)

/-- The real-radius cutoff of a scalar space-time potential. -/
def rieszPressurePotentialCutoffTestReal
    (ψ : Vec3 × ℝ → ℝ) (R : ℝ) (hR : 1 ≤ R) : Vec3 × ℝ → ℝ :=
  fun z => rieszPressurePotentialCutoffReal R hR z.1 * ψ z

/-- The real-radius cutoff of the Helmholtz vector potential. -/
def associatedPressureHelmholtzCutoffVectorPotentialReal
    (φ : Vec3 × ℝ → Vec3) (R : ℝ) (hR : 1 ≤ R) : Vec3 × ℝ → Vec3 :=
  fun z => rieszPressurePotentialCutoffReal R hR z.1 •
    associatedPressureHelmholtzVectorPotential φ z

/-- The real cutoff radius is positive. -/
theorem rieszPressurePotentialCutoffRadiusReal_pos (R : ℝ) (hR : 1 ≤ R) :
    0 < rieszPressurePotentialCutoffRadiusReal R hR := by
  dsimp [rieszPressurePotentialCutoffRadiusReal]
  positivity

/-- The CKN cutoff equals one on the ball of radius `R`. -/
theorem rieszPressurePotentialCutoffReal_eq_one
    (R : ℝ) (hR : 1 ≤ R) {x : Vec3}
    (hx : x ∈ CKN.euclideanBall 0 R) :
    rieszPressurePotentialCutoffReal R hR x = 1 := by
  unfold rieszPressurePotentialCutoffReal
  have hin : 13 * rieszPressurePotentialCutoffRadiusReal R hR / 20 = R := by
    dsimp [rieszPressurePotentialCutoffRadiusReal]
    ring
  rw [← hin] at hx
  exact CKN.mollifiedBallCutoff_eq_one_on_inner 0
    (rieszPressurePotentialCutoffRadiusReal_pos R hR) hx

/-- The real-radius cutoff takes values in `[0,1]`. -/
theorem rieszPressurePotentialCutoffReal_bounds
    (R : ℝ) (hR : 1 ≤ R) (x : Vec3) :
    0 ≤ rieszPressurePotentialCutoffReal R hR x ∧
      rieszPressurePotentialCutoffReal R hR x ≤ 1 := by
  constructor
  · simpa [rieszPressurePotentialCutoffReal] using
      CKN.mollifiedBallCutoff_nonneg 0
        (rieszPressurePotentialCutoffRadiusReal_pos R hR) x
  · simpa [rieszPressurePotentialCutoffReal] using
      CKN.mollifiedBallCutoff_le_one 0
        (rieszPressurePotentialCutoffRadiusReal_pos R hR) x

/-- The real-radius cutoff has the inverse-scale first-derivative bound. -/
theorem rieszPressurePotentialCutoffReal_gradient_bound
    (R : ℝ) (hR : 1 ≤ R) (i : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i x| ≤
      CKN.cutoffGradientConstant / R := by
  have hcoord := CKN.abs_apply_le_vecEuclideanNorm
    (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x) i
  have hbound := CKN.mollifiedBallCutoff_gradient_bound 0
    (rieszPressurePotentialCutoffRadiusReal_pos R hR) x
  change CKN.vecEuclideanNorm
      (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x) ≤
    CKN.cutoffGradientConstant /
      rieszPressurePotentialCutoffRadiusReal R hR at hbound
  have hsp : CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i x =
      CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x i := rfl
  rw [hsp]
  calc
    |CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x i| ≤
        CKN.vecEuclideanNorm
          (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x) := hcoord
    _ ≤ CKN.cutoffGradientConstant /
        rieszPressurePotentialCutoffRadiusReal R hR := hbound
    _ = CKN.cutoffGradientConstant * (13 / 20) / R := by
      dsimp [rieszPressurePotentialCutoffRadiusReal]
      have hR0 : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hR)
      field_simp [hR0]
    _ ≤ CKN.cutoffGradientConstant / R := by
      have hC : 0 ≤ CKN.cutoffGradientConstant := by
        have h := CKN.mollifiedBallCutoff_gradient_bound 0
          (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
        exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
      have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
      apply (div_le_div_iff_of_pos_right hRpos).2
      calc
        CKN.cutoffGradientConstant * (13 / 20) ≤
            CKN.cutoffGradientConstant * 1 := by gcongr; norm_num
        _ = CKN.cutoffGradientConstant := by ring

/-- Every real-radius cutoff Hessian component has an inverse-square bound. -/
theorem rieszPressurePotentialCutoffReal_hessian_component_bound
    (R : ℝ) (hR : 1 ≤ R) (i j : Fin 3) (x : Vec3) :
    |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x| ≤
      CKN.cutoffSecondDerivativeConstant / R ^ 2 := by
  have hbound := CKN.mollifiedBallCutoff_second_derivative_bound 0
    (rieszPressurePotentialCutoffRadiusReal_pos R hR) x
  change ‖fderiv ℝ
      (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ ≤
    CKN.cutoffSecondDerivativeConstant /
      (rieszPressurePotentialCutoffRadiusReal R hR) ^ 2 at hbound
  have hcoord : |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x| ≤
      ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ := by
    have hcomp : CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x =
        (fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x
          (CKN.basisVec i)) j := by
      have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffReal R hR) :=
        CKN.mollifiedBallCutoff_smooth 0
          (rieszPressurePotentialCutoffRadiusReal_pos R hR)
      have hgrad : ContDiff ℝ (⊤ : ℕ∞)
          (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) := by
        rw [contDiff_pi]
        intro k
        change ContDiff ℝ (⊤ : ℕ∞)
          (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) k)
        exact CKN.contDiff_spatialDeriv_smooth hη k
      change CKN.spatialDeriv
        (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j) i x = _
      change (fderiv ℝ (fun y : Vec3 =>
        CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) y j) x)
        (CKN.basisVec i) = _
      rw [fderiv_apply (hgrad.differentiable (by norm_num) x) j]
      rfl
    rw [hcomp]
    calc
      |(fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x
          (CKN.basisVec i)) j| ≤
        ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x
          (CKN.basisVec i)‖ := by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm _ j
      _ ≤ ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ := by
        calc
          _ ≤ ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ *
                ‖CKN.basisVec i‖ := ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ := by
            rw [CKN.basisVec, Pi.norm_single]
            norm_num
  calc
    |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x| ≤
        ‖fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x‖ := hcoord
    _ ≤ CKN.cutoffSecondDerivativeConstant /
        (rieszPressurePotentialCutoffRadiusReal R hR) ^ 2 := hbound
    _ = CKN.cutoffSecondDerivativeConstant * (13 / 20) ^ 2 / R ^ 2 := by
      dsimp [rieszPressurePotentialCutoffRadiusReal]
      ring
    _ ≤ CKN.cutoffSecondDerivativeConstant / R ^ 2 := by
      have hC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
        have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
          (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
        exact le_trans (norm_nonneg _) (by simpa using h)
      have hR2 : 0 < R ^ 2 := by positivity
      apply (div_le_div_iff_of_pos_right hR2).2
      calc
        CKN.cutoffSecondDerivativeConstant * (13 / 20) ^ 2 ≤
            CKN.cutoffSecondDerivativeConstant * 1 := by gcongr; norm_num
        _ = CKN.cutoffSecondDerivativeConstant := by ring

/-- The cutoff derivatives vanish on the closed inner ball of radius `R`. -/
theorem rieszPressurePotentialCutoffReal_derivatives_zero_on_inner
    (R : ℝ) (hR : 1 ≤ R) {x : Vec3}
    (hx : x ∈ CKN.euclideanClosedBall 0 R) :
    CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x = 0 ∧
      fderiv ℝ (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x = 0 := by
  have hinner : 13 * rieszPressurePotentialCutoffRadiusReal R hR / 20 = R := by
    dsimp [rieszPressurePotentialCutoffRadiusReal]
    ring
  have hnotAnnulus : x ∉ CKN.euclideanBall 0
      (3 * rieszPressurePotentialCutoffRadiusReal R hR / 4) \
        CKN.euclideanClosedBall 0
          (13 * rieszPressurePotentialCutoffRadiusReal R hR / 20) := by
    intro hxAnn
    apply hxAnn.2
    rw [hinner]
    exact hx
  exact CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
    (rieszPressurePotentialCutoffRadiusReal_pos R hR) hnotAnnulus

/-- A real-radius scalar cutoff is smooth. -/
theorem rieszPressurePotentialCutoffTestReal_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffTestReal ψ R hR) := by
  have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffReal R hR) :=
    CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadiusReal_pos R hR)
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun z : Vec3 × ℝ => rieszPressurePotentialCutoffReal R hR z.1 * ψ z)
  exact (hη.comp contDiff_fst).mul hψ

/-- The support radius of the real cutoff is a fixed multiple of its inner
scale. -/
theorem rieszPressurePotentialCutoffReal_outer (R : ℝ) (hR : 1 ≤ R) :
    3 * rieszPressurePotentialCutoffRadiusReal R hR / 4 =
      (15 / 13 : ℝ) * R := by
  dsimp [rieszPressurePotentialCutoffRadiusReal]
  ring

/-- The real cutoff gradient has a spatially decaying profile on its support
annulus. -/
theorem rieszPressurePotentialCutoffReal_gradient_profile_bound
    (R : ℝ) (hR : 1 ≤ R) (i : Fin 3) (x : Vec3) :
    |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i x| ≤
      3 * CKN.cutoffGradientConstant / (1 + ‖x‖) := by
  let ρ := rieszPressurePotentialCutoffRadiusReal R hR
  by_cases hx : x ∈ CKN.euclideanBall 0 (3 * ρ / 4) \
      CKN.euclideanClosedBall 0 (13 * ρ / 20)
  · have hbase := rieszPressurePotentialCutoffReal_gradient_bound R hR i x
    have hnorm0 := norm_le_vec3EuclideanNorm x
    have houter := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by dsimp [ρ, rieszPressurePotentialCutoffRadiusReal]; positivity)).1 hx.1
    have houter' : vec3EuclideanNorm x < (15 / 13 : ℝ) * R := by
      dsimp [ρ] at houter
      rw [rieszPressurePotentialCutoffReal_outer R hR] at houter
      simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
        CKN.vecDot, pow_two] using houter
    have hrel : 1 + ‖x‖ ≤ 3 * R := by
      nlinarith only [houter', hR, hnorm0]
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hden : 0 < 1 + ‖x‖ := by positivity
    have hrec : 1 / R ≤ 3 / (1 + ‖x‖) := by
      rw [div_le_div_iff₀ hRpos hden]
      nlinarith only [hrel]
    have hC : 0 ≤ CKN.cutoffGradientConstant := by
      have h := CKN.mollifiedBallCutoff_gradient_bound 0
        (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
      exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
    calc
      |CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i x| ≤
          CKN.cutoffGradientConstant / R := hbase
      _ = CKN.cutoffGradientConstant * (1 / R) := by ring
      _ ≤ CKN.cutoffGradientConstant * (3 / (1 + ‖x‖)) :=
        mul_le_mul_of_nonneg_left hrec hC
      _ = 3 * CKN.cutoffGradientConstant / (1 + ‖x‖) := by ring
  · have hzero := CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR) hx
    have hgrad : CKN.classicalGradient
        (rieszPressurePotentialCutoffReal R hR) x = 0 := by
      simpa [rieszPressurePotentialCutoffReal] using hzero.1
    have hsp : CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) i x = 0 := by
      change CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) x i = 0
      exact congrFun hgrad i
    rw [hsp, abs_zero]
    have hC : 0 ≤ CKN.cutoffGradientConstant := by
      have h := CKN.mollifiedBallCutoff_gradient_bound 0
        (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
      exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
    exact div_nonneg (mul_nonneg (by norm_num) hC) (by positivity)

/-- The real cutoff Hessian has a spatially decaying profile on its support
annulus. -/
theorem rieszPressurePotentialCutoffReal_hessian_profile_bound
    (R : ℝ) (hR : 1 ≤ R) (i j : Fin 3) (x : Vec3) :
    |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x| ≤
      9 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by
  let ρ := rieszPressurePotentialCutoffRadiusReal R hR
  by_cases hx : x ∈ CKN.euclideanBall 0 (3 * ρ / 4) \
      CKN.euclideanClosedBall 0 (13 * ρ / 20)
  · have hbase := rieszPressurePotentialCutoffReal_hessian_component_bound R hR i j x
    have hnorm0 := norm_le_vec3EuclideanNorm x
    have houter := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by dsimp [ρ, rieszPressurePotentialCutoffRadiusReal]; positivity)).1 hx.1
    have houter' : vec3EuclideanNorm x < (15 / 13 : ℝ) * R := by
      dsimp [ρ] at houter
      rw [rieszPressurePotentialCutoffReal_outer R hR] at houter
      simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
        CKN.vecDot, pow_two] using houter
    have hrel : 1 + ‖x‖ ≤ 3 * R := by
      nlinarith only [houter', hR, hnorm0]
    have hC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
      have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
        (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
      exact le_trans (norm_nonneg _) (by simpa using h)
    have hR2 : 0 < R ^ 2 := by positivity
    have hden2 : 0 < (1 + ‖x‖) ^ 2 := by positivity
    have hrec : (1 / R ^ 2) ≤ 9 / (1 + ‖x‖) ^ 2 := by
      rw [div_le_div_iff₀ hR2 hden2]
      have hsq : (1 + ‖x‖) ^ 2 ≤ (3 * R) ^ 2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).2 hrel
      nlinarith only [hsq]
    calc
      |CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x| ≤
          CKN.cutoffSecondDerivativeConstant / R ^ 2 := hbase
      _ = CKN.cutoffSecondDerivativeConstant * (1 / R ^ 2) := by ring
      _ ≤ CKN.cutoffSecondDerivativeConstant * (9 / (1 + ‖x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hrec hC
      _ = 9 * CKN.cutoffSecondDerivativeConstant / (1 + ‖x‖) ^ 2 := by ring
  · have hzero := CKN.mollifiedBallCutoff_derivatives_vanish_outside_annulus 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR) hx
    have hhess : fderiv ℝ
        (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) x = 0 := by
      simpa [rieszPressurePotentialCutoffReal] using hzero.2
    have hcomp : CKN.mixedSecond (rieszPressurePotentialCutoffReal R hR) i j x = 0 := by
      have hη : ContDiff ℝ (⊤ : ℕ∞) (rieszPressurePotentialCutoffReal R hR) :=
        CKN.mollifiedBallCutoff_smooth 0
          (rieszPressurePotentialCutoffRadiusReal_pos R hR)
      have hgrad : ContDiff ℝ (⊤ : ℕ∞)
          (CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR)) := by
        rw [contDiff_pi]
        intro k
        change ContDiff ℝ (⊤ : ℕ∞)
          (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) k)
        exact CKN.contDiff_spatialDeriv_smooth hη k
      change CKN.spatialDeriv
        (CKN.spatialDeriv (rieszPressurePotentialCutoffReal R hR) j) i x = 0
      change (fderiv ℝ (fun y : Vec3 =>
        CKN.classicalGradient (rieszPressurePotentialCutoffReal R hR) y j) x)
        (CKN.basisVec i) = 0
      rw [fderiv_apply (hgrad.differentiable (by norm_num) x) j, hhess]
      rfl
    rw [hcomp, abs_zero]
    have hC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
      have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
        (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
      exact le_trans (norm_nonneg _) (by simpa using h)
    exact div_nonneg (mul_nonneg (by norm_num) hC) (by positivity)

/-- A first derivative of a real-radius cutoff potential differs from the
uncut derivative by a cubic spatial decay profile. -/
theorem associatedPressurePotentialCutoffReal_direction_error_bound
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hdecay : RieszPressurePotentialDecay ψ) (i : Fin 3)
    (R : ℝ) (hR : 1 ≤ R) (z : Vec3 × ℝ) :
    |rieszPressureJointDirection
        (rieszPressurePotentialCutoffTestReal ψ R hR) i z -
      rieszPressureJointDirection ψ i z| ≤
      (3 * CKN.cutoffGradientConstant * Classical.choose hdecay.value_bound +
        2 * Classical.choose hdecay.gradient_bound) *
        (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let η := rieszPressurePotentialCutoffReal R hR
  let C0 := Classical.choose hdecay.value_bound
  let C1 := Classical.choose hdecay.gradient_bound
  let CG := CKN.cutoffGradientConstant
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hC0 : 0 ≤ C0 := (Classical.choose_spec hdecay.value_bound).1
  have hC1 : 0 ≤ C1 := (Classical.choose_spec hdecay.gradient_bound).1
  have hCG : 0 ≤ CG := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hv := (Classical.choose_spec hdecay.value_bound).2 z
  have hgrad := (Classical.choose_spec hdecay.gradient_bound).2 i z
  have hηbound := rieszPressurePotentialCutoffReal_bounds R hR z.1
  have hηgrad := rieszPressurePotentialCutoffReal_gradient_bound R hR i z.1
  have houterRadius : 3 * rieszPressurePotentialCutoffRadiusReal R hR / 4 =
      (15 / 13 : ℝ) * R := rieszPressurePotentialCutoffReal_outer R hR
  have hformula :
      rieszPressureJointDirection
          (rieszPressurePotentialCutoffTestReal ψ R hR) i z =
        CKN.spatialDeriv η i z.1 * ψ z +
          η z.1 * rieszPressureJointDirection ψ i z := by
    rw [← rieszPressure_sliceSpatialDeriv_eq_joint
        (rieszPressurePotentialCutoffTestReal_contDiff hψ R hR) i z,
      ← rieszPressure_sliceSpatialDeriv_eq_joint hψ i z]
    have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
      CKN.mollifiedBallCutoff_smooth 0 (rieszPressurePotentialCutoffRadiusReal_pos R hR)
    have hψslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => ψ (x, z.2)) :=
      hψ.comp (contDiff_id.prodMk contDiff_const)
    have hprod := CKN.spatialDeriv_mul
      ((hη.differentiable (by simp)) z.1)
      ((hψslice.differentiable (by simp)) z.1) i
    simpa [rieszPressurePotentialCutoffTestReal] using hprod
  by_cases hinner : z.1 ∈ CKN.euclideanBall 0 R
  · have hclosed : z.1 ∈ CKN.euclideanClosedBall 0 R := by
      apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (le_trans (by norm_num) hR)).2
      exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 hinner |>.le
    have hηone := rieszPressurePotentialCutoffReal_eq_one R hR hinner
    have hderivzero := rieszPressurePotentialCutoffReal_derivatives_zero_on_inner R hR hclosed
    have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
      change CKN.classicalGradient η z.1 i = 0
      rw [hderivzero.1]
      simp
    have hηone' : η z.1 = 1 := by simpa [η] using hηone
    rw [hformula, hηgradzero, hηone']
    have hcoeff : 0 ≤ 3 * CG * C0 + 2 * C1 := by positivity
    have hn := vec3EuclideanNorm_nonneg z.1
    have hbase : 0 ≤ 1 + vec3EuclideanNorm z.1 := by linarith only [hn]
    have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
      Real.rpow_nonneg hbase _
    have hz : 0 * ψ z + 1 * rieszPressureJointDirection ψ i z -
        rieszPressureJointDirection ψ i z = 0 := by ring
    rw [hz, abs_zero]
    change 0 ≤ (3 * CG * C0 + 2 * C1) *
      (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))
    exact mul_nonneg hcoeff hprof
  · have hvnorm : 0 < 1 + vec3EuclideanNorm z.1 := by
      have hn := vec3EuclideanNorm_nonneg z.1
      linarith only [hn]
    by_cases hout : z.1 ∈ CKN.euclideanBall 0
        (3 * rieszPressurePotentialCutoffRadiusReal R hR / 4)
    · have houtnorm : vec3EuclideanNorm z.1 < (15 / 13 : ℝ) * R := by
        rw [← houterRadius]
        have houterpos : 0 < 3 * rieszPressurePotentialCutoffRadiusReal R hR / 4 := by
          rw [houterRadius]
          positivity
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using
          (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt houterpos).1 hout
      have hrel : 1 + vec3EuclideanNorm z.1 ≤ 3 * R := by
        nlinarith only [houtnorm, hR]
      have hrelInv : 1 / R ≤ 3 / (1 + vec3EuclideanNorm z.1) := by
        rw [div_le_div_iff₀ hRpos hvnorm]
        nlinarith only [hrel]
      rw [hformula]
      change |CKN.spatialDeriv η i z.1 * ψ z +
          η z.1 * rieszPressureJointDirection ψ i z -
            rieszPressureJointDirection ψ i z| ≤
        (3 * CG * C0 + 2 * C1) *
          (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))
      have hfirst :
          |CKN.spatialDeriv η i z.1 * ψ z| ≤
            3 * CG * C0 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
        rw [abs_mul]
        have hvalue' : |ψ z| ≤ C0 *
            (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ)) := hv
        have hgrad' : |CKN.spatialDeriv η i z.1| ≤ CG / R := hηgrad
        have hprod : |CKN.spatialDeriv η i z.1| * |ψ z| ≤
            (CG / R) * (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) :=
          mul_le_mul hgrad' hvalue' (abs_nonneg _) (by positivity)
        have hpow : (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ)) *
              (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) =
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          rw [← Real.rpow_add hvnorm]
          congr 1
          ring
        have hpowInv : (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) =
            1 / (1 + vec3EuclideanNorm z.1) := by
          rw [Real.rpow_neg hvnorm.le, Real.rpow_one]
          simp [div_eq_mul_inv]
        have hfactor : CG / R ≤ CG * 3 *
            (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) := by
          have hinv : 1 / R ≤ 3 *
              (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ)) := by
            simpa [hpowInv, div_eq_mul_inv] using hrelInv
          calc
            CG / R = CG * (1 / R) := by ring
            _ ≤ CG * (3 * (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hinv hCG
            _ = _ := by ring
        calc
          _ ≤ (CG / R) *
              (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) := hprod
          _ ≤ (CG * 3 * (1 + vec3EuclideanNorm z.1) ^ (-(1 : ℝ))) *
              (C0 * (1 + vec3EuclideanNorm z.1) ^ (-(2 : ℝ))) :=
                mul_le_mul_of_nonneg_right hfactor (by positivity)
          _ = 3 * CG * C0 *
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
                rw [← hpow]
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
        _ ≤ 3 * CG * C0 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
            C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          have hgrad' : |rieszPressureJointDirection ψ i z| ≤
              C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
            simpa [C1] using hgrad
          calc
            _ ≤ 3 * CG * C0 *
                  (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
                1 * |rieszPressureJointDirection ψ i z| :=
              add_le_add hfirst
                (mul_le_mul_of_nonneg_right hetaMinus (abs_nonneg _))
            _ ≤ _ := by
              calc
                _ = |rieszPressureJointDirection ψ i z| +
                    3 * CG * C0 *
                      (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by ring
                _ ≤ C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
                    3 * CG * C0 *
                      (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
                    add_le_add_left hgrad' _
                _ = _ := by ring
        _ ≤ (3 * CG * C0 + 2 * C1) *
              (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
          have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
            Real.rpow_nonneg (by positivity) _
          have hcoeff : 3 * CG * C0 + C1 ≤ 3 * CG * C0 + 2 * C1 := by
            have hCGC0 : 0 ≤ 3 * CG * C0 := by positivity
            nlinarith only [hC1, hCGC0]
          calc
            _ = (3 * CG * C0 + C1) *
                (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hprof
    · have houterNotSupport : z.1 ∉ tsupport η := by
        intro hz
        have hsub := CKN.mollifiedBallCutoff_tsupport_subset_outer 0
          (rieszPressurePotentialCutoffRadiusReal_pos R hR) hz
        exact hout (by simpa [η] using hsub)
      have hηzero : η z.1 = 0 := image_eq_zero_of_notMem_tsupport houterNotSupport
      have hηgradzero : CKN.spatialDeriv η i z.1 = 0 := by
        rw [CKN.spatialDeriv]
        have hfd : fderiv ℝ η z.1 = 0 :=
          fderiv_of_notMem_tsupport ℝ houterNotSupport
        rw [hfd]
        simp
      rw [hformula, hηgradzero]
      simp only [η, hηzero, zero_mul, zero_add]
      have hprof : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have hC : 0 ≤ 3 * CG * C0 + 2 * C1 := by positivity
      have hgrad' : |rieszPressureJointDirection ψ i z| ≤
          C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
        simpa [C1] using hgrad
      have hcoeff : C1 ≤ 3 * CG * C0 + 2 * C1 := by
        have hCGC0 : 0 ≤ 3 * CG * C0 := by positivity
        nlinarith only [hC1, hCGC0]
      change |(0 : ℝ) - rieszPressureJointDirection ψ i z| ≤
        (3 * CG * C0 + 2 * C1) *
          (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))
      rw [show (0 : ℝ) - rieszPressureJointDirection ψ i z =
        -rieszPressureJointDirection ψ i z by ring, abs_neg]
      calc
        _ = |rieszPressureJointDirection ψ i z| := rfl
        _ ≤ C1 * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := hgrad'
        _ ≤ (3 * CG * C0 + 2 * C1) *
            (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff hprof

/-- The real-radius vector-potential cutoff is a compact space-time test on
the original time interval. -/
theorem associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (R : ℝ) (hR : 1 ≤ R) :
    associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  let K : Set ℝ := (tsupport φ).image Prod.snd
  let r : ℝ := 3 * rieszPressurePotentialCutoffRadiusReal R hR / 4
  let B : Set Vec3 := CKN.euclideanClosedBall 0 r
  let S : Set (Vec3 × ℝ) := B ×ˢ K
  have hK : IsCompact K := hφ.2.1.isCompact.image continuous_snd
  have hKsubset : K ⊆ Ioo 0 T := by
    rintro t ⟨z, hz, rfl⟩
    exact hφ.2.2 hz |>.2
  have hr : 0 < r := by
    dsimp [r, rieszPressurePotentialCutoffRadiusReal]
    positivity
  have hB : IsCompact B := by
    dsimp [B]
    exact CKN.isCompact_euclideanClosedBall 0 hr.le
  have hS : IsCompact S := hB.prod hK
  have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => rieszPressurePotentialCutoffReal R hR z.1) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadiusReal_pos R hR)).comp contDiff_fst
  have hpotentialSmooth := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) := by
    apply contDiff_pi.2
    intro j
    exact hcutSmooth.mul
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).contDiff.comp hpotentialSmooth)
  have hKzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0 := by
    intro t ht x
    exact (associatedPressureHelmholtzPotentials_zero_off_time_support
      (by simpa [K] using ht) x).2
  have hpointzero : ∀ z, z ∉ S →
      associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR z = 0 := by
    intro z hz
    by_cases ht : z.2 ∈ K
    · have hx : z.1 ∉ B := by
        intro hx
        exact hz ⟨hx, ht⟩
      have houter : z.1 ∉
          CKN.euclideanBall 0
            (3 * rieszPressurePotentialCutoffRadiusReal R hR / 4) := by
        intro hy
        apply hx
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
        have hy' := (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
        simpa [B, r] using hy'.le
      have hnot : z.1 ∉ tsupport (rieszPressurePotentialCutoffReal R hR) := by
        intro hy
        have hy' := CKN.mollifiedBallCutoff_tsupport_subset_outer 0
          (rieszPressurePotentialCutoffRadiusReal_pos R hR) hy
        exact houter (by simpa [r] using hy')
      have hcut : rieszPressurePotentialCutoffReal R hR z.1 = 0 :=
        image_eq_zero_of_notMem_tsupport hnot
      simp [associatedPressureHelmholtzCutoffVectorPotentialReal, hcut]
    · simp [associatedPressureHelmholtzCutoffVectorPotentialReal,
        hKzero z.2 ht z.1]
  have hcompact : HasCompactSupport
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) :=
    HasCompactSupport.intro hS hpointzero
  have htsub : tsupport
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) ⊆ S := by
    change closure (Function.support
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR)) ⊆ S
    apply closure_minimal
    · intro z hz
      by_contra hnot
      exact hz (hpointzero z hnot)
    · exact hS.isClosed
  refine ⟨hcont, hcompact, ?_⟩
  have hsub : S ⊆ spaceTimeSet Set.univ (Ioo 0 T) := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    exact ⟨Set.mem_univ _, hKsubset ht⟩
  exact htsub.trans hsub

/-- The real-radius cutoff curl is a compact solenoidal test. -/
theorem associatedPressureHelmholtzCutoffCurlReal_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (R : ℝ) (hR : 1 ≤ R) :
    associatedPressureTestCurl
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) ∈
        CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) :=
  associatedPressureTestCurl_mem_spaceTimeTestFunction
    (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
      hφ R hR)

/-- A total real-parameter extension of the cutoff vector potential, used to
state limits over `ℝ`; it agrees with the scale-`R` family for `R ≥ 1`. -/
def associatedPressureHelmholtzCutoffVectorPotentialRealTotal
    (φ : Vec3 × ℝ → Vec3) (R : ℝ) : Vec3 × ℝ → Vec3 :=
  associatedPressureHelmholtzCutoffVectorPotentialReal φ (max R 1)
    (le_max_right R 1)

/-- The total real-parameter extension agrees with the specified cutoff when
the radius is at least one. -/
theorem associatedPressureHelmholtzCutoffVectorPotentialRealTotal_eq
    (φ : Vec3 × ℝ → Vec3) (R : ℝ) (hR : 1 ≤ R) :
    associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R =
      associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR := by
  have hcut : rieszPressurePotentialCutoffReal (max R 1) (le_max_right R 1) =
      rieszPressurePotentialCutoffReal R hR := by
    let rmax : {ρ : ℝ // 0 < ρ} :=
      ⟨rieszPressurePotentialCutoffRadiusReal (max R 1) (le_max_right R 1),
        rieszPressurePotentialCutoffRadiusReal_pos (max R 1) (le_max_right R 1)⟩
    let rR : {ρ : ℝ // 0 < ρ} :=
      ⟨rieszPressurePotentialCutoffRadiusReal R hR,
        rieszPressurePotentialCutoffRadiusReal_pos R hR⟩
    have hr : rmax = rR := by
      apply Subtype.ext
      dsimp [rmax, rR, rieszPressurePotentialCutoffRadiusReal]
      rw [max_eq_left hR]
    unfold rieszPressurePotentialCutoffReal
    change CKN.mollifiedBallCutoff 0 rmax.2 = CKN.mollifiedBallCutoff 0 rR.2
    exact congrArg (fun r : {ρ : ℝ // 0 < ρ} => CKN.mollifiedBallCutoff 0 r.2) hr
  funext z
  simp [associatedPressureHelmholtzCutoffVectorPotentialRealTotal,
    associatedPressureHelmholtzCutoffVectorPotentialReal, hcut]

end CKN.Leray

end
