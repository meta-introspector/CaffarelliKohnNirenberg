-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.Support.VorticityCutoff

/-!
# Exterior cutoffs for the spatial tails

The weights of `lem:forced-tails`: an exterior cutoff ζ_R, vanishing on the
ball of radius R and equal to one outside the ball of radius 2R, times an
interior cutoff χ_N, equal to one on the ball of radius N ≥ R and
compactly supported. Both are rescalings of one fixed smooth profile, so the
first derivatives of the product are bounded by a fixed multiple of 1/R and
its second derivatives by a fixed multiple of 1/R².
-/

@[expose] public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

private theorem forcedTailsCutoff_norm_smul (c : ℝ) (x : Vec3) :
    vec3EuclideanNorm (c • x) = |c| * vec3EuclideanNorm x := by
  unfold vec3EuclideanNorm
  have h : (∑ i : Fin 3, (c • x) i ^ 2) = c ^ 2 * ∑ i : Fin 3, x i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- The spatial derivative of a rescaled and multiplied function. -/
private theorem forcedTailsCutoff_spatialDeriv_scale {h : Vec3 → ℝ}
    (hh : Differentiable ℝ h) (a c : ℝ) (i : Fin 3) (x : Vec3) :
    spatialDeriv (fun y => a * h (c • y)) i x = a * (c * spatialDeriv h i (c • x)) := by
  have h1 : HasFDerivAt (fun y : Vec3 => c • y) (c • ContinuousLinearMap.id ℝ Vec3) x :=
    (hasFDerivAt_id x).const_smul c
  have h2 : HasFDerivAt (fun y => a * h (c • y))
      (a • (fderiv ℝ h (c • x)).comp (c • ContinuousLinearMap.id ℝ Vec3)) x :=
    ((hh (c • x)).hasFDerivAt.comp x h1).const_mul a
  unfold spatialDeriv
  rw [h2.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The rescaled profile x ↦ φ(x/s): smooth, between 0 and 1, equal to
one on the ball of radius s, zero outside the ball of radius 2s, with
first derivatives at most L/s and pure second derivatives at most L/s². -/
private theorem forcedTailsCutoff_scaled {φ : Vec3 → ℝ} {L s : ℝ} (hs : 0 < s)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ1 : ∀ x, vec3EuclideanNorm x ≤ 1 → φ x = 1)
    (hφ2 : ∀ x, 2 ≤ vec3EuclideanNorm x → φ x = 0)
    (hL1 : ∀ x i, |spatialDeriv φ i x| ≤ L) (hL2 : ∀ x i, |mixedSecond φ i i x| ≤ L) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (s⁻¹ • y)) ∧
    (∀ x, vec3EuclideanNorm x ≤ s → φ (s⁻¹ • x) = 1) ∧
    (∀ x, 2 * s ≤ vec3EuclideanNorm x → φ (s⁻¹ • x) = 0) ∧
    (∀ x i, |spatialDeriv (fun y => φ (s⁻¹ • y)) i x| ≤ L / s) ∧
    (∀ x i, |mixedSecond (fun y => φ (s⁻¹ • y)) i i x| ≤ L / s ^ 2) := by
  have hsi : 0 < s⁻¹ := inv_pos.2 hs
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hnorm : ∀ x : Vec3, vec3EuclideanNorm (s⁻¹ • x) = vec3EuclideanNorm x / s := fun x => by
    rw [forcedTailsCutoff_norm_smul, abs_of_pos hsi, inv_mul_eq_div]
  have hfirst : ∀ i, spatialDeriv (fun y => φ (s⁻¹ • y)) i =
      fun x => 1 * (s⁻¹ * spatialDeriv φ i (s⁻¹ • x)) := fun i => by
    funext x
    have := forcedTailsCutoff_spatialDeriv_scale hd 1 s⁻¹ i x
    simpa only [one_mul] using this
  refine ⟨hφ.comp (contDiff_const_smul _), fun x hx => hφ1 _ ?_, fun x hx => hφ2 _ ?_,
    fun x i => ?_, fun x i => ?_⟩
  · rw [hnorm, div_le_one hs]
    exact hx
  · rw [hnorm, le_div_iff₀ hs]
    exact hx
  · rw [hfirst i]
    dsimp only
    rw [one_mul, abs_mul, abs_of_pos hsi, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hL1 _ i) hs.le
  · have hd2 : Differentiable ℝ (spatialDeriv φ i) :=
      (contDiff_spatialDeriv_smooth hφ i).differentiable (by simp)
    change |spatialDeriv (spatialDeriv (fun y => φ (s⁻¹ • y)) i) i x| ≤ L / s ^ 2
    rw [hfirst i]
    have h := forcedTailsCutoff_spatialDeriv_scale hd2 1 s⁻¹ i x
    have heq : (fun x => 1 * (s⁻¹ * spatialDeriv φ i (s⁻¹ • x))) =
        fun y => s⁻¹ * spatialDeriv φ i (s⁻¹ • y) := by
      funext y
      rw [one_mul]
    rw [heq]
    have h' := forcedTailsCutoff_spatialDeriv_scale hd2 s⁻¹ s⁻¹ i x
    rw [h', abs_mul, abs_mul, abs_of_pos hsi, ← mul_assoc, ← sq, inv_pow, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hL2 _ i) (by positivity)

private theorem forcedTailsCutoff_abs_mul_le {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- `lem:forced-tails`: the exterior cutoffs. There is a fixed L ≥ 0 such that for
every R > 0 there is a smooth ζ with values in [0,1], zero on the ball of radius
R and one outside the ball of radius 2R, and for every N ≥ R a smooth compactly
supported χ with values in [0,1], one on the ball of radius N, such that the
product ζ χ has first derivatives at most 2L/R and pure second derivatives at most
(2L + 2L²)/R². -/
theorem forcedTails_cutoff_family :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ R : ℝ, 0 < R →
      ∃ ζ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧
        (∀ x, vec3EuclideanNorm x ≤ R → ζ x = 0) ∧
        (∀ x, 2 * R ≤ vec3EuclideanNorm x → ζ x = 1) ∧
        ∀ N : ℝ, R ≤ N →
          ∃ χ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, vec3EuclideanNorm x ≤ N → χ x = 1) ∧
            (∀ x i, |spatialDeriv (fun y => ζ y * χ y) i x| ≤ 2 * L / R) ∧
            (∀ x i, |mixedSecond (fun y => ζ y * χ y) i i x| ≤
              (2 * L + 2 * L ^ 2) / R ^ 2) := by
  obtain ⟨φ, hφ, hφc, hφsupp, hφ1, hφ0, hφle⟩ :=
    CKN.vorticitySpatialCutoff_exists (r := 1) (R := 2) (by norm_num) (by norm_num)
  obtain ⟨L, hL0, hL1, hL2⟩ := CKN.vorticitySmooth_derivative_bounds hφ hφc
  have hφ2 : ∀ x, 2 ≤ vec3EuclideanNorm x → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => by
      have h' := hφsupp h
      change vec3EuclideanNorm (x - 0) < 2 at h'
      rw [sub_zero] at h'
      linarith only [h', hx]
  have hφ01 : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1 := fun x => ⟨hφ0 x, hφle x⟩
  have hL1' : ∀ x i, |spatialDeriv φ i x| ≤ L := fun x i => hL1 x i
  have hL2' : ∀ x i, |mixedSecond φ i i x| ≤ L := fun x i => hL2 x i i
  refine ⟨L, hL0, fun R hR => ?_⟩
  obtain ⟨hζs, hζ1, hζ2, hζd, hζdd⟩ := forcedTailsCutoff_scaled hR hφ hφ1 hφ2 hL1' hL2'
  let ζ : Vec3 → ℝ := fun y => 1 - φ (R⁻¹ • y)
  have hζdiff : Differentiable ℝ (fun y => φ (R⁻¹ • y)) := hζs.differentiable (by simp)
  have hζsd : ∀ i, spatialDeriv ζ i = fun x => -spatialDeriv (fun y => φ (R⁻¹ • y)) i x := by
    intro i
    funext x
    show (fderiv ℝ (fun y => 1 - φ (R⁻¹ • y)) x) (basisVec i) =
      -(fderiv ℝ (fun y => φ (R⁻¹ • y)) x) (basisVec i)
    rw [fderiv_const_sub]
    rfl
  have hζsdd : ∀ i x, mixedSecond ζ i i x = -mixedSecond (fun y => φ (R⁻¹ • y)) i i x := by
    intro i x
    show spatialDeriv (spatialDeriv ζ i) i x =
      -spatialDeriv (spatialDeriv (fun y => φ (R⁻¹ • y)) i) i x
    rw [hζsd i]
    show (fderiv ℝ (fun x => -spatialDeriv (fun y => φ (R⁻¹ • y)) i x) x) (basisVec i) =
      -(fderiv ℝ (spatialDeriv (fun y => φ (R⁻¹ • y)) i) x) (basisVec i)
    rw [fderiv_fun_neg]
    rfl
  refine ⟨ζ, contDiff_const.sub hζs, fun x => ⟨sub_nonneg.2 (hφ01 _).2,
    (sub_le_self_iff _).2 (hφ01 _).1⟩, fun x hx => by simp only [ζ, hζ1 x hx, sub_self],
    fun x hx => by simp only [ζ, hζ2 x hx, sub_zero], fun N hRN => ?_⟩
  have hN : 0 < N := hR.trans_le hRN
  obtain ⟨hχs, hχ1, hχ2, hχd, hχdd⟩ := forcedTailsCutoff_scaled hN hφ hφ1 hφ2 hL1' hL2'
  let χ : Vec3 → ℝ := fun y => φ (N⁻¹ • y)
  have hζb : ∀ x, |ζ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith only [(hφ01 (R⁻¹ • x)).2],
    by linarith only [(hφ01 (R⁻¹ • x)).1]⟩
  have hχb : ∀ x, |χ x| ≤ 1 := fun x => abs_le.2 ⟨by linarith only [(hφ01 (N⁻¹ • x)).1],
    (hφ01 _).2⟩
  have hζd' : ∀ x i, |spatialDeriv ζ i x| ≤ L / R := fun x i => by
    rw [hζsd i, abs_neg]
    exact hζd x i
  have hχd' : ∀ x i, |spatialDeriv χ i x| ≤ L / R := fun x i =>
    (hχd x i).trans (div_le_div_of_nonneg_left hL0 hR hRN)
  have hζdd' : ∀ x i, |mixedSecond ζ i i x| ≤ L / R ^ 2 := fun x i => by
    rw [hζsdd, abs_neg]
    exact hζdd x i
  have hχdd' : ∀ x i, |mixedSecond χ i i x| ≤ L / R ^ 2 := fun x i =>
    (hχdd x i).trans (div_le_div_of_nonneg_left hL0 (by positivity)
      (pow_le_pow_left₀ hR.le hRN 2))
  have hζC : ContDiff ℝ (⊤ : ℕ∞) ζ := contDiff_const.sub hζs
  refine ⟨χ, hχs, ?_, fun x => hφ01 _, hχ1, fun x i => ?_, fun x i => ?_⟩
  · exact hφc.comp_homeomorph (Homeomorph.smulOfNeZero N⁻¹ (inv_ne_zero hN.ne'))
  · rw [spatialDeriv_mul ((hζC.differentiable (by simp)) x) ((hχs.differentiable (by simp)) x)]
    have h1 := forcedTailsCutoff_abs_mul_le (hζd' x i) (hχb x)
    have h2 := forcedTailsCutoff_abs_mul_le (hζb x) (hχd' x i)
    calc _ ≤ |spatialDeriv ζ i x * χ x| + |ζ x * spatialDeriv χ i x| := abs_add_le _ _
      _ ≤ L / R * 1 + 1 * (L / R) := add_le_add h1 h2
      _ = 2 * L / R := by ring
  · rw [spatialSecondDeriv_mul_smooth hζC hχs i i x]
    have h1 := forcedTailsCutoff_abs_mul_le (hζdd' x i) (hχb x)
    have h2 := forcedTailsCutoff_abs_mul_le (hζd' x i) (hχd' x i)
    have h3 := forcedTailsCutoff_abs_mul_le (hζb x) (hχdd' x i)
    calc _ ≤ |mixedSecond ζ i i x * χ x| + |spatialDeriv ζ i x * spatialDeriv χ i x| +
          |spatialDeriv ζ i x * spatialDeriv χ i x| + |ζ x * mixedSecond χ i i x| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ L / R ^ 2 * 1 + L / R * (L / R) + L / R * (L / R) + 1 * (L / R ^ 2) := by
          gcongr
      _ = (2 * L + 2 * L ^ 2) / R ^ 2 := by
          field_simp
          ring

end CKN.Leray

end
