-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Parabolic.Vec3Norm
public import CKN.Foundation.Sobolev.Poincare.Smooth
public import CKN.Foundation.Sobolev.Cutoff.Basic
public import CKN.Foundation.Sobolev.H1.Basic
public import CKN.Foundation.Sobolev.Mollify.LpApproximation
public import CKN.Foundation.Sobolev.Mollify.Transport
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Local Sobolev translation estimates

Translation in a relatively compact region is controlled by the chosen weak
spatial gradient, as used in `lem:compactness`.
-/

@[expose] public section

open MeasureTheory Set
open Filter
open CKN.Foundation.Parabolic
open scoped ENNReal
set_option autoImplicit false

noncomputable section

namespace CKN.Foundation.Sobolev

private theorem clm_eq_dot (L : Vec3 →L[ℝ] ℝ) (h : Vec3) :
    L h = ∑ i : Fin 3, h i * L (CKN.basisVec i) := by
  calc
    L h = L (∑ i : Fin 3, h i • CKN.basisVec i) := by rw [CKN.sum_smul_basisVec]
    _ = ∑ i : Fin 3, L (h i • CKN.basisVec i) := map_sum L _ _
    _ = ∑ i : Fin 3, h i * L (CKN.basisVec i) := by simp only [map_smul, smul_eq_mul]

private theorem dot_bound (h g : Vec3) :
    |∑ i : Fin 3, h i * g i| ≤ vec3EuclideanNorm h * vec3EuclideanNorm g := by
  have hsum : (∑ i : Fin 3, h i * g i) =
      inner ℝ (WithLp.toLp 2 h) (WithLp.toLp 2 g) := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  rw [hsum, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2]
  exact abs_real_inner_le_norm _ _

private theorem clm_apply_le (L : Vec3 →L[ℝ] ℝ) (h : Vec3)
    (g : Vec3) (hg : ∀ i, L (CKN.basisVec i) = g i) :
    |L h| ≤ vec3EuclideanNorm h * vec3EuclideanNorm g := by
  rw [clm_eq_dot]
  simpa only [hg] using dot_bound h g

private theorem ftcLine (f : Vec3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x h : Vec3) :
    f (x + h) - f x = ∫ t in (0:ℝ)..1, (fderiv ℝ f (x + t • h)) h := by
  let γ : ℝ → ℝ := f ∘ (fun t : ℝ => x + t • h)
  have hγderiv (t : ℝ) : HasDerivAt γ ((fderiv ℝ f (x + t • h)) h) t := by
    have hpath : HasDerivAt (fun z : ℝ => x + z • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hf' : HasFDerivAt f (fderiv ℝ f (x + t • h)) (x + t • h) :=
      (hf.differentiable (by simp) (x + t • h)).hasFDerivAt
    have hc := hf'.comp t hpath
    simpa [γ, ContinuousLinearMap.comp_apply] using hc.hasDerivAt
  have hcont : ContinuousOn (fun t : ℝ => (fderiv ℝ f (x + t • h)) h) (Set.uIcc 0 1) := by
    have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn.clm_apply continuous_const.continuousOn
  have hderiv : deriv γ = fun t : ℝ => (fderiv ℝ f (x + t • h)) h := by
    funext t
    exact (hγderiv t).deriv
  have heq := intervalIntegral.integral_deriv_eq_sub' γ hderiv
    (fun t _ => (hγderiv t).differentiableAt) hcont
  simpa [γ] using heq.symm

private theorem continuousOn_Icc_memLp_two {g : ℝ → ℝ} (hg : Continuous g) :
    MemLp g (2 : ℝ≥0∞) (volume.restrict (Icc (0 : ℝ) 1)) := by
  let S : Set ℝ := Set.range (fun t : Icc (0 : ℝ) 1 => g t)
  have hS : Bornology.IsBounded S :=
    (isCompact_range (hg.comp continuous_subtype_val)).isBounded
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  have hbound : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), ‖g t‖ ≤ C := by
    filter_upwards [ae_restrict_mem (isCompact_Icc.measurableSet)] with t ht
    exact hC (g t) ⟨⟨t, ht⟩, rfl⟩
  exact MemLp.of_bound hg.measurable.aestronglyMeasurable C hbound

private theorem intervalIntegral_sq_le_integral_sq {g : ℝ → ℝ} (hg : Continuous g)
    (hgnn : ∀ t, 0 ≤ g t) :
    (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hmem : MemLp g (2 : ℝ≥0∞) μ := continuousOn_Icc_memLp_two hg
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (2 : ℝ≥0∞) μ := memLp_const 1
  have hmem' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hmem
  have hone' : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hone
  have hnonneg : 0 ≤ᵐ[μ] g := Eventually.of_forall hgnn
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg h22 hnonneg
    (Eventually.of_forall (fun _ => (by norm_num : (0 : ℝ) ≤ 1))) hmem' hone'
  have hpow : ∫ t, g t ^ (2 : ℝ) ∂μ = ∫ t, g t ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with t
    exact Real.rpow_natCast (g t) 2
  have hconst' : ∫ t, (1 : ℝ) ^ (2 : ℝ) ∂μ = 1 := by
    simp [μ]
  have hIcc : ∫ t in Icc (0 : ℝ) 1, g t = ∫ t in (0 : ℝ)..1, g t := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hIccSq : ∫ t in Icc (0 : ℝ) 1, g t ^ 2 = ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have hconst : ∫ t, (1 : ℝ) ^ 2 ∂μ = 1 := by simp [μ]
  have hholderReal : ∫ t, g t ∂μ ≤ Real.sqrt (∫ t, g t ^ 2 ∂μ) := by
    calc
      ∫ t, g t ∂μ ≤
          (∫ t, g t ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
              simpa only [mul_one] using hholder
      _ = Real.sqrt (∫ t, g t ^ 2 ∂μ) := by
        rw [hpow, hconst']
        rw [Real.sqrt_eq_rpow]
        norm_num
  have hL : ∫ t in (0 : ℝ)..1, g t = ∫ t, g t ∂μ := by
    simpa [μ] using hIcc.symm
  have hR : ∫ t, g t ^ 2 ∂μ = ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    simpa [μ] using hIccSq
  have hholder' : ∫ t in (0 : ℝ)..1, g t ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, g t ^ 2) := by
    calc
      ∫ t in (0 : ℝ)..1, g t = ∫ t, g t ∂μ := hL
      _ ≤ Real.sqrt (∫ t, g t ^ 2 ∂μ) := hholderReal
      _ = Real.sqrt (∫ t in (0 : ℝ)..1, g t ^ 2) := by rw [hR]
  have hI_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_nonneg fun t => sq_nonneg (g t)
  have hg_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, g t := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    exact integral_nonneg fun t => hgnn t
  have hsqrt : Real.sqrt (∫ t in (0 : ℝ)..1, g t ^ 2) ^ 2 =
      ∫ t in (0 : ℝ)..1, g t ^ 2 := Real.sq_sqrt hI_nonneg
  nlinarith only [hholder', hI_nonneg, hg_nonneg, hsqrt]

private theorem smoothScalarSegmentSq {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (x h : Vec3) :
    |f (x + h) - f x| ^ 2 ≤ vec3EuclideanNorm h ^ 2 *
      ∫ t in (0 : ℝ)..1, vec3EuclideanNorm (CKN.classicalGradient f (x + t • h)) ^ 2 := by
  let g : ℝ → ℝ := fun t => vec3EuclideanNorm (CKN.classicalGradient f (x + t • h))
  have hgcont : Continuous g := by
    apply continuous_vec3EuclideanNorm.comp
    have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x + t • h)) :=
      hfd.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hgrad : Continuous (fun t : ℝ => CKN.classicalGradient f (x + t • h)) := by
      apply continuous_pi
      intro i
      simpa only [CKN.classicalGradient_apply] using hc.clm_apply continuous_const
    exact hgrad
  have hgnn : ∀ t, 0 ≤ g t := fun t => vec3EuclideanNorm_nonneg _
  have hftc := ftcLine f hf x h
  have hdir (t : ℝ) :
      |(fderiv ℝ f (x + t • h)) h| ≤ vec3EuclideanNorm h * g t := by
    apply clm_apply_le _ h (CKN.classicalGradient f (x + t • h))
    intro i
    simp [CKN.classicalGradient_apply]
  have hnorm : IntervalIntegrable (fun t : ℝ => |(fderiv ℝ f (x + t • h)) h|)
      volume 0 1 := by
    have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    exact (continuous_abs.comp
      ((hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const)).intervalIntegrable _ _
  have hgint : IntervalIntegrable (fun t : ℝ => vec3EuclideanNorm h * g t)
      volume 0 1 := (continuous_const.mul hgcont).intervalIntegrable _ _
  have hbound : |f (x + h) - f x| ≤ vec3EuclideanNorm h * ∫ t in (0:ℝ)..1, g t := by
    rw [hftc]
    calc
      |∫ t in (0:ℝ)..1, (fderiv ℝ f (x + t • h)) h| ≤
          ∫ t in (0:ℝ)..1, |(fderiv ℝ f (x + t • h)) h| := by
            simpa only [Real.norm_eq_abs] using
              (intervalIntegral.norm_integral_le_integral_norm
                (f := fun t : ℝ => (fderiv ℝ f (x + t • h)) h) zero_le_one)
      _ ≤ ∫ t in (0:ℝ)..1, vec3EuclideanNorm h * g t := by
            refine intervalIntegral.integral_mono_on zero_le_one hnorm hgint ?_
            intro t ht
            simpa only [Real.norm_eq_abs] using hdir t
      _ = vec3EuclideanNorm h * ∫ t in (0:ℝ)..1, g t := by
            rw [intervalIntegral.integral_const_mul]
  have hcauchy := intervalIntegral_sq_le_integral_sq hgcont hgnn
  have hbase : 0 ≤ vec3EuclideanNorm h * ∫ t in (0:ℝ)..1, g t :=
    mul_nonneg (vec3EuclideanNorm_nonneg _) <|
      intervalIntegral.integral_nonneg zero_le_one (fun t _ => hgnn t)
  have hsquare : |f (x + h) - f x| ^ 2 ≤
      (vec3EuclideanNorm h * ∫ t in (0:ℝ)..1, g t) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hbase).2 hbound
  calc
    |f (x + h) - f x| ^ 2 ≤
        (vec3EuclideanNorm h * ∫ t in (0:ℝ)..1, g t) ^ 2 := hsquare
    _ = vec3EuclideanNorm h ^ 2 * (∫ t in (0:ℝ)..1, g t) ^ 2 := by ring
    _ ≤ vec3EuclideanNorm h ^ 2 * ∫ t in (0:ℝ)..1, g t ^ 2 := by
      exact mul_le_mul_of_nonneg_left hcauchy (sq_nonneg _)
    _ = _ := by simp [g]

def segmentSweep (K : Set Vec3) (h : Vec3) : Set Vec3 :=
  {z | ∃ x ∈ K, ∃ t ∈ Icc (0 : ℝ) 1, z = x + t • h}

private theorem smoothScalarIntegralSq
    {f : Vec3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    {K : Set Vec3} (hK : IsCompact K) (h : Vec3) :
    ∫ x in K, |f (x + h) - f x| ^ 2 ∂volume ≤
      vec3EuclideanNorm h ^ 2 *
        ∫ x in segmentSweep K h,
          vec3EuclideanNorm (CKN.classicalGradient f x) ^ 2 ∂volume := by
  let S := segmentSweep K h
  let g : Vec3 → ℝ := fun z => vec3EuclideanNorm (CKN.classicalGradient f z) ^ 2
  let F : Vec3 → ℝ → ℝ := fun x t => g (x + t • h)
  let μK : Measure Vec3 := volume.restrict K
  let μI : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hgradCont : Continuous (fun z : Vec3 => CKN.classicalGradient f z) := by
    apply continuous_pi
    intro i
    simpa only [CKN.classicalGradient_apply] using
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgCont : Continuous g :=
    continuous_pow 2 |>.comp (continuous_vec3EuclideanNorm.comp hgradCont)
  have hFCont : Continuous (Function.uncurry F) := by
    exact hgCont.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hprodSetCompact : IsCompact (K ×ˢ Icc (0 : ℝ) 1) := hK.prod isCompact_Icc
  have hFintOn : IntegrableOn (Function.uncurry F)
      (K ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) :=
    hFCont.continuousOn.integrableOn_compact hprodSetCompact
  have hFint : Integrable (Function.uncurry F) (μK.prod μI) := by
    simpa [F, μK, μI, IntegrableOn, Measure.prod_restrict] using hFintOn
  have hinnerInt : Integrable
      (fun x : Vec3 => ∫ t : ℝ, F x t ∂μI) μK := hFint.integral_prod_left
  have htimeInt : Integrable
      (fun t : ℝ => ∫ x : Vec3, F x t ∂μK) μI := hFint.integral_prod_right
  have hintervalEq (x : Vec3) :
      (∫ t : ℝ, F x t ∂μI) = ∫ t in (0 : ℝ)..1, g (x + t • h) := by
    change (∫ t in Icc (0 : ℝ) 1, g (x + t • h) ∂volume) = _
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
  have hinnerInt' : Integrable
      (fun x : Vec3 => ∫ t in (0 : ℝ)..1, g (x + t • h)) μK := by
    exact hinnerInt.congr (Filter.Eventually.of_forall hintervalEq)
  have hSchar : S =
      (fun z : Vec3 × ℝ => z.1 + z.2 • h) '' (K ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨x, hxK, t, ht, rfl⟩
      exact ⟨(x, t), ⟨hxK, ht⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hxK, ht⟩, rfl⟩
      exact ⟨x, hxK, t, ht, rfl⟩
  have hpathCont : Continuous (fun z : Vec3 × ℝ => z.1 + z.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hScompact : IsCompact S := by
    rw [hSchar]
    exact hprodSetCompact.image hpathCont
  have hSmeas : MeasurableSet S := hScompact.measurableSet
  have hgS : IntegrableOn g S volume := hgCont.continuousOn.integrableOn_compact hScompact
  have hgSnonneg : 0 ≤ᵐ[volume.restrict S] g :=
    Filter.Eventually.of_forall fun z => by positivity
  have hsetBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∫ x in K, g (x + t • h) ∂volume ≤ ∫ x in S, g x ∂volume := by
    rw [CKN.setIntegral_comp_addRight_translateSet (t • h) K g]
    apply setIntegral_mono_set hgS hgSnonneg
    filter_upwards [] with z hz
    have hzK : z - t • h ∈ K := (CKN.mem_translateSet_iff_sub_mem).1 hz
    exact ⟨z - t • h, hzK, t, ht, by rw [sub_add_cancel]⟩
  have hswap := integral_integral_swap (f := F) hFint
  have hdouble :
      (∫ x : Vec3, ∫ t : ℝ, F x t ∂μI ∂μK) ≤ ∫ x in S, g x ∂volume := by
    calc
      (∫ x : Vec3, ∫ t : ℝ, F x t ∂μI ∂μK) =
          ∫ t : ℝ, ∫ x : Vec3, F x t ∂μK ∂μI := hswap
      _ ≤ ∫ t : ℝ, (∫ x in S, g x ∂volume) ∂μI := by
        have hconstInt : Integrable (fun _ : ℝ => ∫ x in S, g x ∂volume) μI :=
          integrable_const _
        apply integral_mono_ae htimeInt hconstInt
        filter_upwards [ae_restrict_mem isCompact_Icc.measurableSet] with t ht
        change ∫ x in K, g (x + t • h) ∂volume ≤ _
        exact hsetBound t ht
      _ = ∫ x in S, g x ∂volume := by simp [μI]
  have hdiffCont : Continuous (fun x : Vec3 => f (x + h) - f x) := by
    exact hf.continuous.comp (continuous_id.add continuous_const) |>.sub hf.continuous
  have hleftInt : Integrable (fun x : Vec3 => |f (x + h) - f x| ^ 2) μK := by
    exact ((continuous_abs.comp hdiffCont).pow 2).continuousOn.integrableOn_compact hK |>.integrable
  have hPoint (x : Vec3) :
      |f (x + h) - f x| ^ 2 ≤ vec3EuclideanNorm h ^ 2 *
        ∫ t in (0 : ℝ)..1, g (x + t • h) := by
    simpa [g] using smoothScalarSegmentSq hf x h
  have hsqIntegral :
      (∫ x : Vec3, |f (x + h) - f x| ^ 2 ∂μK) ≤
        vec3EuclideanNorm h ^ 2 * ∫ x in S, g x ∂volume := by
    calc
      (∫ x : Vec3, |f (x + h) - f x| ^ 2 ∂μK) ≤
          ∫ x : Vec3, vec3EuclideanNorm h ^ 2 *
            (∫ t in (0 : ℝ)..1, g (x + t • h)) ∂μK :=
              integral_mono_ae hleftInt (by
                exact hinnerInt'.const_mul _) (Filter.Eventually.of_forall hPoint)
      _ = vec3EuclideanNorm h ^ 2 *
            (∫ x : Vec3, ∫ t : ℝ, F x t ∂μI ∂μK) := by
              rw [integral_const_mul]
              congr 1
              apply integral_congr_ae
              filter_upwards [] with x
              rw [← hintervalEq]
      _ ≤ vec3EuclideanNorm h ^ 2 * ∫ x in S, g x ∂volume :=
            mul_le_mul_of_nonneg_left hdouble (sq_nonneg _)
  simpa only [S, μK] using hsqIntegral

def mollifyVec3 (v : Vec3 → Vec3) (ε : ℝ) (hε : 0 < ε) : Vec3 → Vec3 :=
  fun x i => CKN.mollify (fun y => v y i) ε hε x

private theorem mollifyVec3_norm_le
    {v : Vec3 → Vec3} {ε : ℝ} (hε : 0 < ε)
    (hV : MemLp (fun x => WithLp.toLp 2 (v x)) 2 volume) (x : Vec3) :
    vec3EuclideanNorm (mollifyVec3 v ε hε x) ≤
      CKN.mollify (fun x => vec3EuclideanNorm (v x)) ε hε x := by
  let G : Vec3 → WithLp 2 Vec3 := fun y => WithLp.toLp 2 (v y)
  let ρ : Vec3 → ℝ := CKN.mollifier ε hε
  let L : ℝ →L[ℝ] WithLp 2 Vec3 →L[ℝ] WithLp 2 Vec3 :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hGloc : LocallyIntegrable G volume := hV.locallyIntegrable (by norm_num)
  have hconv : ConvolutionExists ρ G L volume := by
    exact (CKN.mollifier_hasCompactSupport hε).convolutionExists_left
      (L := L) (CKN.mollifier_contDiff hε (n := 0)).continuous hGloc
  let q : WithLp 2 Vec3 := convolution ρ G L volume x
  have hcoord (i : Fin 3) :
      (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 3 => ℝ) i) q =
        CKN.mollify (fun y => v y i) ε hε x := by
    change (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 3 => ℝ) i)
        (convolution ρ G L volume x) = _
    rw [convolution_def]
    have hmap := (PiLp.proj (𝕜 := ℝ) (p := 2)
      (β := fun _ : Fin 3 => ℝ) i).integral_comp_comm (hconv x)
    rw [hmap.symm]
    simp [G, L, ρ, CKN.mollify, convolution_def, PiLp.proj_apply,
      ContinuousLinearMap.lsmul_apply]
  have hqof : WithLp.ofLp q = mollifyVec3 v ε hε x := by
    funext i
    simpa [q, mollifyVec3, PiLp.proj_apply] using hcoord i
  have hqnorm : ‖q‖ = vec3EuclideanNorm (mollifyVec3 v ε hε x) := by
    calc
      ‖q‖ = ‖WithLp.toLp 2 (WithLp.ofLp q)‖ := by simp
      _ = ‖WithLp.toLp 2 (mollifyVec3 v ε hε x)‖ := by rw [hqof]
      _ = vec3EuclideanNorm (mollifyVec3 v ε hε x) := by
        rw [vec3EuclideanNorm_eq_l2]
  calc
    vec3EuclideanNorm (mollifyVec3 v ε hε x) = ‖q‖ := hqnorm.symm
    _ = ‖∫ y, ρ y • G (x - y) ∂volume‖ := by
      rfl
    _ ≤ ∫ y, ‖ρ y • G (x - y)‖ ∂volume := norm_integral_le_integral_norm _
    _ = ∫ y, ρ y * vec3EuclideanNorm (v (x - y)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (CKN.mollifier_nonneg hε y)]
      rw [show ρ y = CKN.mollifier ε hε y from rfl]
      rw [← vec3EuclideanNorm_eq_l2]
    _ = CKN.mollify (fun y => vec3EuclideanNorm (v y)) ε hε x := by
      change (∫ y, CKN.mollifier ε hε y *
        vec3EuclideanNorm (v (x - y)) ∂volume) = _
      rw [CKN.mollify, MeasureTheory.convolution_def]
      rfl

private theorem eLpNorm_two_le_of_integral_sq
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
    {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) ν)
    (hI : ∫ x, |f x| ^ 2 ∂μ ≤ c ^ 2 * ∫ x, |g x| ^ 2 ∂ν) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal c * eLpNorm g 2 ν := by
  have hfFormula : lpNorm f 2 μ = Real.sqrt (∫ x, |f x| ^ 2 ∂μ) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hf.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hgFormula : lpNorm g 2 ν = Real.sqrt (∫ x, |g x| ^ 2 ∂ν) := by
    rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      hg.aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hroot := Real.sqrt_le_sqrt hI
  have hrootEq : Real.sqrt (c ^ 2 * ∫ x, |g x| ^ 2 ∂ν) =
      c * Real.sqrt (∫ x, |g x| ^ 2 ∂ν) := by
    rw [Real.sqrt_mul (sq_nonneg c) (∫ x, |g x| ^ 2 ∂ν),
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg hc]
  have hLp : lpNorm f 2 μ ≤ c * lpNorm g 2 ν := by
    rw [hfFormula, hgFormula]
    exact hroot.trans_eq hrootEq
  calc
    eLpNorm f 2 μ = ENNReal.ofReal (lpNorm f 2 μ) :=
      (MeasureTheory.ofReal_lpNorm hf).symm
    _ ≤ ENNReal.ofReal (c * lpNorm g 2 ν) := ENNReal.ofReal_le_ofReal hLp
    _ = ENNReal.ofReal c * eLpNorm g 2 ν := by
      rw [ENNReal.ofReal_mul hc, ← MeasureTheory.ofReal_lpNorm hg]

private theorem mollify_eLpNorm_le_two {f : Vec3 → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hf : AEMeasurable f volume) :
    eLpNorm (CKN.mollify f ε hε) 2 volume ≤ eLpNorm f 2 volume := by
  have hkernelInt : Integrable (CKN.mollifier ε hε) volume :=
    (CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous.integrable_of_hasCompactSupport
      (CKN.mollifier_hasCompactSupport (d := 3) hε)
  simpa only [CKN.mollify] using
    CKN.young_convolution_nonneg_integral_one_of_aemeasurable
      (p := (2 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top
      (CKN.mollifier_nonneg (d := 3) hε) hkernelInt (CKN.mollifier_integral_one (d := 3) hε)
      (CKN.mollifier_contDiff (d := 3) hε (n := 0)).continuous.measurable hf

private theorem segmentSweep_isCompact {K : Set Vec3} (hK : IsCompact K) (h : Vec3) :
    IsCompact (segmentSweep K h) := by
  have hEq : segmentSweep K h =
      (fun z : Vec3 × ℝ => z.1 + z.2 • h) '' (K ×ˢ Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨(x, t), ⟨hx, ht⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨x, hx, t, ht, rfl⟩
  rw [hEq]
  exact (hK.prod isCompact_Icc).image
    (continuous_fst.add (continuous_snd.smul continuous_const))

/-- Scalar translation is controlled by the weak gradient on the region swept
out by the connecting segments. -/
private theorem scalarTranslationEstimateL2
    {U : Set Vec3} (hU : IsOpen U) (u : CKN.H1Function U)
    {K : Set Vec3} (hK : IsCompact K) (h : Vec3)
    (hsegment : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    eLpNorm (fun x => u.toFun (x + h) - u.toFun x) 2 (volume.restrict K) ≤
      ENNReal.ofReal (vec3EuclideanNorm h) *
        eLpNorm (fun x => vec3EuclideanNorm (u.grad x)) 2 (volume.restrict U) := by
  let S : Set Vec3 := segmentSweep K h
  let g : Vec3 → ℝ := U.indicator u.toFun
  let G : Vec3 → Vec3 := U.indicator u.grad
  let gN : Vec3 → ℝ := fun x => vec3EuclideanNorm (G x)
  have hUmeas : MeasurableSet U := hU.measurableSet
  have hScompact : IsCompact S := by
    exact segmentSweep_isCompact hK h
  have hSmeas : MeasurableSet S := hScompact.measurableSet
  have hSsubU : S ⊆ U := by
    intro z hz
    rcases hz with ⟨x, hx, t, ht, rfl⟩
    exact hsegment x hx t ht
  obtain ⟨δ, hδ, hthick⟩ := hScompact.exists_cthickening_subset_open hU hSsubU
  have hδpos : 0 < δ := hδ
  let ε : ℕ → ℝ := fun n => δ / ((n : ℝ) + 2)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεle (n : ℕ) : ε n ≤ δ := by
    dsimp [ε]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith only [hn]
    simpa only [div_one] using
      (div_le_div_of_nonneg_left hδpos.le (by positivity) hden)
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    simpa only [add_comm] using
      (tendsto_atTop_add_const_left atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hεinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hεlim : Tendsto ε atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => δ) atTop (nhds δ)).mul hεinv
    simpa only [ε, div_eq_mul_inv, mul_zero] using hmul
  have huGlobal : MemLp g 2 volume := by
    rw [memLp_indicator_iff_restrict hUmeas]
    exact u.memL2
  have hGi (i : Fin 3) : MemLp (fun x => G x i) 2 volume := by
    have hEq : (fun x => G x i) = U.indicator (fun x => u.grad x i) := by
      funext x
      by_cases hx : x ∈ U <;> simp [G, hx]
    rw [hEq]
    rw [memLp_indicator_iff_restrict hUmeas]
    exact u.grad_memL2 i
  have hGvec : MemLp (fun x => WithLp.toLp 2 (G x)) 2 volume := by
    apply MeasureTheory.memLp_piLp_iff.mpr
    intro i
    simpa [G, PiLp.proj_apply] using hGi i
  have hGnorm : MemLp gN 2 volume := by
    simpa only [gN, vec3EuclideanNorm_eq_l2] using hGvec.norm
  have hGnormEq : gN = U.indicator (fun x => vec3EuclideanNorm (u.grad x)) := by
    funext x
    by_cases hx : x ∈ U <;> simp [gN, G, hx, vec3EuclideanNorm]
  have hGnormU : eLpNorm gN 2 volume =
      eLpNorm (fun x => vec3EuclideanNorm (u.grad x)) 2 (volume.restrict U) := by
    rw [hGnormEq, eLpNorm_indicator_eq_eLpNorm_restrict hUmeas]
  have hgLoc : LocallyIntegrable g volume := huGlobal.locallyIntegrable (by norm_num)
  have hGiLoc (i : Fin 3) : LocallyIntegrable (fun x => G x i) volume :=
    (hGi i).locallyIntegrable (by norm_num)
  have hweak (i : Fin 3) : CKN.HasWeakPartialDerivOn U i g (fun x => G x i) := by
    intro φ hφ hφcompact hφU
    have hleft :
        (∫ x in U, g x * (fderiv ℝ φ x) (CKN.basisVec i) ∂volume) =
          ∫ x in U, u.toFun x * (fderiv ℝ φ x) (CKN.basisVec i) ∂volume := by
      apply setIntegral_congr_ae hUmeas
      filter_upwards [] with x
      intro hx
      simp [g, hx]
    have hright :
        (∫ x in U, (fun y => G y i) x * φ x ∂volume) =
          ∫ x in U, (u.grad x i) * φ x ∂volume := by
      apply setIntegral_congr_ae hUmeas
      filter_upwards [] with x
      intro hx
      simp [G, hx]
    rw [hleft, hright]
    exact u.hasWeakPartialDerivOn i φ hφ hφcompact hφU
  let f : ℕ → Vec3 → ℝ := fun n => CKN.mollify g (ε n) (hεpos n)
  have hErr : Tendsto
      (fun n => eLpNorm (fun x => f n x - g x) 2 volume) atTop (nhds 0) := by
    simpa [f] using
      (CKN.tendsto_eLpNorm_sub_zero_mollify (p := (2 : ℝ≥0∞))
        (by norm_num) ENNReal.coe_ne_top huGlobal hεlim hεpos)
  have hgnAEMeas : AEMeasurable gN volume := hGnorm.aestronglyMeasurable.aemeasurable
  have hgnConvBound (n : ℕ) :
      eLpNorm (CKN.mollify gN (ε n) (hεpos n)) 2 volume ≤ eLpNorm gN 2 volume :=
    mollify_eLpNorm_le_two (hεpos n) hgnAEMeas
  have hgnConvMem (n : ℕ) : MemLp (CKN.mollify gN (ε n) (hεpos n)) 2 volume := by
    rw [memLp_iff]
    exact (hgnConvBound n).trans_lt hGnorm
  have hGconvCoordMem (n : ℕ) (i : Fin 3) :
      MemLp (CKN.mollify (fun x => G x i) (ε n) (hεpos n)) 2 volume := by
    rw [memLp_iff]
    exact (mollify_eLpNorm_le_two (hεpos n)
      (hGi i).aestronglyMeasurable.aemeasurable).trans_lt (hGi i)
  have hGconvMem (n : ℕ) :
      MemLp (fun x => WithLp.toLp 2 (mollifyVec3 G (ε n) (hεpos n) x)) 2 volume := by
    apply MeasureTheory.memLp_piLp_iff.mpr
    intro i
    simpa [mollifyVec3, PiLp.proj_apply] using hGconvCoordMem n i
  have hGconvNormMem (n : ℕ) :
      MemLp (fun x => vec3EuclideanNorm (mollifyVec3 G (ε n) (hεpos n) x))
        2 volume := by
    simpa only [vec3EuclideanNorm_eq_l2] using (hGconvMem n).norm
  have hfnCont (n : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (f n) := by
    simpa [f] using CKN.mollify_contDiff (hεpos n) hgLoc (n := (⊤ : ℕ∞))
  have hgradFn (n : ℕ) (i : Fin 3) (x : Vec3) (hx : x ∈ S) :
      (fderiv ℝ (f n) x) (CKN.basisVec i) =
        CKN.mollify (fun y => G y i) (ε n) (hεpos n) x := by
    apply CKN.fderiv_mollify_eq_mollify_of_hasWeakPartialDerivOn
      hU hgLoc (hGiLoc i) (hweak i) (hεpos n)
    exact (Metric.closedBall_subset_closedBall (hεle n)).trans <|
      (Metric.closedBall_subset_cthickening hx δ).trans hthick
  have hgradFnVec (n : ℕ) (x : Vec3) (hx : x ∈ S) :
      CKN.classicalGradient (f n) x = mollifyVec3 G (ε n) (hεpos n) x := by
    funext i
    simpa [mollifyVec3, CKN.classicalGradient_apply] using hgradFn n i x hx
  have hgradFnContinuous (n : ℕ) :
      Continuous (fun x => CKN.classicalGradient (f n) x) := by
    apply continuous_pi
    intro i
    simpa only [CKN.classicalGradient_apply] using
      ((hfnCont n).continuous_fderiv
        (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
  have hgradFnNormMem (n : ℕ) :
      MemLp (fun x => vec3EuclideanNorm (CKN.classicalGradient (f n) x))
        2 (volume.restrict S) := by
    have hsource : MemLp
        (fun x => vec3EuclideanNorm (mollifyVec3 G (ε n) (hεpos n) x)) 2
        (volume.restrict S) :=
      (hGconvNormMem n).mono_measure Measure.restrict_le_self
    apply hsource.mono'
      ((continuous_vec3EuclideanNorm.comp (hgradFnContinuous n)).aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem (μ := volume) hSmeas] with x hx
    rw [Function.comp_apply, hgradFnVec n x hx]
    exact (abs_of_nonneg (vec3EuclideanNorm_nonneg _)).le
  have hgradFnBound (n : ℕ) :
      eLpNorm (fun x => vec3EuclideanNorm (CKN.classicalGradient (f n) x))
          2 (volume.restrict S) ≤
        eLpNorm (fun x => vec3EuclideanNorm (u.grad x))
          2 (volume.restrict U) := by
    calc
      eLpNorm (fun x => vec3EuclideanNorm (CKN.classicalGradient (f n) x))
          2 (volume.restrict S) =
        eLpNorm (fun x => vec3EuclideanNorm (mollifyVec3 G (ε n) (hεpos n) x))
          2 (volume.restrict S) := by
            apply eLpNorm_congr_ae
            filter_upwards [ae_restrict_mem (μ := volume) hSmeas] with x hx
            rw [hgradFnVec n x hx]
      _ = eLpNorm (fun x => WithLp.toLp 2 (mollifyVec3 G (ε n) (hεpos n) x))
          2 (volume.restrict S) := by
            simpa only [vec3EuclideanNorm_eq_l2] using
              (eLpNorm_norm (fun x => WithLp.toLp 2 (mollifyVec3 G (ε n) (hεpos n) x))
                ((hGconvMem n).mono_measure Measure.restrict_le_self).aestronglyMeasurable)
      _ ≤ eLpNorm (fun x => WithLp.toLp 2 (mollifyVec3 G (ε n) (hεpos n) x))
          2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ eLpNorm (CKN.mollify gN (ε n) (hεpos n)) 2 volume := by
            apply eLpNorm_mono_ae_real (hGconvMem n).aestronglyMeasurable
            filter_upwards [] with x
            simpa only [vec3EuclideanNorm_eq_l2, gN] using
              mollifyVec3_norm_le (hεpos n) hGvec x
      _ ≤ eLpNorm gN 2 volume := hgnConvBound n
      _ = eLpNorm (fun x => vec3EuclideanNorm (u.grad x))
          2 (volume.restrict U) := hGnormU
  have hfnMem (n : ℕ) : MemLp (f n) 2 volume := by
    rw [memLp_iff]
    simpa [f] using
      (mollify_eLpNorm_le_two (hεpos n)
        huGlobal.aestronglyMeasurable.aemeasurable).trans_lt huGlobal
  have hfnShiftMem (n : ℕ) : MemLp (fun x => f n (x + h)) 2 volume :=
    (hfnMem n).comp_measurePreserving (measurePreserving_add_right volume h)
  have hdiffMem (n : ℕ) :
      MemLp (fun x => f n (x + h) - f n x) 2 (volume.restrict K) :=
    ((hfnShiftMem n).sub (hfnMem n)).mono_measure Measure.restrict_le_self
  have hgradBound (n : ℕ) :
      eLpNorm (fun x => f n (x + h) - f n x) 2 (volume.restrict K) ≤
        ENNReal.ofReal (vec3EuclideanNorm h) *
          eLpNorm (fun x => vec3EuclideanNorm (u.grad x)) 2 (volume.restrict U) := by
    have hInt := smoothScalarIntegralSq (hfnCont n) hK h
    have hInt' :
        ∫ x, |f n (x + h) - f n x| ^ 2 ∂(volume.restrict K) ≤
          vec3EuclideanNorm h ^ 2 *
            ∫ x, |vec3EuclideanNorm (CKN.classicalGradient (f n) x)| ^ 2
              ∂(volume.restrict S) := by
      simpa [f, S, Real.norm_eq_abs, sq_abs] using hInt
    calc
      eLpNorm (fun x => f n (x + h) - f n x) 2 (volume.restrict K) ≤
          ENNReal.ofReal (vec3EuclideanNorm h) *
            eLpNorm (fun x => vec3EuclideanNorm (CKN.classicalGradient (f n) x))
              2 (volume.restrict S) :=
            eLpNorm_two_le_of_integral_sq (vec3EuclideanNorm_nonneg h)
              (hdiffMem n) (hgradFnNormMem n) hInt'
      _ ≤ ENNReal.ofReal (vec3EuclideanNorm h) *
          eLpNorm (fun x => vec3EuclideanNorm (u.grad x)) 2 (volume.restrict U) :=
            mul_le_mul_of_nonneg_left (hgradFnBound n) (by positivity)
  let d : Vec3 → ℝ := fun x => u.toFun (x + h) - u.toFun x
  let dₙ : ℕ → Vec3 → ℝ := fun n x => f n (x + h) - f n x
  have hErrShift (n : ℕ) :
      eLpNorm (fun x => f n (x + h) - g (x + h)) 2 volume =
        eLpNorm (fun x => f n x - g x) 2 volume := by
    calc
      eLpNorm (fun x => f n (x + h) - g (x + h)) 2 volume =
          eLpNorm ((fun y => f n y - g y) ∘ fun x => x + h) 2 volume := by
            apply eLpNorm_congr_ae
            filter_upwards [] with x
            rfl
      _ = eLpNorm (fun x => f n x - g x) 2 volume :=
        eLpNorm_comp_measurePreserving (p := (2 : ℝ≥0∞))
        ((hfnMem n).sub huGlobal).aestronglyMeasurable
        (measurePreserving_add_right volume h)
  have hdiffErrBound (n : ℕ) :
      eLpNorm (fun x => dₙ n x - d x) 2 (volume.restrict K) ≤
        2 * eLpNorm (fun x => f n x - g x) 2 volume := by
    have hEq : (fun x => dₙ n x - d x) =ᵐ[volume.restrict K]
        (fun x => (f n (x + h) - g (x + h)) - (f n x - g x)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) (s := K)
        hK.measurableSet] with x hx
      have hx0 : x ∈ U := by simpa using hsegment x hx 0 (by norm_num)
      have hx1 : x + h ∈ U := by
        simpa using hsegment x hx 1 (by norm_num)
      change (f n (x + h) - f n x) - (u.toFun (x + h) - u.toFun x) = _
      simp [g, hx0, hx1]
      ring
    rw [eLpNorm_congr_ae hEq]
    calc
      eLpNorm (fun x => (f n (x + h) - g (x + h)) - (f n x - g x))
          2 (volume.restrict K) ≤
        eLpNorm (fun x => f n (x + h) - g (x + h)) 2 (volume.restrict K) +
          eLpNorm (fun x => f n x - g x) 2 (volume.restrict K) :=
            eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      _ ≤ eLpNorm (fun x => f n (x + h) - g (x + h)) 2 volume +
          eLpNorm (fun x => f n x - g x) 2 volume := by
            apply add_le_add
            · exact eLpNorm_mono_measure _ Measure.restrict_le_self
            · exact eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = 2 * eLpNorm (fun x => f n x - g x) 2 volume := by
            rw [hErrShift n, two_mul]
  have hdiffErr : Tendsto
      (fun n => eLpNorm (fun x => dₙ n x - d x) 2 (volume.restrict K))
      atTop (nhds 0) := by
    have htwice : Tendsto
        (fun n => 2 * eLpNorm (fun x => f n x - g x) 2 volume) atTop (nhds 0) := by
      refine ENNReal.tendsto_nhds_zero.2 ?_
      intro η hη
      filter_upwards [ENNReal.tendsto_nhds_zero.1 hErr (η / 2)
        (ENNReal.half_pos hη.ne')] with n hn
      calc
        2 * eLpNorm (fun x => f n x - g x) 2 volume ≤ 2 * (η / 2) :=
          mul_le_mul_of_nonneg_left hn (by norm_num)
        _ = η := ENNReal.mul_div_cancel (by norm_num) ENNReal.coe_ne_top
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds htwice (Eventually.of_forall fun _ => zero_le)
        (Eventually.of_forall hdiffErrBound)
  have hInMeasure : TendstoInMeasure (volume.restrict K) dₙ atTop d :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hdiffErr
  have hdnAEMeas (n : ℕ) : AEStronglyMeasurable (dₙ n) (volume.restrict K) :=
    (hdiffMem n).aestronglyMeasurable
  have hdAEMeas : AEStronglyMeasurable d (volume.restrict K) := by
    have hglobal : AEStronglyMeasurable (fun x => g (x + h) - g x) volume := by
      exact ((huGlobal.aestronglyMeasurable.comp_measurePreserving
        (measurePreserving_add_right volume h)).sub huGlobal.aestronglyMeasurable)
    have hEq : d =ᵐ[volume.restrict K] (fun x => g (x + h) - g x) := by
      filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) (s := K)
        hK.measurableSet] with x hx
      have hx0 : x ∈ U := by simpa using hsegment x hx 0 (by norm_num)
      have hx1 : x + h ∈ U := by
        simpa using hsegment x hx 1 (by norm_num)
      simp [d, g, hx0, hx1]
    exact hglobal.restrict.congr hEq.symm
  exact eLpNorm_le_of_tendstoInMeasure
    (Eventually.of_forall hgradBound) hInMeasure hdnAEMeas

/-- For a three component Sobolev field, each component's local `L²`
translation is controlled by the corresponding weak gradient. The connecting
segments stay in `U`, as in the local approximation used in `lem:compactness`.
-/
theorem translationEstimateL2
    {U : Set Vec3} (hU : IsOpen U) (u : Fin 3 → CKN.H1Function U)
    {K : Set Vec3} (hK : IsCompact K) (h : Vec3)
    (hsegment : ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ U) :
    ∀ i : Fin 3,
      eLpNorm (fun x => (u i).toFun (x + h) - (u i).toFun x) 2 (volume.restrict K) ≤
        ENNReal.ofReal (vec3EuclideanNorm h) *
          eLpNorm (fun x => vec3EuclideanNorm ((u i).grad x)) 2 (volume.restrict U) := by
  intro i
  exact scalarTranslationEstimateL2 hU (u i) hK h hsegment

end CKN.Foundation.Sobolev

end
