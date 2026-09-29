-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegEquicontinuitySourceMain

/-!
# `lem:reg-equicontinuity`

For every `w ∈ C_c^∞(ℝ³;ℝ³)`, every `0 < ε ≤ 1` and every `0 ≤ s < t`,
`|∫ (u_ε(x,t) - u_ε(x,s))·w(x) dx| ≤ C(A) N(w) |t - s|^{2/5}` with
`N(w) = ‖w‖₂ + ‖Δw‖₂ + ‖∇w‖_∞ + ‖∇w‖_{5/2}`, `A = ‖a‖₂`, `C(A) = C₀ (A + A²)`.
The constant `C₀` depends only on the Gagliardo–Nirenberg and
Calderón–Zygmund constants.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The pointwise bound of a first derivative by the differential. -/
private theorem regEquiSrcFinal_deriv_le_pt {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (i j : Fin 3) (x : Vec3) :
    |spatialDeriv (fun y => w y i) j x| ≤ ‖fderiv ℝ w x‖ := by
  have hcomp : fderiv ℝ (fun y => w y i) x =
      (ContinuousLinearMap.proj i).comp (fderiv ℝ w x) :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x
      ((hw.differentiable (by simp)) x).hasFDerivAt).fderiv
  change |fderiv ℝ (fun y => w y i) x (CKN.basisVec j)| ≤ _
  rw [hcomp]
  change |(fderiv ℝ w x (CKN.basisVec j)) i| ≤ _
  calc |(fderiv ℝ w x (CKN.basisVec j)) i| = ‖(fderiv ℝ w x (CKN.basisVec j)) i‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ w x (CKN.basisVec j)‖ := norm_le_pi_norm _ i
    _ ≤ ‖fderiv ℝ w x‖ * ‖CKN.basisVec j‖ := (fderiv ℝ w x).le_opNorm _
    _ = ‖fderiv ℝ w x‖ := by simp [CKN.basisVec, Pi.norm_single]

/-- Components of a square-integrable vector field have no larger `L²` norm. -/
private theorem regEquiSrcFinal_component_le {f : Vec3 → Vec3} (hf : MemLp f 2 volume)
    (i : Fin 3) :
    (eLpNorm (fun x => f x i) 2 volume).toReal ≤ (eLpNorm f 2 volume).toReal := by
  refine ENNReal.toReal_mono hf.eLpNorm_ne_top ?_
  refine eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable hf.aestronglyMeasurable)
    fun x => ?_
  exact norm_le_pi_norm (f x) i

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


/-- `lem:reg-equicontinuity`. -/
theorem regEquicontinuity_source
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (_hε : 0 < ε) (_hεone : ε ≤ 1)
        (w : Vec3 → Vec3), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
        ∀ s t : ℝ, 0 ≤ s → s < t →
          |∫ x, ∑ i : Fin 3, (uε a ha ε (x, t) i - uε a ha ε (x, s) i) * w x i| ≤
            C₀ * ((eLpNorm a 2 volume).toReal + (eLpNorm a 2 volume).toReal ^ 2) *
              ((eLpNorm w 2 volume).toReal +
                (eLpNorm (fun x (i : Fin 3) => spatialLaplacian (fun y => w y i) x) 2
                  volume).toReal +
                (⨆ x, ‖fderiv ℝ w x‖) +
                (eLpNorm (fun x => fderiv ℝ w x) (ENNReal.ofReal (5 / 2 : ℝ))
                  volume).toReal) *
              (t - s) ^ (2 / 5 : ℝ) := by
  have hKp := regEquiSrcPressureConstant_nonneg
  refine ⟨4 * (9 + 3 * regEquiSrcPressureConstant), by positivity, ?_⟩
  intro a ha ε hε _hε1 w hw hwc s t hs hst
  set A : ℝ := (eLpNorm a 2 volume).toReal with hA_def
  set AE : ℝ := (eLpNorm (regUniformSpatialField a) 2 volume).toReal with hAE_def
  set n1 : ℝ := (eLpNorm w 2 volume).toReal with hn1
  set n2 : ℝ := (eLpNorm (fun x (i : Fin 3) => spatialLaplacian (fun y => w y i) x) 2
    volume).toReal with hn2
  set G : ℝ := ⨆ x, ‖fderiv ℝ w x‖ with hG
  set n4 : ℝ := (eLpNorm (fun x => fderiv ℝ w x) (ENNReal.ofReal (5 / 2 : ℝ))
    volume).toReal with hn4
  set Kp := regEquiSrcPressureConstant with hKp_def
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hAE0 : 0 ≤ AE := ENNReal.toReal_nonneg
  have hn10 : 0 ≤ n1 := ENNReal.toReal_nonneg
  have hn20 : 0 ≤ n2 := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (regEquiSrc_deriv_le hw hwc 0 0 0)
  have hn40 : 0 ≤ n4 := ENNReal.toReal_nonneg
  have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => w y i) := fun i =>
    (contDiff_apply ℝ ℝ i).comp hw
  have hwL2 : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hwc
  -- the Laplacian
  have hLap : MemLp (fun x (i : Fin 3) => spatialLaplacian (fun y => w y i) x) 2 volume := by
    refine Continuous.memLp_of_hasCompactSupport ?_ ?_
    · refine continuous_pi fun i => ?_
      exact continuous_finsetSum _ fun j _ => (CKN.contDiff_spatialDeriv_smooth
        (CKN.contDiff_spatialDeriv_smooth (hwi i) j) j).continuous
    · refine HasCompactSupport.intro hwc fun x hx => ?_
      funext i
      have hd : x ∉ tsupport (fun y => spatialDeriv (fun y => w y i) i y) := fun h => hx
        ((tsupport_fderiv_apply_subset ℝ (CKN.basisVec i)).trans
          (tsupport_comp_subset (g := fun v : Vec3 => v i) rfl w) h)
      simp only [spatialLaplacian, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hdj : x ∉ tsupport (fun y => spatialDeriv (fun y => w y i) j y) := fun h => hx
        ((tsupport_fderiv_apply_subset ℝ (CKN.basisVec j)).trans
          (tsupport_comp_subset (g := fun v : Vec3 => v i) rfl w) h)
      have hdd : x ∉ tsupport (fun y => spatialDeriv (spatialDeriv (fun y => w y i) j) j y) :=
        fun h => hdj (tsupport_fderiv_apply_subset ℝ (CKN.basisVec j) h)
      exact image_eq_zero_of_notMem_tsupport
        (f := fun y => spatialDeriv (spatialDeriv (fun y => w y i) j) j y) hdd
  have hF1 : (∑ i : Fin 3, (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) ≤
      3 * n2 := by
    have h : ∀ i : Fin 3, (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal ≤ n2 :=
      fun i => regEquiSrcFinal_component_le hLap i
    calc _ ≤ ∑ _i : Fin 3, n2 := Finset.sum_le_sum fun i _ => h i
      _ = 3 * n2 := by simp
  -- the divergence
  have hF2 : (eLpNorm (fun x => ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x)
      (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal ≤ 3 * n4 := by
    have hDw : MemLp (fun x => fderiv ℝ w x) (ENNReal.ofReal (5 / 2 : ℝ)) volume :=
      (hw.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hwc.fderiv (𝕜 := ℝ))
    have hdivm : AEStronglyMeasurable (fun x => ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x)
        volume := (continuous_finsetSum _ fun i _ =>
          (CKN.contDiff_spatialDeriv_smooth (hwi i) i).continuous).aestronglyMeasurable
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := 3) hdivm
      (g := fun x => fderiv ℝ w x) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i : Fin 3, |spatialDeriv (fun y => w y i) i x| ≤ ∑ _i : Fin 3, ‖fderiv ℝ w x‖ :=
              Finset.sum_le_sum fun i _ => regEquiSrcFinal_deriv_le_pt hw i i x
          _ = 3 * ‖fderiv ℝ w x‖ := by simp) (ENNReal.ofReal (5 / 2 : ℝ))
    have hfin : ENNReal.ofReal 3 * eLpNorm (fun x => fderiv ℝ w x)
        (ENNReal.ofReal (5 / 2 : ℝ)) volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDw.eLpNorm_ne_top
    calc _ ≤ (ENNReal.ofReal 3 * eLpNorm (fun x => fderiv ℝ w x)
          (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal := ENNReal.toReal_mono hfin hle
      _ = 3 * n4 := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  -- the pairings
  obtain ⟨⟨hSlice, -⟩, -⟩ := hregularised a ha ε hε
  have hpair : ∀ τ, 0 ≤ τ → Integrable (fun x => ∑ i : Fin 3, uε a ha ε (x, τ) i * w x i) ∧
      |∫ x, ∑ i : Fin 3, uε a ha ε (x, τ) i * w x i| ≤ 3 * AE * n1 := by
    intro τ hτ
    have hc : ∀ i, Integrable (fun x => uε a ha ε (x, τ) i * w x i) volume := fun i =>
      ((hSlice τ hτ).eval i).integrable_mul (hwL2.eval i)
    refine ⟨integrable_finsetSum _ fun i _ => hc i, ?_⟩
    rw [integral_finsetSum _ fun i _ => hc i]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 3, |∫ x, uε a ha ε (x, τ) i * w x i| ≤ ∑ _i : Fin 3, AE * n1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨hmem, hle⟩ := regEquiSrc_slice_component ρ uε pε hregularised a ha ε hε τ hτ i
          refine (abs_integral_mul_le_eLpNorm_two hmem (hwL2.eval i)).trans ?_
          exact mul_le_mul hle (regEquiSrcFinal_component_le hwL2 i) ENNReal.toReal_nonneg hAE0
      _ = 3 * AE * n1 := by simp; ring
  have hlhs : (∫ x, ∑ i : Fin 3, (uε a ha ε (x, t) i - uε a ha ε (x, s) i) * w x i) =
      (∫ x, ∑ i : Fin 3, uε a ha ε (x, t) i * w x i) -
        ∫ x, ∑ i : Fin 3, uε a ha ε (x, s) i * w x i := by
    rw [← integral_sub (hpair t (hs.trans hst.le)).1 (hpair s hs).1]
    congr 1
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hF3 : |(∫ x, ∑ i : Fin 3, uε a ha ε (x, t) i * w x i) -
      ∫ x, ∑ i : Fin 3, uε a ha ε (x, s) i * w x i| ≤ 6 * AE * n1 := by
    refine (abs_sub _ _).trans ?_
    have h1 := (hpair t (hs.trans hst.le)).2
    have h2 := (hpair s hs).2
    linarith only [h1, h2]
  -- the Euclidean and the sup-norm `L²` norms of the datum
  have hAEA : AE ≤ 2 * A := by
    have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
    have hle : eLpNorm (fun x : Vec3 => vec3EuclideanNorm (a x)) 2 volume ≤
        ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume := by
      refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
          ha.1.aestronglyMeasurable) ?_ 2
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact vec3EuclideanNorm_le_sqrt_three_mul_norm _
    have hfin : ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ha.1.eLpNorm_ne_top
    have h3 : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hAE' : AE ≤ Real.sqrt 3 * A := by
      rw [hAE_def, ← hfield]
      calc _ ≤ (ENNReal.ofReal (Real.sqrt 3) * eLpNorm a 2 volume).toReal :=
            ENNReal.toReal_mono hfin hle
        _ = Real.sqrt 3 * A := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact hAE'.trans (mul_le_mul_of_nonneg_right h3 hA0)
  -- the increment bound
  have hinc := regEquiSrc_increment_le ρ uε pε hregularised a ha ε hε w hw hwc hs hst
  set N : ℝ := n1 + n2 + G + n4 with hN
  set B : ℝ := 6 * AE * n1 + 3 * AE * n2 + 9 * AE ^ 2 * G + 3 * Kp * AE ^ 2 * n4 with hB
  have hts : 0 < t - s := sub_pos.2 hst
  have hpow0 : 0 ≤ (t - s) ^ (2 / 5 : ℝ) := Real.rpow_nonneg hts.le _
  have hmain : |(∫ x, ∑ i : Fin 3, uε a ha ε (x, t) i * w x i) -
      ∫ x, ∑ i : Fin 3, uε a ha ε (x, s) i * w x i| ≤ B * (t - s) ^ (2 / 5 : ℝ) := by
    rcases le_total (t - s) 1 with h1 | h1
    · have hlin : t - s ≤ (t - s) ^ (2 / 5 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hts h1 (by norm_num : (2 / 5 : ℝ) ≤ 1)
        rwa [Real.rpow_one] at h
      have hX : 0 ≤ AE * (∑ i : Fin 3,
          (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) +
          9 * AE ^ 2 * G := by
        have : 0 ≤ ∑ i : Fin 3, (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal :=
          Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
        positivity
      have hstep1 : (t - s) * (AE * (∑ i : Fin 3,
          (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) + 9 * AE ^ 2 * G) ≤
          (t - s) ^ (2 / 5 : ℝ) * (AE * (3 * n2) + 9 * AE ^ 2 * G) := by
        calc _ ≤ (t - s) ^ (2 / 5 : ℝ) * (AE * (∑ i : Fin 3,
              (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) +
                9 * AE ^ 2 * G) := mul_le_mul_of_nonneg_right hlin hX
          _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ hpow0
            have := mul_le_mul_of_nonneg_left hF1 hAE0
            linarith only [this]
      have hstep2 : Kp * AE ^ 2 * (eLpNorm (fun x => ∑ i : Fin 3,
          spatialDeriv (fun y => w y i) i x) (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
          (t - s) ^ (2 / 5 : ℝ) ≤ Kp * AE ^ 2 * (3 * n4) * (t - s) ^ (2 / 5 : ℝ) := by
        have hKA : 0 ≤ Kp * AE ^ 2 := mul_nonneg hKp (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF2 hKA) hpow0
      have hextra : 0 ≤ 6 * AE * n1 * (t - s) ^ (2 / 5 : ℝ) := by positivity
      calc _ ≤ _ := hinc
        _ ≤ B * (t - s) ^ (2 / 5 : ℝ) := by
          rw [hB]
          nlinarith only [hstep1, hstep2, hextra]
    · have hone : 1 ≤ (t - s) ^ (2 / 5 : ℝ) := Real.one_le_rpow h1 (by norm_num)
      have hB6 : 6 * AE * n1 ≤ B := by
        rw [hB]
        have : 0 ≤ 3 * AE * n2 + 9 * AE ^ 2 * G + 3 * Kp * AE ^ 2 * n4 := by positivity
        linarith only [this]
      have hB0 : 0 ≤ B := le_trans (by positivity) hB6
      calc _ ≤ 6 * AE * n1 := hF3
        _ ≤ B := hB6
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * (t - s) ^ (2 / 5 : ℝ) := mul_le_mul_of_nonneg_left hone hB0
  -- comparison of the constants
  have hBN : B ≤ (9 + 3 * Kp) * (AE + AE ^ 2) * N := by
    rw [hB, hN]
    nlinarith only [hAE0, hn10, hn20, hG0, hn40, hKp, sq_nonneg AE,
      mul_nonneg hAE0 hn10, mul_nonneg hAE0 hn20, mul_nonneg hAE0 hG0, mul_nonneg hAE0 hn40,
      mul_nonneg (sq_nonneg AE) hn10, mul_nonneg (sq_nonneg AE) hn20,
      mul_nonneg (sq_nonneg AE) hG0, mul_nonneg (sq_nonneg AE) hn40,
      mul_nonneg (mul_nonneg hKp hAE0) hn10, mul_nonneg (mul_nonneg hKp hAE0) hn20,
      mul_nonneg (mul_nonneg hKp hAE0) hG0, mul_nonneg (mul_nonneg hKp hAE0) hn40,
      mul_nonneg (mul_nonneg hKp (sq_nonneg AE)) hn10,
      mul_nonneg (mul_nonneg hKp (sq_nonneg AE)) hn20,
      mul_nonneg (mul_nonneg hKp (sq_nonneg AE)) hG0]
  have hAEA2 : AE + AE ^ 2 ≤ 4 * (A + A ^ 2) := by
    have h2 : AE ^ 2 ≤ (2 * A) ^ 2 := pow_le_pow_left₀ hAE0 hAEA 2
    nlinarith only [hAEA, h2, hA0]
  have hN0 : 0 ≤ N := by positivity
  have hfinal : B ≤ 4 * (9 + 3 * Kp) * (A + A ^ 2) * N := by
    refine hBN.trans ?_
    have hc : 0 ≤ 9 + 3 * Kp := by positivity
    calc (9 + 3 * Kp) * (AE + AE ^ 2) * N ≤ (9 + 3 * Kp) * (4 * (A + A ^ 2)) * N := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAEA2 hc) hN0
      _ = 4 * (9 + 3 * Kp) * (A + A ^ 2) * N := by ring
  rw [hlhs]
  calc _ ≤ B * (t - s) ^ (2 / 5 : ℝ) := hmain
    _ ≤ 4 * (9 + 3 * Kp) * (A + A ^ 2) * N * (t - s) ^ (2 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hfinal hpow0

end CKN.Leray

end
