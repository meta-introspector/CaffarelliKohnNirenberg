-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.IsForcedLerayHopfSolution
public import CKN.Statements.ForcedQuadraticTensor
public import CKN.Leray.ForcedLerayLimitTenThirds
public import CKN.Leray.ForcedHopfSlab
public import CKN.Foundation.RellichBallsCore
public import CKN.Leray.Support.VorticityL2Tools

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The finite-time energy class of a forced Leray--Hopf solution gives the
space-time `L^(10/3)` bound used for its quadratic pressure. -/
theorem forcedAssociatedPressure_velocity_memLp_tenThirds
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    MemLp u (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  rcases hF with ⟨hT, -, -, huAEmeas, hDuAEmeas, hKineticTop,
    hJointTop, hWeakGradient, -, -, -, -, -⟩
  classical
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let ν : Measure ℝ := volume.restrict (Ioo 0 T)
  let uM : ParabolicPoint → Vec3 := huAEmeas.mk u
  let DuM : ParabolicPoint → Fin 3 → Vec3 := hDuAEmeas.mk Du
  have huM : Measurable uM := huAEmeas.measurable_mk
  have hDuM : Measurable DuM := hDuAEmeas.measurable_mk
  have huEq : u =ᵐ[volume.restrict Q] uM := huAEmeas.ae_eq_mk
  have hDuEq : Du =ᵐ[volume.restrict Q] DuM := hDuAEmeas.ae_eq_mk
  have hmeasure : (volume : Measure ParabolicPoint).restrict Q =
      (volume : Measure Vec3).prod ν := by
    rw [forcedHopf_slab_measure_eq_prod Set.univ (Ioo 0 T)]
    simp [ν, Measure.restrict_univ]
    rfl
  have huEqProd : u =ᵐ[(volume : Measure Vec3).prod ν] uM := by
    rw [← hmeasure]
    exact huEq
  have hDuEqProd : Du =ᵐ[(volume : Measure Vec3).prod ν] DuM := by
    rw [← hmeasure]
    exact hDuEq
  let E : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3, ‖uM (x, t)‖ₑ ^ (2 : ℝ)
  have hEmeas : Measurable E := by
    dsimp [E]
    exact (huM.enorm.pow_const (2 : ℝ)).lintegral_prod_left'
  have hUeqTime : ∀ᵐ t ∂ν, ∀ᵐ x ∂(volume : Measure Vec3),
      u (x, t) = uM (x, t) := by
    have hswap := (Measure.measurePreserving_swap (μ := ν)
      (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae huEqProd
    exact Measure.ae_ae_of_ae_prod hswap
  have hEeq : E =ᵐ[ν] fun t => ∫⁻ x : Vec3, ‖u (x, t)‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hUeqTime] with t ht
    apply lintegral_congr_ae
    filter_upwards [ht] with x hx
    rw [hx]
  have hEss : essSup E ν =
      essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)) ν :=
    essSup_congr_ae hEeq
  let B : ℝ≥0∞ := essSup E ν
  have hBtop : B < ⊤ := by
    simpa [B, hEss, ν] using hKineticTop
  have hEbound : ∀ᵐ t ∂ν, E t ≤ B := by
    change ∀ᵐ t ∂ν, E t ≤ essSup E ν
    exact ENNReal.ae_le_essSup E
  let good : Set ℝ := {t | t ∈ Ioo 0 T ∧ E t ≤ B}
  have hGoodMeas : MeasurableSet good := by
    dsimp [good]
    exact measurableSet_Ioo.inter (measurableSet_le hEmeas measurable_const)
  have hGoodAE : ∀ᵐ t ∂ν, t ∈ good := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hEbound] with t ht hE
    exact ⟨ht, hE⟩
  let v : ParabolicPoint → Vec3 := fun z => if z.2 ∈ good then uM z else 0
  let W : ParabolicPoint → Fin 3 → Vec3 := fun z => if z.2 ∈ good then DuM z else 0
  have hvMeas : Measurable v := by
    dsimp [v]
    exact Measurable.ite (measurable_snd hGoodMeas) huM measurable_const
  have hWMeas : Measurable W := by
    dsimp [W]
    exact Measurable.ite (measurable_snd hGoodMeas) hDuM measurable_const
  have hvEqProd : v =ᵐ[(volume : Measure Vec3).prod ν] uM := by
    have hgoodProd : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), z.2 ∈ good := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_snd hGoodMeas)).2
      filter_upwards [] with x
      exact hGoodAE
    filter_upwards [hgoodProd] with z hz
    simp [v, hz]
  have hWEqProd : W =ᵐ[(volume : Measure Vec3).prod ν] DuM := by
    have hgoodProd : ∀ᵐ z ∂((volume : Measure Vec3).prod ν), z.2 ∈ good := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_snd hGoodMeas)).2
      filter_upwards [] with x
      exact hGoodAE
    filter_upwards [hgoodProd] with z hz
    simp [W, hz]
  have hvEq : v =ᵐ[volume.restrict Q] u := by
    have h := hvEqProd.trans huEqProd.symm
    rw [← hmeasure] at h
    exact h
  have hWEq : W =ᵐ[volume.restrict Q] Du := by
    have h := hWEqProd.trans hDuEqProd.symm
    rw [← hmeasure] at h
    exact h
  have hDuSquare : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    exact lintegral_mono fun z => le_add_left le_rfl
  have hSpatialBound : (∫⁻ z in Q,
      ENNReal.ofReal (spatialGradientSq u Du z)) < ⊤ := by
    have hpoint (z : ParabolicPoint) :
        ENNReal.ofReal (spatialGradientSq u Du z) ≤
          9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
      have hreal : spatialGradientSq u Du z ≤ 9 * ‖Du z‖ ^ (2 : ℕ) := by
        unfold spatialGradientSq
        calc
          ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ (2 : ℕ) ≤
              ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du z‖ ^ (2 : ℕ) := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            have hcoord : |Du z i j| ≤ ‖Du z‖ := by
              exact (norm_le_pi_norm (Du z i) j).trans (norm_le_pi_norm (Du z) i)
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hcoord 2
          _ = 9 * ‖Du z‖ ^ (2 : ℕ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
      calc
        ENNReal.ofReal (spatialGradientSq u Du z) ≤
            ENNReal.ofReal (9 * ‖Du z‖ ^ (2 : ℕ)) := ENNReal.ofReal_le_ofReal hreal
        _ = 9 * ‖Du z‖ₑ ^ (2 : ℝ) := by
          rw [ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal (9 : ℝ) = 9 by norm_num,
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
          norm_num [ENNReal.rpow_natCast]
    have hle : (∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z)) ≤
        9 * (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) := by
      calc
        _ ≤ ∫⁻ z in Q, 9 * ‖Du z‖ₑ ^ (2 : ℝ) := lintegral_mono hpoint
        _ = 9 * (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) := by
          rw [lintegral_const_mul' _ _ (by norm_num)]
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (by norm_num) hDuSquare)
  have hSpatialEq : (∫⁻ z in Q,
      ENNReal.ofReal (spatialGradientSq v W z)) =
      ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq u Du z) := by
    apply lintegral_congr_ae
    filter_upwards [hWEq] with z hzW
    simp only [spatialGradientSq, hzW]
  let D : ℝ≥0∞ := ∫⁻ t in Ioo 0 T, ∫⁻ x : Vec3,
    ENNReal.ofReal (spatialGradientSq v W (x, t)) ∂volume
  have hDle : D ≤ ∫⁻ z in Q, ENNReal.ofReal (spatialGradientSq v W z) := by
    have hmeas : Measurable (fun z : ParabolicPoint =>
        ENNReal.ofReal (spatialGradientSq v W z)) := by
      apply ENNReal.measurable_ofReal.comp
      unfold spatialGradientSq
      fun_prop
    have hiter := (lintegral_slab_eq_prod
      (fun z : ParabolicPoint => ENNReal.ofReal (spatialGradientSq v W z))
      (Ioo 0 T)).trans (lintegral_prod_symm _ hmeas.aemeasurable)
    simpa [D, Q] using hiter.symm.le
  have hDfinite : D < ⊤ := by
    exact lt_of_le_of_lt hDle (by simpa [hSpatialEq] using hSpatialBound)
  have hgradSlices := CKN.Foundation.ae_memLp_two_spatial_gradient_slice_of_lintegral_lt_top
    (K := (Set.univ : Set Vec3)) (J := Ioo 0 T) v W hWMeas
    (by simpa [D] using hDfinite)
  have hWeakV : ∀ᵐ t ∂ν, ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => v (x, t) i) (fun x => W (x, t) i) := by
    have hUtime' : ∀ᵐ t ∂ν, ∀ᵐ x ∂(volume : Measure Vec3),
        v (x, t) = u (x, t) := by
      have hvEqOrig : v =ᵐ[(volume : Measure Vec3).prod ν] u :=
        hvEqProd.trans huEqProd.symm
      have hswap := (Measure.measurePreserving_swap (μ := ν)
        (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hvEqOrig
      exact Measure.ae_ae_of_ae_prod hswap
    have hWtime' : ∀ᵐ t ∂ν, ∀ᵐ x ∂(volume : Measure Vec3),
        W (x, t) = Du (x, t) := by
      have hWEqOrig : W =ᵐ[(volume : Measure Vec3).prod ν] Du :=
        hWEqProd.trans hDuEqProd.symm
      have hswap := (Measure.measurePreserving_swap (μ := ν)
        (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hWEqOrig
      exact Measure.ae_ae_of_ae_prod hswap
    filter_upwards [hWeakGradient, hUtime', hWtime'] with t hweak huT hWT i
    have hleft : (fun x : Vec3 => u (x, t) i) =ᵐ[volume]
        fun x => v (x, t) i := by
      filter_upwards [huT] with x hx
      exact congrArg (fun g : Vec3 => g i) hx.symm
    have hright : (fun x : Vec3 => Du (x, t) i) =ᵐ[volume]
        fun x => W (x, t) i := by
      filter_upwards [hWT] with x hx
      exact congrArg (fun g : Fin 3 → Vec3 => g i) hx.symm
    exact hasWeakGradientOn_congr_ae_right hright
      (hasWeakGradientOn_congr_ae_left hleft (hweak i))
  have hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => v (x, t)) 2 volume := by
    intro t ht
    by_cases hgood : t ∈ good
    · have hEt : E t ≤ B := hgood.2
      have hfinite : (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (uM (x, t))) ^ (2 : ℝ)) < ⊤ := by
        have hpoint (x : Vec3) :
            ENNReal.ofReal (vec3EuclideanNorm (uM (x, t))) ^ (2 : ℝ) ≤
              3 * ‖uM (x, t)‖ₑ ^ (2 : ℝ) := by
          exact vec3Euclidean_sq_le_three_enorm_sq (uM (x, t))
        calc
          _ ≤ 3 * E t := by
            calc
              _ ≤ ∫⁻ x : Vec3, 3 * ‖uM (x, t)‖ₑ ^ (2 : ℝ) := lintegral_mono hpoint
              _ = 3 * E t := by rw [lintegral_const_mul' _ _ (by norm_num)]
          _ ≤ 3 * B := mul_le_mul_of_nonneg_left hEt (by norm_num)
          _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hBtop
      have hsliceM : MemLp (fun x : Vec3 => uM (x, t)) 2 volume :=
        CKN.Foundation.memLp_two_vec3_raw_of_lintegral_sq_lt_top volume
          (fun x => uM (x, t)) (huM.comp measurable_prodMk_right)
          (by simpa using hfinite)
      have hvEqSlice : (fun x : Vec3 => v (x, t)) = fun x => uM (x, t) := by
        funext x
        simp [v, hgood]
      rw [hvEqSlice]
      exact hsliceM
    · have hvzero : (fun x : Vec3 => v (x, t)) = 0 := by
        funext x
        simp [v, hgood]
      rw [hvzero]
      exact MemLp.zero
  have hSliceBound : ∀ t ∈ Ioo 0 T, ∀ i : Fin 3,
      eLpNorm (fun x : Vec3 => v (x, t) i) 2 volume ≤ B ^ (1 / 2 : ℝ) := by
    intro t ht i
    by_cases hgood : t ∈ good
    · have hcomponent : MemLp (fun x : Vec3 => v (x, t) i) 2 volume :=
        (memLp_pi_iff.mp (hSlice t ht.1.le)) i
      have hLpIdentity : eLpNorm (fun x : Vec3 => v (x, t) i) 2 volume ^ (2 : ℝ) =
          ∫⁻ x : Vec3, ‖v (x, t) i‖ₑ ^ (2 : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
          hcomponent.aestronglyMeasurable, ENNReal.toReal_ofNat,
          ← ENNReal.rpow_mul]
        norm_num
      have hcomponentBound : (∫⁻ x : Vec3, ‖v (x, t) i‖ₑ ^ (2 : ℝ)) ≤ E t := by
        rw [show (fun x : Vec3 => ‖v (x, t) i‖ₑ ^ (2 : ℝ)) =
          fun x => ‖uM (x, t) i‖ₑ ^ (2 : ℝ) by
            funext x
            simp [v, hgood]]
        exact lintegral_mono fun x => by
          have hcoord : ‖uM (x, t) i‖ₑ ≤ ‖uM (x, t)‖ₑ :=
            by
              rw [← ofReal_norm, ← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm (uM (x, t)) i)
          exact ENNReal.rpow_le_rpow hcoord (by norm_num)
      have hnormSq : eLpNorm (fun x : Vec3 => v (x, t) i) 2 volume ^ (2 : ℝ) ≤
          B := hLpIdentity ▸ hcomponentBound.trans hgood.2
      have hroot : (eLpNorm (fun x : Vec3 => v (x, t) i) 2 volume ^
          (2 : ℝ)) ^ (1 / 2 : ℝ) = eLpNorm (fun x : Vec3 => v (x, t) i) 2 volume := by
        rw [← ENNReal.rpow_mul]
        norm_num
      rw [← hroot]
      exact ENNReal.rpow_le_rpow hnormSq (by norm_num)
    · have hvzero : (fun x : Vec3 => v (x, t) i) = 0 := by
        funext x
        simp [v, hgood]
      rw [hvzero, eLpNorm_zero]
      exact bot_le
  have hSlices : ∀ᵐ t ∂ν,
      ∃ hh : ∀ _i : Fin 3, H1Function (Set.univ : Set Vec3),
        (∀ i x, (hh i).toFun x = v (x, t) i) ∧
        (∀ i x j, (hh i).grad x j = W (x, t) i j) := by
    filter_upwards [hgradSlices, hWeakV, ae_restrict_mem measurableSet_Ioo]
      with t hDt hwt ht
    let hh : ∀ _i : Fin 3, H1Function (Set.univ : Set Vec3) := fun i => {
      toFun := fun x => v (x, t) i
      grad := fun x => W (x, t) i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (memLp_pi_iff.mp (hSlice t ht.1.le)) i
      gradMemL2 := by
        intro j
        simpa [CKN.GradMemLpOn, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDt) i)) j)
      hasWeakGradient := hwt i }
    exact ⟨hh, fun i x => rfl, fun i x j => rfl⟩
  have hGradientBound : D ≤ D := le_rfl
  have hBhalfTop : B ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBtop.ne
  have hten (i : Fin 3) := forcedLerayLimit_component_tenThirds_slab v W
    (B ^ (1 / 2 : ℝ)) D T hSlices hSliceBound hvMeas hWMeas
    hGradientBound hBhalfTop hDfinite i
  have hvLp : MemLp v (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) :=
    memLp_pi_iff.2 fun i => (hten i).1
  exact (memLp_congr_ae hvEq).1 hvLp

end CKN.Leray

end
