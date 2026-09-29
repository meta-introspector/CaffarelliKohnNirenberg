-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedGradientCore
public import CKN.Leray.AssocPressureForcedNonlinearPressure
public import CKN.Leray.AssocPressureForcedPressure

/-!
# Full cancellation on compact scalar-gradient tests

The forced weak identities cancel the linear terms, and the canonical Riesz
pressure cancels the quadratic terms.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

private theorem forcedAssociatedPressureCompactDerivative_memLp
    {T r : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    MemLp g (ENNReal.ofReal r)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  have hglobal : MemLp g (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    hg.continuous.memLp_of_hasCompactSupport hgc
  have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa using hrestrict

/-- The complete forced Leray momentum expression vanishes on the gradient of
a compact smooth scalar potential for the canonical Riesz pressure. -/
theorem forcedAssociatedPressureCompactGradient_momentum_zero
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du)
    (hN5 : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint))
    (hN3 : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure ParabolicPoint))
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T) :
    ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd g i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i *
            u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z
        - CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (CKN.forcedQuadraticTensor T u) hN5 z *
            rieszPressureJointLaplacian g z)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let Q : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  let p5 : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN5
  let p3 : Vec3 × ℝ → ℝ :=
    CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN3
  let L : Vec3 × ℝ → ℝ := fun z =>
    -(∑ i : Fin 3, uP z i * CKN.timePartialProd
        (CKN.spatialPartialProd g i) z)
      + ∑ i : Fin 3, ∑ j : Fin 3,
        DuP z i j * CKN.spatialSecondPartialProd g i j z
  let N5 : Vec3 × ℝ → ℝ := fun z =>
    (∑ i : Fin 3, ∑ j : Fin 3,
      uP z i * uP z j * CKN.spatialSecondPartialProd g i j z)
      + p5 z * rieszPressureJointLaplacian g z
  have hQmeas : MeasurableSet Q :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hμ : μ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
    calc
      μ = ((volume : Measure Vec3).restrict Set.univ).prod
          (volume.restrict (Ioo 0 T)) := by simp [μ]
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict Q := by
        rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
  let forcedGradientCancelHolder22 : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  let forcedGradientCancelHolderPressure : ENNReal.HolderTriple
      (ENNReal.ofReal (5 / 3 : ℝ)) (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : Real.HolderTriple (5 / 3 : ℝ) (5 / 2 : ℝ) 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hU : MemLp uP 2 μ := by
    simpa [uP, μ] using forcedAssociatedPressure_velocity_memLp_two_productSlab hF
  have hDu : MemLp DuP 2 μ := by
    simpa [DuP, μ] using forcedAssociatedPressure_gradient_memLp_two_productSlab hF
  have hLinear : ∫ z : Vec3 × ℝ, L z ∂μ = 0 := by
    simpa [L, uP, DuP, μ] using
      forcedAssociatedPressureCompactGradient_linear_cancel hF hg hgc
  have hTimeIntegrable (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => uP z i *
        CKN.timePartialProd (CKN.spatialPartialProd g i) z) μ := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞)
        (CKN.timePartialProd (CKN.spatialPartialProd g i)) :=
      CKN.contDiff_timePartial (CKN.spatialPartial_contDiff hg i)
    have hsc : HasCompactSupport
        (CKN.timePartialProd (CKN.spatialPartialProd g i)) :=
      CKN.hasCompactSupport_timePartial
        (CKN.hasCompactSupport_spatialPartial hgc i)
    have hderivative : MemLp
        (CKN.timePartialProd (CKN.spatialPartialProd g i)) 2 μ :=
      by
        simpa [μ] using
          forcedAssociatedPressureCompactDerivative_memLp (r := 2) hsm hsc
    have hui : MemLp (fun z : Vec3 × ℝ => uP z i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    change Integrable ((fun z : Vec3 × ℝ => uP z i) *
      CKN.timePartialProd (CKN.spatialPartialProd g i)) μ
    exact memLp_one_iff_integrable.mp (hui.mul hderivative)
  have hHessianSmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialSecondPartialProd g i j) :=
    CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hg i) j
  have hHessianCompact (i j : Fin 3) : HasCompactSupport
      (CKN.spatialSecondPartialProd g i j) :=
    CKN.hasCompactSupport_spatialPartial
      (CKN.hasCompactSupport_spatialPartial hgc i) j
  have hViscIntegrable (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => DuP z i j *
        CKN.spatialSecondPartialProd g i j z) μ := by
    have hHij : MemLp (CKN.spatialSecondPartialProd g i j) 2 μ :=
      by
        simpa [μ] using forcedAssociatedPressureCompactDerivative_memLp
          (r := 2) (hHessianSmooth i j) (hHessianCompact i j)
    have hDuij : MemLp (fun z : Vec3 × ℝ => DuP z i j) 2 μ :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    change Integrable ((fun z : Vec3 × ℝ => DuP z i j) *
      CKN.spatialSecondPartialProd g i j) μ
    exact memLp_one_iff_integrable.mp (hDuij.mul hHij)
  have hLIntegrable : Integrable L μ := by
    apply Integrable.add
    · exact (integrable_finsetSum _ (fun i hi => hTimeIntegrable i)).neg
    · apply integrable_finsetSum
      intro i hi
      apply integrable_finsetSum
      intro j hj
      exact hViscIntegrable i j
  have hTensor (i j : Fin 3) : MemLp
      (fun z : Vec3 × ℝ => uP z i * uP z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    have hglobal := forcedAssociatedPressure_tensor_memLp_fiveThirds hF i j
    have hrestrict := hglobal.restrict Q
    have hEq : CKN.forcedQuadraticTensor T u i j =ᵐ[
        (volume : Measure (Vec3 × ℝ)).restrict Q]
        (fun z : Vec3 × ℝ => uP z i * uP z j) := by
      filter_upwards [ae_restrict_mem hQmeas] with z hz
      have hzt : z.2 ∈ Ioo 0 T := hz.2
      simp [CKN.forcedQuadraticTensor, uP, hzt,
        parabolicHomeomorph_symm_apply]
    have hresult := (memLp_congr_ae hEq).1 hrestrict
    simpa [hμ] using hresult
  have hp5 : MemLp p5 (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    have hglobal := rieszPressureSpaceTime_memLp (5 / 3 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN5
    have hrestrict := hglobal.restrict Q
    rw [hμ]
    exact hrestrict
  have hHessian52 (i j : Fin 3) : MemLp
    (CKN.spatialSecondPartialProd g i j)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ :=
    by
      simpa [μ] using forcedAssociatedPressureCompactDerivative_memLp
        (r := 5 / 2) (hHessianSmooth i j) (hHessianCompact i j)
  have hConvIntegrable (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => uP z i * uP z j *
        CKN.spatialSecondPartialProd g i j z) μ := by
    have hprod : MemLp
        ((fun z : Vec3 × ℝ => uP z i * uP z j) *
          CKN.spatialSecondPartialProd g i j)
        1 μ := (hTensor i j).mul (hHessian52 i j)
    change Integrable
      ((fun z : Vec3 × ℝ => uP z i * uP z j) *
        CKN.spatialSecondPartialProd g i j) μ
    exact memLp_one_iff_integrable.mp hprod
  have hConvSumIntegrable : Integrable
      (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          uP z i * uP z j * CKN.spatialSecondPartialProd g i j z) μ := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hConvIntegrable i j
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressureJointLaplacian g) := rieszPressureJointLaplacian_contDiff hg
  have hLapCompact : HasCompactSupport
      (rieszPressureJointLaplacian g) :=
    rieszPressureJointLaplacian_hasCompactSupport hgc
  have hLap52 : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ :=
    forcedAssociatedPressureCompactDerivative_memLp hLapSmooth hLapCompact
  have hPressureIntegrable : Integrable
      (fun z : Vec3 × ℝ => p5 z * rieszPressureJointLaplacian g z) μ := by
    change Integrable (p5 * rieszPressureJointLaplacian g) μ
    exact memLp_one_iff_integrable.mp (hp5.mul hLap52)
  have hNIntegrable : Integrable N5 μ := by
    change Integrable
      ((fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, ∑ j : Fin 3,
          uP z i * uP z j * CKN.spatialSecondPartialProd g i j z) +
        p5 * rieszPressureJointLaplacian g) μ
    exact hConvSumIntegrable.add hPressureIntegrable
  have hp3Mem : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    have hglobal := rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN3
    have hrestrict := hglobal.restrict Q
    rw [← hμ] at hrestrict
    exact hrestrict
  have hpAEGlobal := forcedAssociatedPressure_rieszPressure_exponents_ae_eq hN5 hN3
  have hpAE : p5 =ᵐ[μ] p3 := by
    rw [hμ]
    exact ae_restrict_of_ae hpAEGlobal
  have hN3zero := forcedAssociatedPressureCompactGradient_nonlinearPressure_cancel
    hN3 hg hgc hgsupp
  have hN5zero : ∫ z : Vec3 × ℝ,
      ((∑ i : Fin 3, ∑ j : Fin 3,
        uP z i * uP z j * CKN.spatialSecondPartialProd g i j z)
        + p5 z * rieszPressureJointLaplacian g z) ∂μ = 0 := by
    calc
      _ = ∫ z : Vec3 × ℝ,
          ((∑ i : Fin 3, ∑ j : Fin 3,
            uP z i * uP z j * CKN.spatialSecondPartialProd g i j z)
            + p3 z * rieszPressureJointLaplacian g z) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpAE] with z hpz
          rw [hpz]
      _ = 0 := by simpa [uP, μ, p3] using hN3zero
  have hTargetEq (z : Vec3 × ℝ) :
      (-(∑ i : Fin 3, uP z i * CKN.timePartialProd
          (CKN.spatialPartialProd g i) z)
        - ∑ i : Fin 3, ∑ j : Fin 3,
          uP z i * uP z j * CKN.spatialSecondPartialProd g i j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
          DuP z i j * CKN.spatialSecondPartialProd g i j z
        - p5 z * rieszPressureJointLaplacian g z) = L z - N5 z := by
    simp [L, N5]
    ring
  calc
    _ = ∫ z : Vec3 × ℝ, L z - N5 z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hTargetEq z
    _ = (∫ z : Vec3 × ℝ, L z ∂μ) -
        ∫ z : Vec3 × ℝ, N5 z ∂μ := integral_sub hLIntegrable hNIntegrable
    _ = 0 := by rw [hLinear, hN5zero]; simp

end CKN.Leray

end
