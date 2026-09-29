-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureCompactGradientCore
public import CKN.Statements.ForcedQuadraticTensor

/-!
# Forced nonlinear pressure cancellation

The canonical pressure of the forced quadratic tensor cancels the nonlinear
term on compact smooth scalar-gradient tests.
-/

@[expose] public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal
open scoped Convolution
open scoped Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The nonlinear and canonical pressure terms cancel on a compact smooth
scalar-gradient test for the forced quadratic tensor. -/
theorem forcedAssociatedPressureCompactGradient_nonlinearPressure_cancel
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure ParabolicPoint))
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ (Set.univ : Set Vec3) ×ˢ Ioo 0 T) :
    ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i *
          u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) +
        CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
          (CKN.forcedQuadraticTensor T u) hN z *
          rieszPressureJointLaplacian g z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let Q : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo 0 T
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F := CKN.forcedQuadraticTensor T u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := fun i j =>
    hN i j
  let p3 := rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hμ : μ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
    calc
      μ = ((volume : Measure Vec3).restrict Set.univ).prod
          (volume.restrict (Ioo 0 T)) := by simp [μ]
      _ = ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict Q := by
        rw [Measure.prod_restrict]
      _ = (volume : Measure (Vec3 × ℝ)).restrict Q := by
        rw [← Measure.volume_eq_prod Vec3 ℝ]
  have hdecay := associatedPressurePotentialDecay_of_compactSupport hg hgc
  have hDual := rieszPressureSpaceTime_noncompactPotential_duality
    F hF hg hdecay
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointLaplacian g) :=
    rieszPressureJointLaplacian_contDiff hg
  have hLapCompact : HasCompactSupport (rieszPressureJointLaplacian g) := by
    have hzero : ∀ z ∉ tsupport g,
        rieszPressureJointLaplacian g z = 0 := by
      intro z hz
      unfold rieszPressureJointLaplacian
      apply Finset.sum_eq_zero
      intro i hi
      rw [← rieszPressure_sliceMixedSecond_eq_joint hg i i z]
      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hz i i
    exact HasCompactSupport.intro hgc.isCompact (by
      intro z hz
      exact hzero z hz)
  have hLapMem : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    hLapSmooth.continuous.memLp_of_hasCompactSupport hLapCompact
  have hPMem : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    dsimp [p3, F, hF]
    exact rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u)
      (fun i j => hN i j)
  have hLapMu : MemLp (rieszPressureJointLaplacian g)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    rw [hμ]
    exact hLapMem.restrict Q
  have hPMu : MemLp p3 (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact hPMem.restrict Q
  have hFmu (i j : Fin 3) : MemLp (F i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [hμ]
    exact (hF i j).restrict Q
  have hHessSmooth (i j : Fin 3) :
      ContDiff ℝ (⊤ : ℕ∞) (rieszPressureJointHessian g i j) :=
    rieszPressureJointHessian_contDiff hg i j
  have hHessCompact (i j : Fin 3) :
      HasCompactSupport (rieszPressureJointHessian g i j) :=
    rieszPressureJointHessian_hasCompactSupport hgc i j
  have hHessMem (i j : Fin 3) : MemLp (rieszPressureJointHessian g i j)
      (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    (hHessSmooth i j).continuous.memLp_of_hasCompactSupport (hHessCompact i j)
  have hHessMu (i j : Fin 3) : MemLp (rieszPressureJointHessian g i j)
      (ENNReal.ofReal (3 : ℝ)) μ := by
    rw [hμ]
    exact (hHessMem i j).restrict Q
  let : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) 1 := by
    have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hFInt (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      F i j z * rieszPressureJointHessian g i j z) μ :=
    (hFmu i j).integrable_mul (hHessMu i j)
  have hConvAE (i j : Fin 3) :
      (fun z : Vec3 × ℝ =>
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) =ᵐ[μ]
      fun z => F i j z * rieszPressureJointHessian g i j z := by
    rw [hμ]
    filter_upwards [ae_restrict_mem hQmeas] with z hz
    have htime : z.2 ∈ Ioo 0 T := by simpa [Q] using hz
    have hzQ : z ∈ Q := by
      exact ⟨Set.mem_univ _, htime⟩
    have hmem : parabolicHomeomorph.symm z ∈
        spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
      change ((z.1, z.2) : ParabolicPoint) ∈
        (Set.univ : Set Vec3) ×ˢ Ioo 0 T
      exact ⟨Set.mem_univ _, htime⟩
    have hsecond : CKN.spatialSecondPartialProd g i j z =
        rieszPressureJointHessian g i j z := by
      change CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 = _
      have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
        hg.comp (contDiff_prodMk_left (𝕜 := ℝ)
          (n := (⊤ : ℕ∞)) z.2)
      calc
        CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 =
            CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) i j z.1 :=
          CKN.mixedSecond_swap hslice j i z.1
        _ = rieszPressureJointHessian g i j z :=
          rieszPressure_sliceMixedSecond_eq_joint hg i j z
    simp [CKN.forcedQuadraticTensor, F, htime, hsecond]
  have hConvInt (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
        CKN.spatialSecondPartialProd g i j z) μ :=
    (hFInt i j).congr (hConvAE i j).symm
  have hPressInt : Integrable (fun z : Vec3 × ℝ =>
      p3 z * rieszPressureJointLaplacian g z) μ := hPMu.integrable_mul hLapMu
  have hconvSumInt : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z) μ := by
    apply integrable_finsetSum (s := Finset.univ)
    intro i hi
    apply integrable_finsetSum (s := Finset.univ)
    intro j hj
    exact hConvInt i j
  have hconvSum : ∫ z : Vec3 × ℝ,
      ∑ i : Fin 3, ∑ j : Fin 3,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z ∂μ =
      ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂μ := by
    rw [integral_finsetSum _ (fun i hi => integrable_finsetSum _ (fun j hj => hConvInt i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum _ (fun j hj => hConvInt i j)]
  have hconvTerm (i j : Fin 3) :
      ∫ z : Vec3 × ℝ,
        u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
          CKN.spatialSecondPartialProd g i j z ∂μ =
        ∫ z : Vec3 × ℝ, F i j z *
          rieszPressureJointHessian g i j z ∂(volume : Measure (Vec3 × ℝ)) := by
    rw [hμ]
    calc
        ∫ z in Q,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂(volume : Measure (Vec3 × ℝ)) =
        ∫ z in Q, F i j z * rieszPressureJointHessian g i j z ∂volume := by
          apply setIntegral_congr_ae hQmeas
          filter_upwards [] with z hz
          have htime : z.2 ∈ Ioo 0 T := by simpa [Q] using hz
          have hzQ : z ∈ Q := ⟨Set.mem_univ _, htime⟩
          have hmem : parabolicHomeomorph.symm z ∈
              spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
            change ((z.1, z.2) : ParabolicPoint) ∈
              (Set.univ : Set Vec3) ×ˢ Ioo 0 T
            exact ⟨Set.mem_univ _, htime⟩
          have hsecond : CKN.spatialSecondPartialProd g i j z =
              rieszPressureJointHessian g i j z := by
            change CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 = _
            have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, z.2)) :=
              hg.comp (contDiff_prodMk_left (𝕜 := ℝ)
                (n := (⊤ : ℕ∞)) z.2)
            calc
              CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) j i z.1 =
                  CKN.mixedSecond (fun x : Vec3 => g (x, z.2)) i j z.1 :=
                CKN.mixedSecond_swap hslice j i z.1
              _ = rieszPressureJointHessian g i j z :=
                rieszPressure_sliceMixedSecond_eq_joint hg i j z
          simp [CKN.forcedQuadraticTensor, F, htime, hsecond]
      _ = ∫ z, F i j z * rieszPressureJointHessian g i j z ∂volume := by
        rw [← integral_indicator hQmeas]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ Q
        · simp [hz]
        · have hnotTime : z.2 ∉ Ioo 0 T := by simpa [Q] using hz
          simp [hz, CKN.forcedQuadraticTensor, F, hnotTime]
  have hpressGlobal :
      ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z
          ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
    calc
      ∫ z, p3 z * rieszPressureJointLaplacian g z ∂volume =
        ∫ z in Q, p3 z * rieszPressureJointLaplacian g z ∂volume := by
          calc
            _ = ∫ z, Q.indicator (fun z => p3 z *
                rieszPressureJointLaplacian g z) z ∂volume := by
                  apply integral_congr_ae
                  filter_upwards [] with z
                  by_cases hz : z ∈ Q
                  · simp [hz]
                  · have hnot : z ∉ tsupport g := fun hm => hz (hgsupp hm)
                    have hzero : rieszPressureJointLaplacian g z = 0 := by
                      unfold rieszPressureJointLaplacian
                      apply Finset.sum_eq_zero
                      intro i hi
                      rw [← rieszPressure_sliceMixedSecond_eq_joint hg i i z]
                      exact CKN.spatialSecondPartial_eq_zero_off_tsupport hnot i i
                    simp [hz, hzero]
            _ = _ := integral_indicator hQmeas
      _ = ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
          rw [← hμ]
  calc
    ∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z) +
          p3 z * rieszPressureJointLaplacian g z ∂μ =
      (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ,
          u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
            CKN.spatialSecondPartialProd g i j z ∂μ) +
        ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z ∂μ := by
          rw [integral_add hconvSumInt hPressInt, hconvSum]
    _ = (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z : Vec3 × ℝ, F i j z * rieszPressureJointHessian g i j z
          ∂(volume : Measure (Vec3 × ℝ))) +
        ∫ z : Vec3 × ℝ, p3 z * rieszPressureJointLaplacian g z
          ∂(volume : Measure (Vec3 × ℝ)) := by
          rw [hpressGlobal]
          apply congrArg₂ HAdd.hAdd
          · apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hconvTerm i j
          · rfl
    _ = 0 := by
      rw [hDual]
      ring

end CKN.Leray

end
