-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedPairings
public import CKN.Leray.AssocPressureMixedNorm
public import CKN.Leray.ForcedHopfSlab
public import CKN.Statements.IsForcedLerayHopfSolution

/-!
# Linear cancellation on compact gradient tests

The forced weak divergence and weak gradient identities cancel the time and
viscous terms when the test is a compact scalar gradient.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The forced joint-energy clause gives the product-coordinate `L²`
membership of velocity on the finite slab. -/
theorem forcedAssociatedPressure_velocity_memLp_two_productSlab
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  rcases hF with ⟨_, _, _, huMeas, _, _, hJointTop, -, -, -, -, -, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have huFinite : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    apply lintegral_mono
    intro z
    exact le_add_of_nonneg_right (by positivity)
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top huMeas huFinite
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q)) (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp := hu2.comp_measurePreserving hMapProd
  change MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 2
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' Q)) at hcomp
  have hset : parabolicHomeomorph.symm ⁻¹' Q =
      (Set.univ : Set Vec3) ×ˢ Ioo 0 T := by
    ext z
    change ((parabolicHomeomorph.symm z).1 ∈ (Set.univ : Set Vec3) ∧
      (parabolicHomeomorph.symm z).2 ∈ Ioo 0 T) ↔ z ∈ Set.univ ×ˢ Ioo 0 T
    simp
  rw [hset, ← Measure.prod_restrict] at hcomp
  simpa [μ] using hcomp

/-- The forced joint-energy clause gives the product-coordinate `L²`
membership of the weak gradient on the finite slab. -/
theorem forcedAssociatedPressure_gradient_memLp_two_productSlab
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  rcases hF with ⟨_, _, _, _, hDuMeas, _, hJointTop, -, -, -, -, -, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have hDuFinite : (∫⁻ z in Q, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    apply lintegral_mono
    intro z
    exact le_add_left le_rfl
  have hDu2 : MemLp Du 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top hDuMeas hDuFinite
  have hQmeas : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hMap : MeasurePreserving parabolicHomeomorph.symm
      (volume.restrict (parabolicHomeomorph.symm ⁻¹' Q))
      (volume.restrict Q) :=
    parabolicHomeomorphSymm_measurePreserving.restrict_preimage hQmeas
  have hMapProd : MeasurePreserving parabolicHomeomorph.symm
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (parabolicHomeomorph.symm ⁻¹' Q)) (volume.restrict Q) := by
    rw [← Measure.volume_eq_prod Vec3 ℝ]
    exact hMap
  have hcomp := hDu2.comp_measurePreserving hMapProd
  change MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
    (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
      (parabolicHomeomorph.symm ⁻¹' Q)) at hcomp
  have hset : parabolicHomeomorph.symm ⁻¹' Q =
      (Set.univ : Set Vec3) ×ˢ Ioo 0 T := by
    ext z
    change ((parabolicHomeomorph.symm z).1 ∈ (Set.univ : Set Vec3) ∧
      (parabolicHomeomorph.symm z).2 ∈ Ioo 0 T) ↔ z ∈ Set.univ ×ˢ Ioo 0 T
    simp
  rw [hset, ← Measure.prod_restrict] at hcomp
  simpa [μ] using hcomp

private theorem forcedAssociatedPressure_divergencePairing
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3,
          u (parabolicHomeomorph.symm (x, t)) i * ψ.partialDeriv i x = 0 := by
  rcases hF with ⟨_, _, _, _, _, _, _, _, hWeakDiv, _, _, _, _⟩
  filter_upwards [hWeakDiv] with t ht
  intro ψ
  simpa only [parabolicHomeomorph_symm_apply] using ht ψ

private theorem forcedAssociatedPressure_weakGradientSlices
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (parabolicHomeomorph.symm (x, t)) i)
        (fun x => Du (parabolicHomeomorph.symm (x, t)) i) := by
  rcases hF with ⟨_, _, _, _, _, _, _, hWeakGrad, _, _, _, _, _⟩
  filter_upwards [hWeakGrad] with t ht
  intro i
  simpa only [parabolicHomeomorph_symm_apply] using ht i

/-- The time and viscosity terms vanish on a compact smooth scalar gradient
by the forced weak-divergence and weak-gradient clauses. -/
theorem forcedAssociatedPressureCompactGradient_linear_cancel
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
          CKN.timePartialProd (CKN.spatialPartialProd g i) z)
        + ∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j *
            CKN.spatialSecondPartialProd g i j z)
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  have hU : MemLp uP 2 μ := by
    simpa [uP, μ] using forcedAssociatedPressure_velocity_memLp_two_productSlab hF
  have hDu : MemLp DuP 2 μ := by
    simpa [DuP, μ] using forcedAssociatedPressure_gradient_memLp_two_productSlab hF
  have hdiv := forcedAssociatedPressure_divergencePairing hF
  have hweak := forcedAssociatedPressure_weakGradientSlices hF
  have htime : ContDiff ℝ (⊤ : ℕ∞) (CKN.timePartialProd g) :=
    CKN.contDiff_timePartial hg
  have htimec : HasCompactSupport (CKN.timePartialProd g) :=
    CKN.hasCompactSupport_timePartial hgc
  have hTimeZero := forcedField_pairing_scalarGradient_zero hU hdiv
    htime htimec
  have hTimeComm (z : Vec3 × ℝ) (i : Fin 3) :
      CKN.timePartialProd (CKN.spatialPartialProd g i) z =
        CKN.spatialPartialProd (CKN.timePartialProd g) i z :=
    associatedPressureTimeSpatialPartialProd_commute hg i z
  have hTimeIntegrable : Integrable
      (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, uP z i * CKN.timePartialProd
          (CKN.spatialPartialProd g i) z) μ := by
    have hSum : Integrable (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, uP z i * CKN.spatialPartialProd
          (CKN.timePartialProd g) i z) μ := by
      have hDerivative (i : Fin 3) : MemLp
          (CKN.spatialPartialProd (CKN.timePartialProd g) i) 2 μ := by
        exact associatedPressureCompact_memLp_two (T := T)
          (CKN.spatialPartial_contDiff htime i)
          (CKN.hasCompactSupport_spatialPartial htimec i)
      apply integrable_finsetSum
      intro i hi
      exact memLp_one_iff_integrable.mp
        (((memLp_pi_iff.mp hU) i).mul (hDerivative i))
    have hAE : (fun z : Vec3 × ℝ =>
        ∑ i : Fin 3, uP z i * CKN.timePartialProd
          (CKN.spatialPartialProd g i) z) =ᵐ[μ]
        fun z => ∑ i : Fin 3, uP z i * CKN.spatialPartialProd
          (CKN.timePartialProd g) i z := by
      filter_upwards [] with z
      apply Finset.sum_congr rfl
      intro i hi
      rw [hTimeComm z i]
    exact hSum.congr hAE.symm
  have hTimeIntegral : ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, uP z i * CKN.timePartialProd
        (CKN.spatialPartialProd g i) z) ∂μ = 0 := by
    calc
      _ = ∫ z : Vec3 × ℝ,
          ∑ i : Fin 3, uP z i * CKN.spatialPartialProd
            (CKN.timePartialProd g) i z ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with z
          apply Finset.sum_congr rfl
          intro i hi
          rw [hTimeComm z i]
      _ = 0 := hTimeZero
  have hHsmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialSecondPartialProd g i j) :=
    CKN.spatialPartial_contDiff (CKN.spatialPartial_contDiff hg i) j
  have hHcompact (i j : Fin 3) : HasCompactSupport
      (CKN.spatialSecondPartialProd g i j) :=
    CKN.hasCompactSupport_spatialPartial
      (CKN.hasCompactSupport_spatialPartial hgc i) j
  have hThirdsmooth (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) :=
    CKN.spatialPartial_contDiff (hHsmooth i j) j
  have hThirdcompact (i j : Fin 3) : HasCompactSupport
      (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) :=
    CKN.hasCompactSupport_spatialPartial (hHcompact i j) j
  have hVterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      DuP z i j * CKN.spatialSecondPartialProd g i j z) μ := by
    have hDuij : MemLp (fun z : Vec3 × ℝ => DuP z i j) 2 μ :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    have hH : MemLp (CKN.spatialSecondPartialProd g i j) 2 μ :=
      associatedPressureCompact_memLp_two (T := T) (hHsmooth i j) (hHcompact i j)
    exact memLp_one_iff_integrable.mp (hDuij.mul hH)
  have hNterm (i j : Fin 3) : Integrable (fun z : Vec3 × ℝ =>
      uP z i * CKN.spatialPartialProd
        (CKN.spatialSecondPartialProd g i j) j z) μ := by
    have hui : MemLp (fun z : Vec3 × ℝ => uP z i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    have hT : MemLp
        (CKN.spatialPartialProd (CKN.spatialSecondPartialProd g i j) j) 2 μ :=
      associatedPressureCompact_memLp_two (T := T)
        (hThirdsmooth i j) (hThirdcompact i j)
    exact memLp_one_iff_integrable.mp (hui.mul hT)
  have hVsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        DuP z i j * CKN.spatialSecondPartialProd g i j z) μ := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hVterm i j
  have hNsum : Integrable (fun z : Vec3 × ℝ =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g i j) j z) μ := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hNterm i j
  have hPair (i j : Fin 3) :
      ∫ z : Vec3 × ℝ, DuP z i j * CKN.spatialSecondPartialProd g i j z ∂μ =
        -∫ z : Vec3 × ℝ, uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g i j) j z ∂μ := by
    exact forcedWeakGradient_pairing hU hDu hweak
      (hHsmooth i j) (hHcompact i j) i j
  have hVIntegral : ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3,
        DuP z i j * CKN.spatialSecondPartialProd g i j z) ∂μ =
      -∫ z : Vec3 × ℝ,
        (∑ i : Fin 3, ∑ j : Fin 3,
          uP z i * CKN.spatialPartialProd
            (CKN.spatialSecondPartialProd g i j) j z) ∂μ := by
    have hInner (i : Fin 3) :
        ∫ z : Vec3 × ℝ, ∑ j : Fin 3,
          DuP z i j * CKN.spatialSecondPartialProd g i j z ∂μ =
        -∫ z : Vec3 × ℝ, ∑ j : Fin 3,
          uP z i * CKN.spatialPartialProd
            (CKN.spatialSecondPartialProd g i j) j z ∂μ := by
      rw [integral_finsetSum _ (fun j hj => hVterm i j)]
      rw [integral_finsetSum _ (fun j hj => hNterm i j)]
      simp_rw [hPair i]
      rw [Finset.sum_neg_distrib]
    rw [integral_finsetSum _ (fun i hi =>
      integrable_finsetSum _ (fun j hj => hVterm i j))]
    rw [integral_finsetSum _ (fun i hi =>
      integrable_finsetSum _ (fun j hj => hNterm i j))]
    calc
      _ = ∑ i : Fin 3, -(∫ z : Vec3 × ℝ, ∑ j : Fin 3,
          uP z i * CKN.spatialPartialProd
            (CKN.spatialSecondPartialProd g i j) j z ∂μ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hInner i
      _ = _ := by rw [Finset.sum_neg_distrib]
  have hNzero (j : Fin 3) :
      ∫ z : Vec3 × ℝ,
        ∑ i : Fin 3, uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g j j) i z ∂μ = 0 := by
    exact forcedField_pairing_scalarGradient_zero hU hdiv
      (hHsmooth j j) (hHcompact j j)
  have hNreindex (z : Vec3 × ℝ) :
      (∑ i : Fin 3, ∑ j : Fin 3,
        uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g i j) j z) =
      ∑ j : Fin 3, ∑ i : Fin 3,
        uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g j j) i z := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    rw [associatedPressureSpatialTriple_commute hg i j z]
  have hNzeroAll : ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3,
        uP z i * CKN.spatialPartialProd
          (CKN.spatialSecondPartialProd g i j) j z) ∂μ = 0 := by
    calc
      _ = ∑ j : Fin 3, ∫ z : Vec3 × ℝ,
          ∑ i : Fin 3, uP z i * CKN.spatialPartialProd
            (CKN.spatialSecondPartialProd g j j) i z ∂μ := by
        rw [show (fun z : Vec3 × ℝ =>
          ∑ i : Fin 3, ∑ j : Fin 3,
            uP z i * CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g i j) j z) =
          (fun z => ∑ j : Fin 3, ∑ i : Fin 3,
            uP z i * CKN.spatialPartialProd
              (CKN.spatialSecondPartialProd g j j) i z) from funext hNreindex]
        exact integral_finsetSum _ (fun j hj =>
          integrable_finsetSum _ (fun i hi => by
            have hterm := hNterm i j
            apply hterm.congr
            filter_upwards [] with z
            rw [associatedPressureSpatialTriple_commute hg i j z]))
      _ = 0 := by simp [hNzero]
  have hViscIntegral : ∫ z : Vec3 × ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3,
        DuP z i j * CKN.spatialSecondPartialProd g i j z) ∂μ = 0 := by
    rw [hVIntegral, hNzeroAll]
    simp
  have hsumIntegrable : Integrable (fun z : Vec3 × ℝ =>
      -(∑ i : Fin 3, uP z i * CKN.timePartialProd
          (CKN.spatialPartialProd g i) z)
        + ∑ i : Fin 3, ∑ j : Fin 3,
          DuP z i j * CKN.spatialSecondPartialProd g i j z) μ := by
    exact hTimeIntegrable.neg.add hVsum
  have hresult : ∫ z : Vec3 × ℝ,
      (-(∑ i : Fin 3, uP z i * CKN.timePartialProd
          (CKN.spatialPartialProd g i) z)
        + ∑ i : Fin 3, ∑ j : Fin 3,
          DuP z i j * CKN.spatialSecondPartialProd g i j z) ∂μ = 0 := by
    calc
      _ = (∫ z : Vec3 × ℝ,
          -(∑ i : Fin 3, uP z i * CKN.timePartialProd
            (CKN.spatialPartialProd g i) z) ∂μ) +
          ∫ z : Vec3 × ℝ, ∑ i : Fin 3, ∑ j : Fin 3,
            DuP z i j * CKN.spatialSecondPartialProd g i j z ∂μ :=
        integral_add hTimeIntegrable.neg hVsum
      _ = 0 := by rw [integral_neg, hTimeIntegral, hViscIntegral]; simp
  simpa [uP, DuP, μ] using hresult

end CKN.Leray

end
