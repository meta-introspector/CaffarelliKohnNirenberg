-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegContractBoundsPressure

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


local instance regContractThreeHalvesLpFact :
    Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by norm_num⟩

/-- The regularized energy identity bounds both the velocity and its
mollified transport field in spatial `L²` on every time slice. -/
private theorem regContract_slice_vecNorm_bound
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (u : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3)
    (hA : MemLp (regUniformSpatialField a) 2 volume)
    (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hEnergy : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
        2 volume ^ (2 : ℕ))
    (t : ℝ) (ht : 0 ≤ t) :
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume ∧
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume := by
  let V : L2Vec3 → L2Vec3 := regUniformVelocitySlice u t
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  have hVmem : MemLp V 2 volume := by
    have hcoord := (hSlice t ht).comp_measurePreserving
      (PiLp.volume_preserving_ofLp (Fin 3))
    have hL2 := hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp V 2 volume
    exact hL2
  have hMollA := regMollifyVector_eLpNorm_two_le ρ ε hε hA
  have hEnergyBound : eLpNorm V 2 volume ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := by
    calc
      eLpNorm V 2 volume ^ (2 : ℕ) ≤
          eLpNorm V 2 volume ^ (2 : ℕ) +
            2 * regUniformDissipation u D t := le_add_right le_rfl
      _ = eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ) := hEnergy t ht
      _ ≤ A ^ (2 : ℕ) := by
        exact pow_le_pow_left₀ (by positivity) hMollA (2 : ℕ)
  have hVbound : eLpNorm V 2 volume ≤ A := by
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
    simpa [A] using hEnergyBound
  have hVcomp := hVmem.aestronglyMeasurable.comp_measurePreserving
    vec3ToL2Vec3_measurePreserving
  have hUeq : eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume =
      eLpNorm V 2 volume := by
    calc
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) 2 volume =
          eLpNorm (fun x : Vec3 => ‖V (WithLp.toLp 2 x)‖) 2 volume := by
        apply eLpNorm_congr_ae
        filter_upwards [] with x
        simp [V, regUniformVelocitySlice, vec3EuclideanNorm_eq_l2]
      _ = eLpNorm (fun x : Vec3 => V (WithLp.toLp 2 x)) 2 volume :=
        eLpNorm_norm _ hVcomp
      _ = eLpNorm V 2 volume :=
        eLpNorm_comp_measurePreserving hVmem.aestronglyMeasurable
          vec3ToL2Vec3_measurePreserving
  let W : L2Vec3 → L2Vec3 := regMollifyVector ρ ε hε V
  have hWmeas : AEStronglyMeasurable W volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hVmem
  have hWbound : eLpNorm W 2 volume ≤ A := by
    calc
      eLpNorm W 2 volume ≤ eLpNorm V 2 volume :=
        regMollifyVector_eLpNorm_two_le ρ ε hε hVmem
      _ ≤ A := hVbound
  have hWcomp := hWmeas.comp_measurePreserving
    vec3ToL2Vec3_measurePreserving
  have hJeq : eLpNorm (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume =
      eLpNorm W 2 volume := by
    calc
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u (x, t))) 2 volume =
          eLpNorm (fun x : Vec3 => ‖W (WithLp.toLp 2 x)‖) 2 volume := by
        apply eLpNorm_congr_ae
        filter_upwards [] with x
        simp [W, regUniformMollifiedVelocity, V,
          vec3EuclideanNorm_eq_l2]
      _ = eLpNorm (fun x : Vec3 => W (WithLp.toLp 2 x)) 2 volume :=
        eLpNorm_norm _ hWcomp
      _ = eLpNorm W 2 volume :=
        eLpNorm_comp_measurePreserving hWmeas vec3ToL2Vec3_measurePreserving
  exact ⟨by rw [hUeq]; exact hVbound, by rw [hJeq]; exact hWbound⟩

private theorem regContract_pressure_ae_eq_truncatedSpaceTimeRiesz
    (T r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (p : Vec3 × ℝ → ℝ) (hpMeas : Measurable p)
    (hR4 : ∀ t : ℝ, 0 < t → t < T → ∃ hF2 : ∀ i j,
      MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal 2)
        (volume : Measure Vec3),
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative 2 (by norm_num)
          (fun i j => (hF2 i j).toLp
            (fun x : Vec3 => F i j (x, t)))) :
    (fun z : Vec3 × ℝ => p z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) T)]
      rieszPressureSpaceTime r hr F hF := by
  let μt : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T)
  have hSlabMeasure :
      ((volume : Measure (Vec3 × ℝ)).restrict
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) T)) =
      (volume : Measure Vec3).prod μt := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Set.Ioo (0 : ℝ) T)]
    simp [μt, Measure.restrict_univ]
  have hSlices := rieszPressureSpaceTime_slice_ae_eq r hr F hF
  have hSliceEq : ∀ᵐ t ∂μt,
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        fun x => rieszPressureSpaceTime r hr F hF (x, t) := by
    filter_upwards [ae_restrict_of_ae hSlices,
      ae_restrict_mem measurableSet_Ioo] with t ht htime
    rcases ht with ⟨hFrt, hSpaceTimePressure⟩
    obtain ⟨hF2t, hR4t⟩ := hR4 t htime.1 htime.2
    let F2 : PressureTensorLp 2 := fun i j =>
      (hF2t i j).toLp (fun x : Vec3 => F i j (x, t))
    have hRepresentative := rieszPressureSliceRepresentative_ae_eq
      2 (by norm_num) F2
    have hCommon := rieszPressureSlice_ae_eq_of_memLp_common
      r hr 2 (by norm_num) (fun i j x => F i j (x, t)) hFrt hF2t
    have hPtoSlice2 : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (rieszPressureSlice 2 (by norm_num) F2 : Vec3 → ℝ) := by
      exact hR4t.trans hRepresentative.symm
    have hPtoSliceR : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (rieszPressureSlice r hr
          (fun i j => (hFrt i j).toLp (fun x : Vec3 => F i j (x, t))) :
            Vec3 → ℝ) := hPtoSlice2.trans hCommon.symm
    exact hPtoSliceR.trans hSpaceTimePressure.symm
  let S : Set (Vec3 × ℝ) :=
    {z | p z = rieszPressureSpaceTime r hr F hF z}
  have hSmeas : MeasurableSet S :=
    measurableSet_eq_fun hpMeas (rieszPressureSpaceTime_measurable r hr F hF)
  have hSswap : MeasurableSet
      {z : ℝ × Vec3 | p (z.2, z.1) =
        rieszPressureSpaceTime r hr F hF (z.2, z.1)} := by
    change MeasurableSet (Prod.swap ⁻¹' S)
    exact measurableSet_swap_iff.mpr hSmeas
  have hSections : ∀ᵐ t ∂μt, ∀ᵐ x : Vec3 ∂volume,
      p (x, t) = rieszPressureSpaceTime r hr F hF (x, t) := hSliceEq
  have hSectionsSwap : ∀ᵐ x : Vec3 ∂volume, ∀ᵐ t ∂μt,
      p (x, t) = rieszPressureSpaceTime r hr F hF (x, t) :=
    (Measure.ae_ae_comm hSswap).mp hSections
  have hProduct : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod μt),
      z ∈ S := (Measure.ae_prod_iff_ae_ae hSmeas).2 hSectionsSwap
  rw [hSlabMeasure]
  filter_upwards [hProduct] with z hz
  exact hz

/-- The actual regularized pressure obeys the finite-slab `L^(3/2)` estimate
in `lem:reg-pressure-bound`. -/
theorem regContract_regPressure_slab_threeHalves
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (T : ℝ) (hT : 0 < T) :
    ∃ hp : MemLp (pε a ha ε) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))),
      lpNorm (pε a ha ε) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤
        9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          ((T * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2) ^
              (1 / 6 : ℝ) *
            ((6 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
              eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2) ^
              (5 / 6 : ℝ)) := by
  classical
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let p : ParabolicPoint → ℝ := pε a ha ε
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => u y i) j z
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi (0 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict P
  let S : Set (Vec3 × ℝ) := Set.univ ×ˢ Ioo (0 : ℝ) T
  let μt : Measure ℝ := volume.restrict (Ioo 0 T)
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let K : ℝ≥0∞ := CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  let C : ℝ≥0∞ := 6 * K * A
  let B : ℝ := C.toReal
  let Areal : ℝ := A.toReal ^ 2
  let Mreal : ℝ := B ^ 2
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitialAE, _hWeakDivFree⟩,
      hUcont, _hDcont, _hDDcont, _hDtcont, hPcont, _hDpcont,
      hUcontDiff, _hDdiff, _hPdiff, _hBounds, _hLocalLp,
      _hEquation, hPressure, hEnergy⟩
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hSmeas : MeasurableSet S := by
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  let Ubar : ParabolicPoint → Vec3 := P.piecewise u (fun _ => 0)
  let pbar : ParabolicPoint → ℝ := P.piecewise p (fun _ => 0)
  have hUcontinuous : ContinuousOn u P := by
    apply continuousOn_pi.mpr
    intro i
    simpa [u, P] using hUcont i
  have hpcontinuous : ContinuousOn p P := by
    simpa [p, P] using hPcont
  have hUbarMeas : Measurable Ubar :=
    lerayLimit_measurableOn_extension P hPmeas u (fun _ => 0)
      hUcontinuous continuousOn_const
  have hpbarMeas : Measurable pbar :=
    lerayLimit_measurableOn_extension P hPmeas p (fun _ => 0)
      hpcontinuous continuousOn_const
  have hUbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) : Ubar (x, t) = u (x, t) := by
    change P.piecewise u (fun _ => 0) (x, t) = u (x, t)
    rw [Set.piecewise_eq_of_mem P u (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hpbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) : pbar (x, t) = p (x, t) := by
    change P.piecewise p (fun _ => 0) (x, t) = p (x, t)
    rw [Set.piecewise_eq_of_mem P p (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hBoth := regContract_regTenThirds
    (ρ := ρ) (uε := uε) (pε := pε) (hregularised := hregularised)
    a ha ε hε
  have hUVector : eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
      (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ C := by
    calc
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
          (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
        eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z))
          (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure := by
            simp [u, μ, P, regUniformPositiveTimeMeasure]
      _ ≤ C := by simpa [C, K, A] using le_trans (le_add_right le_rfl) hBoth
  have hJVector : eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u z))
      (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ C := by
    calc
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u z))
          (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
        eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm
          (regUniformMollifiedVelocity ρ ε hε u z))
          (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure := by
            simp [u, μ, P, regUniformPositiveTimeMeasure]
      _ ≤ C := by simpa [C, K, A] using le_trans (le_add_left le_rfl) hBoth
  have hUbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (u z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hUbarPos x t hz.2)
  have hUbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ ≤ C := by
    rw [eLpNorm_congr_ae hUbarRawEq]
    simpa [q, u, μ, P, C, K, A, regUniformPositiveTimeMeasure] using hUVector
  let : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
  let : NormedAddCommGroup ParabolicPoint :=
    inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
  let : NormedSpace ℝ ParabolicPoint :=
    inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
  let : OpensMeasurableSpace ParabolicPoint := by
    change OpensMeasurableSpace (Vec3 × ℝ)
    let : SecondCountableTopologyEither Vec3 ℝ := ⟨Or.inl inferInstance⟩
    exact Prod.opensMeasurableSpace
  let J : ParabolicPoint → Vec3 := regUniformMollifiedVelocity ρ ε hε u
  have hJcontinuousComp : ∀ i : Fin 3, ContinuousOn (fun z => J z i) P := by
    have hJcont := regUniform_mollified_velocity_continuousOn ρ ε hε
      (S := P) (fun t ht => hSlice t (le_of_lt ht)) hUcontDiff
      (by intro z hz; exact hz.2)
      (by
        intro z hz y
        change z.1 - y ∈ Set.univ ∧ 0 < z.2
        exact ⟨Set.mem_univ _, hz.2⟩)
    intro i
    change ContinuousOn
      (fun z : Vec3 × ℝ =>
        regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i)
      (Set.univ ×ˢ Ioi (0 : ℝ))
    exact hJcont i
  have hJcontinuous : ContinuousOn J P := by
    apply continuousOn_pi.mpr
    intro i
    exact hJcontinuousComp i
  let Jbar : ParabolicPoint → Vec3 := P.piecewise J (fun _ => 0)
  have hJbarMeas : Measurable Jbar :=
    lerayLimit_measurableOn_extension P hPmeas J (fun _ => 0)
      hJcontinuous continuousOn_const
  have hJbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) : Jbar (x, t) = J (x, t) := by
    change P.piecewise J (fun _ => 0) (x, t) = J (x, t)
    rw [Set.piecewise_eq_of_mem P J (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hJbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (J z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hJbarPos x t hz.2)
  have hJbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) q μ ≤ C := by
    rw [eLpNorm_congr_ae hJbarRawEq]
    simpa [q, J, u, μ, P, C, K, A, regUniformPositiveTimeMeasure] using hJVector
  have hA : MemLp (regUniformSpatialField a) 2 volume := by
    have hcoord : MemLp
        (fun x : L2Vec3 => a (WithLp.ofLp x)) (2 : ℝ≥0∞) volume :=
      ha.1.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hAtop : A < ⊤ := by simpa [A] using hA.eLpNorm_lt_top
  have hKtop : K < ⊤ := by
    dsimp [K]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (Classical.choose_spec CKN.sobolev_L6_global).1
  have hCtop : C < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hKtop) hAtop
  have hBnonneg : 0 ≤ B := ENNReal.toReal_nonneg
  have hCofReal : C = ENNReal.ofReal B := by
    simp [B, ENNReal.ofReal_toReal hCtop.ne]
  have hUcomponent : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => Ubar z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => Ubar z i) q μ ≤ C := by
    intro i
    exact regContract_vector_component_bound Ubar hUbarMeas
      hUbarBound hCtop i
  have hJcomponent : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => Jbar z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => Jbar z i) q μ ≤ C := by
    intro i
    exact regContract_vector_component_bound Jbar hJbarMeas
      hJbarBound hCtop i
  have hUcomponentRaw : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => u z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => u z i) q μ ≤ C := by
    intro i
    have hEq : (fun z : ParabolicPoint => Ubar z i) =ᵐ[μ]
        (fun z => u z i) := by
      filter_upwards [ae_restrict_mem hPmeas] with z hz
      rcases z with ⟨x, t⟩
      exact congrArg (fun v : Vec3 => v i) (hUbarPos x t hz.2)
    exact ⟨(memLp_congr_ae hEq).1 (hUcomponent i).1,
      by rw [← eLpNorm_congr_ae hEq]; exact (hUcomponent i).2⟩
  have hJcomponentRaw : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => J z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => J z i) q μ ≤ C := by
    intro i
    have hEq : (fun z : ParabolicPoint => Jbar z i) =ᵐ[μ]
        (fun z => J z i) := by
      filter_upwards [ae_restrict_mem hPmeas] with z hz
      rcases z with ⟨x, t⟩
      exact congrArg (fun v : Vec3 => v i) (hJbarPos x t hz.2)
    exact ⟨(memLp_congr_ae hEq).1 (hJcomponent i).1,
      by rw [← eLpNorm_congr_ae hEq]; exact (hJcomponent i).2⟩
  have hUbarComponentEq (i : Fin 3) :
      (fun z : ParabolicPoint => Ubar z i) =
        P.indicator (fun z : ParabolicPoint => u z i) := by
    funext z
    by_cases hz : z ∈ P <;> simp [Ubar, hz]
  have hJbarComponentEq (i : Fin 3) :
      (fun z : ParabolicPoint => Jbar z i) =
        P.indicator (fun z : ParabolicPoint => J z i) := by
    funext z
    by_cases hz : z ∈ P <;> simp [Jbar, hz]
  have hUfull : ∀ i : Fin 3,
      MemLp (fun z : Vec3 × ℝ => Ubar z i) q volume := by
    intro i
    have hInd := (memLp_indicator_iff_restrict hPmeas).2 (hUcomponentRaw i).1
    exact (memLp_congr_ae (Filter.Eventually.of_forall
      (fun z => congrFun (hUbarComponentEq i).symm z))).1 hInd
  have hJfull : ∀ i : Fin 3,
      MemLp (fun z : Vec3 × ℝ => Jbar z i) q volume := by
    intro i
    have hInd := (memLp_indicator_iff_restrict hPmeas).2 (hJcomponentRaw i).1
    exact (memLp_congr_ae (Filter.Eventually.of_forall
      (fun z => congrFun (hJbarComponentEq i).symm z))).1 hInd
  have hUfullBound : ∀ i : Fin 3,
      eLpNorm (fun z : Vec3 × ℝ => Ubar z i) q volume ≤ ENNReal.ofReal B := by
    intro i
    change eLpNorm (fun z : ParabolicPoint => Ubar z i) q volume ≤ _
    rw [hUbarComponentEq i, eLpNorm_indicator_eq_eLpNorm_restrict hPmeas]
    calc
      eLpNorm (fun z : ParabolicPoint => u z i) q μ ≤ C := (hUcomponentRaw i).2
      _ = ENNReal.ofReal B := hCofReal
  have hJfullBound : ∀ i : Fin 3,
      eLpNorm (fun z : Vec3 × ℝ => Jbar z i) q volume ≤ ENNReal.ofReal B := by
    intro i
    change eLpNorm (fun z : ParabolicPoint => Jbar z i) q volume ≤ _
    rw [hJbarComponentEq i, eLpNorm_indicator_eq_eLpNorm_restrict hPmeas]
    calc
      eLpNorm (fun z : ParabolicPoint => J z i) q μ ≤ C := (hJcomponentRaw i).2
      _ = ENNReal.ofReal B := hCofReal
  obtain ⟨hFglobal, _hGlobalClassBound⟩ :=
    regPressure_regularized_fiveThirds_bound
      Jbar Ubar hJfull hUfull B B hBnonneg hBnonneg hJfullBound hUfullBound
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    regPressureSpaceTimeTensor Jbar Ubar
  have hFglobalBound : ∀ i j : Fin 3,
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤
        ENNReal.ofReal (B ^ 2) := by
    have : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
        (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
      have h : (10 / 3 : ℝ).HolderTriple (10 / 3 : ℝ) (5 / 3 : ℝ) :=
        ⟨by norm_num, by norm_num, by norm_num⟩
      exact h.ennrealOfReal
    intro i j
    have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := ENNReal.ofReal (10 / 3 : ℝ))
      (q := ENNReal.ofReal (10 / 3 : ℝ))
      (r := ENNReal.ofReal (5 / 3 : ℝ))
      (fun a b : ℝ => a * b) 1 continuous_mul
      (hJfull i).aestronglyMeasurable (hUfull j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simp [Real.norm_eq_abs])
    calc
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤
          eLpNorm (fun z : Vec3 × ℝ => Jbar z i)
            (ENNReal.ofReal (10 / 3 : ℝ)) volume *
          eLpNorm (fun z : Vec3 × ℝ => Ubar z j)
            (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
        change eLpNorm (fun z : Vec3 × ℝ => Jbar z i * Ubar z j)
          (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤ _
        simpa [ENNReal.smul_def, one_mul] using hHolder
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal B :=
        mul_le_mul (hJfullBound i) (hUfullBound j) (by positivity) (by positivity)
      _ = ENNReal.ofReal (B ^ 2) := by
        rw [← ENNReal.ofReal_mul hBnonneg]
        congr 1
        ring
  let FT : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j => S.indicator (F i j)
  have hFT53 : ∀ i j,
      MemLp (FT i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume := by
    intro i j
    change MemLp (S.indicator (F i j)) (ENNReal.ofReal (5 / 3 : ℝ)) volume
    exact (memLp_indicator_iff_restrict hSmeas).2
      ((hFglobal i j).mono_measure Measure.restrict_le_self)
  have hFT53Bound : ∀ i j,
      eLpNorm (FT i j) (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤
        ENNReal.ofReal (B ^ 2) := by
    intro i j
    change eLpNorm (S.indicator (F i j))
      (ENNReal.ofReal (5 / 3 : ℝ)) volume ≤ ENNReal.ofReal (B ^ 2)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hSmeas]
    calc
      eLpNorm (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
          (volume.restrict S) ≤ eLpNorm (F i j)
            (ENNReal.ofReal (5 / 3 : ℝ)) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal (B ^ 2) := hFglobalBound i j
  have hAofReal : ENNReal.ofReal A.toReal = A :=
    ENNReal.ofReal_toReal hAtop.ne
  have hA2ofReal : ENNReal.ofReal Areal = A ^ (2 : ℕ) := by
    dsimp [Areal]
    rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, hAofReal]
  have hFT1Bound : ∀ i j,
      eLpNorm (FT i j) 1 volume ≤ ENNReal.ofReal (T * Areal) := by
    have hSlabMeasure : (volume : Measure (Vec3 × ℝ)).restrict S =
        (volume : Measure Vec3).prod μt := by
      change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (Set.univ ×ˢ Ioo (0 : ℝ) T) = _
      rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
        (ν := (volume : Measure ℝ)) Set.univ (Ioo (0 : ℝ) T)]
      simp [μt, Measure.restrict_univ]
    have hFmeas (i j : Fin 3) : Measurable (F i j) := by
      change Measurable (fun z : Vec3 × ℝ => Jbar z i * Ubar z j)
      exact ((measurable_pi_apply i).comp hJbarMeas).mul
        ((measurable_pi_apply j).comp hUbarMeas)
    have hTimeUniv : μt Set.univ = ENNReal.ofReal T := by
      simp [μt, Real.volume_Ioo]
    have hSliceTensorL1 (t : ℝ) (ht : 0 < t) (htT : t < T)
        (i j : Fin 3) :
        eLpNorm (fun x : Vec3 => F i j (x, t)) 1 volume ≤ A ^ (2 : ℕ) := by
      have hSliceBounds := regContract_slice_vecNorm_bound
        ρ ε hε a u D hA hSlice hEnergy t (le_of_lt ht)
      have hUbarSlice :
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Ubar (x, t)))
            2 volume ≤ A := by
        rw [eLpNorm_congr_ae (Filter.Eventually.of_forall fun x =>
          congrArg vec3EuclideanNorm (hUbarPos x t ht))]
        simpa [A] using hSliceBounds.1
      have hJbarSlice :
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Jbar (x, t)))
            2 volume ≤ A := by
        rw [eLpNorm_congr_ae (Filter.Eventually.of_forall fun x =>
          congrArg vec3EuclideanNorm (hJbarPos x t ht))]
        simpa [A] using hSliceBounds.2
      have hUbarSliceMeas : Measurable (fun x : Vec3 => Ubar (x, t)) :=
        hUbarMeas.comp (measurable_id.prodMk measurable_const)
      have hJbarSliceMeas : Measurable (fun x : Vec3 => Jbar (x, t)) :=
        hJbarMeas.comp (measurable_id.prodMk measurable_const)
      have hJi := regContract_vector_component_bound
        (fun x : Vec3 => Jbar (x, t)) hJbarSliceMeas hJbarSlice hAtop i
      have hUi := regContract_vector_component_bound
        (fun x : Vec3 => Ubar (x, t)) hUbarSliceMeas hUbarSlice hAtop j
      have : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
          (ENNReal.ofReal (2 : ℝ)) 1 := by
        have h : (2 : ℝ).HolderTriple 2 1 :=
          ⟨by norm_num, by norm_num, by norm_num⟩
        simpa using h.ennrealOfReal
      have hProdMem : MemLp
          (fun x : Vec3 => Jbar (x, t) i * Ubar (x, t) j) 1 volume :=
        (hJi.1).mul (hUi.1)
      have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (2 : ℝ)) (q := ENNReal.ofReal (2 : ℝ))
        (r := (1 : ℝ≥0∞)) (fun a b : ℝ => a * b) 1 continuous_mul
        hJi.1.aestronglyMeasurable hUi.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
      have hHolder' : eLpNorm
          (fun x : Vec3 => Jbar (x, t) i * Ubar (x, t) j) 1 volume ≤
          eLpNorm (fun x : Vec3 => Jbar (x, t) i) 2 volume *
            eLpNorm (fun x : Vec3 => Ubar (x, t) j) 2 volume := by
        simpa [ENNReal.smul_def, one_mul] using hHolder
      have hProductBound : eLpNorm
          (fun x : Vec3 => Jbar (x, t) i * Ubar (x, t) j) 1 volume ≤
          A * A := by
        calc
          _ ≤ eLpNorm (fun x : Vec3 => Jbar (x, t) i) 2 volume *
              eLpNorm (fun x : Vec3 => Ubar (x, t) j) 2 volume := hHolder'
          _ ≤ A * A := mul_le_mul hJi.2 hUi.2 (by positivity) (by positivity)
      have hTensorEq :
          (fun x : Vec3 => F i j (x, t)) =
            (fun x : Vec3 => Jbar (x, t) i * Ubar (x, t) j) := by
        funext x
        rfl
      rw [eLpNorm_congr_ae (Filter.Eventually.of_forall
        (fun x => congrFun hTensorEq x))]
      calc
        eLpNorm (fun x : Vec3 => Jbar (x, t) i * Ubar (x, t) j) 1 volume ≤
            A * A := hProductBound
        _ = A ^ (2 : ℕ) := by simp [pow_two]
    intro i j
    change eLpNorm (S.indicator (F i j)) 1 volume ≤ ENNReal.ofReal (T * Areal)
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hSmeas, hSlabMeasure]
    have hFmeas : Measurable (F i j) := by
      change Measurable (fun z : Vec3 × ℝ => Jbar z i * Ubar z j)
      exact ((measurable_pi_apply i).comp hJbarMeas).mul
        ((measurable_pi_apply j).comp hUbarMeas)
    calc
      eLpNorm (F i j) 1 ((volume : Measure Vec3).prod μt) =
          ∫⁻ z : Vec3 × ℝ, ‖F i j z‖ₑ
            ∂((volume : Measure Vec3).prod μt) :=
        eLpNorm_one_eq_lintegral_enorm hFmeas.aestronglyMeasurable
      _ = ∫⁻ t : ℝ, ∫⁻ x : Vec3, ‖F i j (x, t)‖ₑ ∂volume ∂μt := by
        rw [MeasureTheory.lintegral_prod _ hFmeas.enorm.aemeasurable]
        exact MeasureTheory.lintegral_lintegral_swap
          (μ := (volume : Measure Vec3)) (ν := μt)
          (f := fun x t => ‖F i j (x, t)‖ₑ)
          hFmeas.enorm.aemeasurable
      _ ≤ ∫⁻ t : ℝ, A ^ (2 : ℕ) ∂μt := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        have hSliceFmeas : Measurable (fun x : Vec3 => F i j (x, t)) :=
          hFmeas.comp (measurable_id.prodMk measurable_const)
        rw [← eLpNorm_one_eq_lintegral_enorm
          hSliceFmeas.aestronglyMeasurable]
        exact hSliceTensorL1 t ht.1 ht.2 i j
      _ = ENNReal.ofReal T * A ^ (2 : ℕ) := by
        rw [lintegral_const]
        rw [hTimeUniv]
        exact mul_comm _ _
      _ = ENNReal.ofReal (T * Areal) := by
        rw [← hA2ofReal, ← ENNReal.ofReal_mul hT.le]
  have hFT1 : ∀ i j, MemLp (FT i j) 1 volume := by
    intro i j
    rw [memLp_iff]
    exact lt_of_le_of_lt (hFT1Bound i j) ENNReal.ofReal_lt_top
  have hFT53ForInterp : ∀ i j,
      MemLp (FT i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) := hFT53
  have hFT1ForInterp : ∀ i j,
      MemLp (FT i j) (ENNReal.ofReal (1 : ℝ))
        (volume : Measure (Vec3 × ℝ)) := by
    simpa using hFT1
  have hFT1BoundForInterp : ∀ i j,
      eLpNorm (FT i j) (ENNReal.ofReal (1 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal (T * Areal) := by
    simpa using hFT1Bound
  have hFT53BoundForInterp : ∀ i j,
      eLpNorm (FT i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure (Vec3 × ℝ)) ≤ ENNReal.ofReal Mreal := by
    simpa [Mreal, B] using hFT53Bound
  have hTnn : 0 ≤ T := le_of_lt hT
  have hAnnonneg : 0 ≤ Areal := by positivity
  have hMnonneg : 0 ≤ Mreal := by positivity
  obtain ⟨hF32, hClassBound⟩ := regPressure_spaceTime_threeHalves_norm_bound
    T Areal Mreal hTnn hAnnonneg hMnonneg FT hFT1ForInterp
    hFT53ForInterp hFT1BoundForInterp hFT53BoundForInterp
  have hR4 : ∀ t : ℝ, 0 < t → t < T → ∃ hF2 : ∀ i j : Fin 3,
      MemLp (fun x : Vec3 => FT i j (x, t)) (ENNReal.ofReal 2) volume,
      (fun x : Vec3 => pbar (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative 2 (by norm_num)
          (fun i j => (hF2 i j).toLp (fun x : Vec3 => FT i j (x, t))) := by
    intro t ht htT
    rcases hPressure t ht with ⟨hF2raw, hPressureEq, _hDistribution⟩
    have hTensorEq (i j : Fin 3) :
        (fun x : Vec3 => FT i j (x, t)) =
          (fun x : Vec3 => J (x, t) i * u (x, t) j) := by
      funext x
      change S.indicator (F i j) (x, t) = J (x, t) i * u (x, t) j
      have hxS : ((x, t) : Vec3 × ℝ) ∈ S := by
        change x ∈ Set.univ ∧ t ∈ Ioo 0 T
        exact ⟨Set.mem_univ _, ⟨ht, htT⟩⟩
      rw [Set.indicator_of_mem hxS]
      change Jbar (x, t) i * Ubar (x, t) j = _
      rw [hJbarPos x t ht, hUbarPos x t ht]
    let hF2 : ∀ i j : Fin 3,
        MemLp (fun x : Vec3 => FT i j (x, t)) (ENNReal.ofReal 2) volume := by
      intro i j
      rw [hTensorEq i j]
      exact hF2raw i j
    have hLpEq :
        (fun i j => (hF2 i j).toLp (fun x : Vec3 => FT i j (x, t))) =
          (fun i j => (hF2raw i j).toLp
            (fun x : Vec3 => J (x, t) i * u (x, t) j)) := by
      funext i j
      apply Lp.ext
      filter_upwards [(hF2 i j).coeFn_toLp, (hF2raw i j).coeFn_toLp]
        with x hnew hraw
      exact hnew.trans ((congrFun (hTensorEq i j) x).trans hraw.symm)
    have hRepEq := congrArg (rieszPressureSliceRepresentative 2 (by norm_num)) hLpEq
    have hPbar : (fun x : Vec3 => pbar (x, t)) =ᵐ[volume]
        (fun x => p (x, t)) := by
      filter_upwards [] with x
      exact hpbarPos x t ht
    refine ⟨hF2, ?_⟩
    exact hPbar.trans (hPressureEq.trans
      (Filter.Eventually.of_forall fun x => (congrFun hRepEq x).symm))
  have hPressureRep := regContract_pressure_ae_eq_truncatedSpaceTimeRiesz
    T (3 / 2 : ℝ) (by norm_num) FT hF32 pbar hpbarMeas hR4
  have hpbarActual : (fun z : Vec3 × ℝ => pbar z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict S] (fun z => p z) := by
    filter_upwards [ae_restrict_mem hSmeas] with z hz
    rcases z with ⟨x, t⟩
    exact hpbarPos x t hz.2.1
  have hpActualRep : (fun z : Vec3 × ℝ => p z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict S]
      rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32 :=
    hpbarActual.symm.trans hPressureRep
  let hFull : MemLp (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp (3 / 2 : ℝ) (by norm_num) FT hF32
  have hSlabLe : (volume : Measure (Vec3 × ℝ)).restrict S ≤
      (volume : Measure (Vec3 × ℝ)) := Measure.restrict_le_self
  let hp : MemLp (pε a ha ε) (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict S) := by
    change MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict S)
    exact (memLp_congr_ae hpActualRep).2 (hFull.mono_measure hSlabLe)
  have hNorm : eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
        ((volume : Measure (Vec3 × ℝ)).restrict S) ≤
      eLpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    calc
      eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict S) =
        eLpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
          (ENNReal.ofReal (3 / 2 : ℝ)) ((volume : Measure (Vec3 × ℝ)).restrict S) :=
            eLpNorm_congr_ae hpActualRep
      _ ≤ eLpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) :=
        eLpNorm_mono_measure _ hSlabLe
  let pressureClass := rieszPressureSpaceTimeClass (3 / 2 : ℝ) (by norm_num)
    (rieszPressureSpaceTimeTensorToLp (3 / 2 : ℝ) (by norm_num) FT hF32)
  have hRepClass : rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32 =ᵐ[
      (volume : Measure (Vec3 × ℝ))] pressureClass := by
    simpa [pressureClass, rieszPressureSpaceTime,
      rieszPressureSpaceTimeRepresentative] using
      ((Lp.aestronglyMeasurable pressureClass).aemeasurable.ae_eq_mk).symm
  have hRieszLpNormBound :
      lpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
        (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) ≤
      9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
        ((T * Areal) ^ (1 / 6 : ℝ) * Mreal ^ (5 / 6 : ℝ)) := by
    change ENNReal.toReal (eLpNorm
      (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) ≤ _
    rw [eLpNorm_congr_ae hRepClass]
    simpa only [Lp.norm_def] using hClassBound
  refine ⟨hp, ?_⟩
  calc
    lpNorm (pε a ha ε) (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict S) =
        ENNReal.toReal (eLpNorm p (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict S)) := by
        rfl
    _ ≤ ENNReal.toReal (eLpNorm
          (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ))) :=
        ENNReal.toReal_mono hFull.eLpNorm_ne_top hNorm
    _ = lpNorm (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) FT hF32)
          (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := rfl
    _ ≤ 9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
        ((T * Areal) ^ (1 / 6 : ℝ) * Mreal ^ (5 / 6 : ℝ)) := hRieszLpNormBound

end CKN.Leray

end
