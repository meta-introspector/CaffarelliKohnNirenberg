-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegContractBoundsL2
public import CKN.Leray.RegContractBoundsTenThirds
public import CKN.Leray.RegPressureBound
public import CKN.Leray.RieszPressureSlices
public import CKN.Leray.RegUniformEnergy
public import CKN.Leray.RieszPressurePackageSlices
public import CKN.Leray.LerayLimitMeasurability
public import CKN.Statements.SpaceTimeSet

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)

/-- The two vector estimates in `lem:reg-ten-thirds`, with an explicit
constant depending only on the Sobolev interpolation constant. -/
theorem regContract_regTenThirds
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) :
    eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (uε a ha ε z))
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure +
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z))
        (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
      6 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
        eLpNorm (regUniformSpatialField a) 2 volume := by
  have hu := regContract_velocity_tenThirds
    (ρ := ρ) (uε := uε) (pε := pε) (hregularised := hregularised)
    a ha ε hε
  have hJ := regContract_mollifiedVelocity_tenThirds
    (ρ := ρ) (uε := uε) (pε := pε) (hregularised := hregularised)
    a ha ε hε
  calc
    _ ≤
        3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
            eLpNorm (regUniformSpatialField a) 2 volume +
          3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
            eLpNorm (regUniformSpatialField a) 2 volume := add_le_add hu hJ
    _ = 6 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
          eLpNorm (regUniformSpatialField a) 2 volume := by ring

/-- A coordinate of a measurable vector field is controlled in `L^q` by
its Euclidean norm. -/
theorem regContract_vector_component_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → Vec3) {q B : ℝ≥0∞}
    (hf : Measurable f)
    (hB : eLpNorm (fun z => vec3EuclideanNorm (f z)) q μ ≤ B)
    (hBtop : B < ⊤) (i : Fin 3) :
    MemLp (fun z => f z i) q μ ∧
      eLpNorm (fun z => f z i) q μ ≤ B := by
  have hcoordMeas : Measurable (fun z => f z i) :=
    (measurable_pi_apply i).comp hf
  have hcoordBound : eLpNorm (fun z => f z i) q μ ≤ B := by
    calc
      eLpNorm (fun z => f z i) q μ ≤
          eLpNorm (fun z => vec3EuclideanNorm (f z)) q μ :=
        eLpNorm_mono_ae_real hcoordMeas.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by
            rw [Real.norm_eq_abs]
            exact abs_apply_le_vec3EuclideanNorm (f z) i)
      _ ≤ B := hB
  constructor
  · rw [memLp_iff]
    exact lt_of_le_of_lt hcoordBound hBtop
  · exact hcoordBound

private theorem regContract_pressure_ae_eq_spaceTimeRiesz
    (r : ℝ) (hr : 1 < r)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (p : Vec3 × ℝ → ℝ) (hpMeas : Measurable p)
    (hR4 : ∀ t : ℝ, 0 < t → ∃ hF2 : ∀ i j,
      MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal 2)
        (volume : Measure Vec3),
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        rieszPressureSliceRepresentative 2 (by norm_num)
          (fun i j => (hF2 i j).toLp
            (fun x : Vec3 => F i j (x, t)))) :
    (fun z : Vec3 × ℝ => p z) =ᵐ[regUniformPositiveTimeMeasure]
      rieszPressureSpaceTime r hr F hF := by
  let μt : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hPositiveTimeMeasure :
      regUniformPositiveTimeMeasure =
        (volume : Measure Vec3).prod μt := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)) =
      (volume : Measure Vec3).prod (volume.restrict (Set.Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Set.Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hRieszMeas := rieszPressureSpaceTime_measurable r hr F hF
  have hSlices := rieszPressureSpaceTime_slice_ae_eq r hr F hF
  have hSliceEq : ∀ᵐ t ∂μt,
      (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        fun x => rieszPressureSpaceTime r hr F hF (x, t) := by
    filter_upwards [ae_restrict_of_ae hSlices,
      ae_restrict_mem measurableSet_Ioi] with t ht hpos
    rcases ht with ⟨hFrt, hSpaceTimePressure⟩
    rcases hR4 t hpos with ⟨hF2t, hR4Pressure⟩
    let F2 : PressureTensorLp 2 := fun i j =>
      (hF2t i j).toLp (fun x : Vec3 => F i j (x, t))
    have hRepresentative := rieszPressureSliceRepresentative_ae_eq
      2 (by norm_num) F2
    have hCommon := rieszPressureSlice_ae_eq_of_memLp_common
      r hr 2 (by norm_num) (fun i j x => F i j (x, t)) hFrt hF2t
    have hPtoSlice2 : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (rieszPressureSlice 2 (by norm_num) F2 : Vec3 → ℝ) := by
      exact hR4Pressure.trans hRepresentative.symm
    have hPtoSliceR : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (rieszPressureSlice r hr
          (fun i j => (hFrt i j).toLp (fun x : Vec3 => F i j (x, t))) :
            Vec3 → ℝ) := hPtoSlice2.trans hCommon.symm
    exact hPtoSliceR.trans hSpaceTimePressure.symm
  let S : Set (Vec3 × ℝ) :=
    {z | p z = rieszPressureSpaceTime r hr F hF z}
  have hSmeas : MeasurableSet S :=
    measurableSet_eq_fun hpMeas hRieszMeas
  have hSections : ∀ᵐ t ∂μt, ∀ᵐ x : Vec3 ∂volume,
      p (x, t) = rieszPressureSpaceTime r hr F hF (x, t) := hSliceEq
  have hSswap : MeasurableSet
      {z : ℝ × Vec3 | p (z.2, z.1) =
        rieszPressureSpaceTime r hr F hF (z.2, z.1)} := by
    change MeasurableSet (Prod.swap ⁻¹' S)
    exact measurableSet_swap_iff.mpr hSmeas
  have hSectionsSwap : ∀ᵐ x : Vec3 ∂volume, ∀ᵐ t ∂μt,
      p (x, t) = rieszPressureSpaceTime r hr F hF (x, t) :=
    (Measure.ae_ae_comm hSswap).mp hSections
  have hProduct : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod μt),
      z ∈ S := (Measure.ae_prod_iff_ae_ae hSmeas).2 hSectionsSwap
  rw [hPositiveTimeMeasure]
  filter_upwards [hProduct] with z hz
  exact hz

private theorem regContract_pressure_memLp_of_spaceTimeRiesz
    (r : ℝ) (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (p : Vec3 × ℝ → ℝ)
    (hEq : p =ᵐ[regUniformPositiveTimeMeasure]
      rieszPressureSpaceTime r hr F hF)
    (B : ℝ) (hBound :
      ‖rieszPressureSpaceTimeClass r hr
        (rieszPressureSpaceTimeTensorToLp r hr F hF)‖ ≤ B) :
    ∃ _hp : MemLp p (ENNReal.ofReal r) regUniformPositiveTimeMeasure,
      ENNReal.toReal (eLpNorm p (ENNReal.ofReal r)
        regUniformPositiveTimeMeasure) ≤ B := by
  let hFull : MemLp (rieszPressureSpaceTime r hr F hF)
      (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
    rieszPressureSpaceTime_memLp r hr F hF
  have hPositiveLe : regUniformPositiveTimeMeasure ≤
      (volume : Measure (Vec3 × ℝ)) := Measure.restrict_le_self
  let hPositive : MemLp (rieszPressureSpaceTime r hr F hF)
      (ENNReal.ofReal r) regUniformPositiveTimeMeasure :=
    hFull.mono_measure hPositiveLe
  let hp : MemLp p (ENNReal.ofReal r) regUniformPositiveTimeMeasure :=
    (memLp_congr_ae hEq).2 hPositive
  have hNorm : eLpNorm p (ENNReal.ofReal r) regUniformPositiveTimeMeasure ≤
      eLpNorm (rieszPressureSpaceTime r hr F hF)
        (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) := by
    calc
      eLpNorm p (ENNReal.ofReal r) regUniformPositiveTimeMeasure =
          eLpNorm (rieszPressureSpaceTime r hr F hF)
            (ENNReal.ofReal r) regUniformPositiveTimeMeasure := eLpNorm_congr_ae hEq
      _ ≤ eLpNorm (rieszPressureSpaceTime r hr F hF)
          (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ)) :=
        eLpNorm_mono_measure _ hPositiveLe
  let : Fact (1 ≤ ENNReal.ofReal r) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr.le⟩
  let pressureClass := rieszPressureSpaceTimeClass r hr
    (rieszPressureSpaceTimeTensorToLp r hr F hF)
  have hRep : rieszPressureSpaceTime r hr F hF =ᵐ[volume] pressureClass := by
    simpa [pressureClass, rieszPressureSpaceTime,
      rieszPressureSpaceTimeRepresentative] using
      ((Lp.aestronglyMeasurable pressureClass).aemeasurable.ae_eq_mk).symm
  have hFullEq : hFull.toLp (rieszPressureSpaceTime r hr F hF) = pressureClass := by
    apply Lp.ext
    filter_upwards [hFull.coeFn_toLp, hRep] with z hz hclass
    exact hz.trans hclass
  refine ⟨hp, ?_⟩
  calc
    ENNReal.toReal (eLpNorm p (ENNReal.ofReal r)
        regUniformPositiveTimeMeasure) ≤
    ENNReal.toReal (eLpNorm (rieszPressureSpaceTime r hr F hF)
        (ENNReal.ofReal r) (volume : Measure (Vec3 × ℝ))) :=
      ENNReal.toReal_mono hFull.eLpNorm_ne_top hNorm
    _ = ‖hFull.toLp (rieszPressureSpaceTime r hr F hF)‖ :=
      (Lp.norm_toLp _ hFull).symm
    _ = ‖pressureClass‖ := congrArg norm hFullEq
    _ ≤ B := hBound

/-- The pressure in the regularized contract satisfies the global
`L^(5/3)` estimate of `lem:reg-pressure-bound`. -/
theorem regContract_regPressure_fiveThirds
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) :
    ∃ hp : MemLp (pε a ha ε) (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure,
      ‖hp.toLp (pε a ha ε)‖ ≤
        9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
          (((3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
            eLpNorm (regUniformSpatialField a) 2 volume).toReal) ^ 2) := by
  classical
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let p : ParabolicPoint → ℝ := pε a ha ε
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi (0 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict P
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let K : ℝ≥0∞ := CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  let C : ℝ≥0∞ := 3 * K * A
  let B : ℝ := C.toReal
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitialAE, _hWeakDivFree⟩,
      hUcont, _hDcont, _hDDcont, _hDtcont, hPcont, _hDpcont,
      hUcontDiff, _hDdiff, _hPdiff, _hBounds, _hLocalLp,
      _hEquation, hPressure, _hEnergy⟩
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
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
  have hUVector := regContract_velocity_tenThirds
    (ρ := ρ) (uε := uε) (pε := pε) (hregularised := hregularised)
    a ha ε hε
  have hJVector := regContract_mollifiedVelocity_tenThirds
    (ρ := ρ) (uε := uε) (pε := pε) (hregularised := hregularised)
    a ha ε hε
  let : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
  let : NormedAddCommGroup ParabolicPoint :=
    inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
  let : NormedSpace ℝ ParabolicPoint :=
    inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
  let : OpensMeasurableSpace ParabolicPoint := by
    change OpensMeasurableSpace (Vec3 × ℝ)
    let : SecondCountableTopologyEither Vec3 ℝ :=
      ⟨Or.inl inferInstance⟩
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
  have hUbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (u z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hUbarPos x t hz.2)
  have hUrawBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) q μ ≤ C := by
    simpa [u, q, μ, P, C, K, A, regUniformPositiveTimeMeasure] using hUVector
  have hUbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ ≤ C := by
    rw [eLpNorm_congr_ae hUbarRawEq]
    exact hUrawBound
  have hJbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (J z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hJbarPos x t hz.2)
  have hJrawBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (J z)) q μ ≤ C := by
    simpa [J, u, q, μ, P, C, K, A, regUniformPositiveTimeMeasure] using hJVector
  have hJbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) q μ ≤ C := by
    rw [eLpNorm_congr_ae hJbarRawEq]
    exact hJrawBound
  have hUcomponent : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => Ubar z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => Ubar z i) q μ ≤ C := by
    intro i
    exact regContract_vector_component_bound Ubar hUbarMeas hUbarBound hCtop i
  have hJcomponent : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => Jbar z i) q μ ∧
        eLpNorm (fun z : ParabolicPoint => Jbar z i) q μ ≤ C := by
    intro i
    exact regContract_vector_component_bound Jbar hJbarMeas hJbarBound hCtop i
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
  obtain ⟨hF, hClassBound⟩ := regPressure_regularized_fiveThirds_bound
    Jbar Ubar hJfull hUfull B B hBnonneg hBnonneg hJfullBound hUfullBound
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ :=
    regPressureSpaceTimeTensor Jbar Ubar
  have hpRep :
      (fun z : Vec3 × ℝ => pbar z) =ᵐ[regUniformPositiveTimeMeasure]
        rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF := by
    have hR4 : ∀ t : ℝ, 0 < t → ∃ hF2 : ∀ i j : Fin 3,
        MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => pbar (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF2 i j).toLp (fun x : Vec3 => F i j (x, t))) := by
      intro t ht
      rcases hPressure t ht with ⟨hF2raw, hPressureEq, _hDistribution⟩
      have hTensorEq (i j : Fin 3) :
          (fun x : Vec3 => F i j (x, t)) =
            (fun x : Vec3 => J (x, t) i * u (x, t) j) := by
        funext x
        change Jbar (x, t) i * Ubar (x, t) j = J (x, t) i * u (x, t) j
        rw [hJbarPos x t ht, hUbarPos x t ht]
      let hF2 : ∀ i j : Fin 3,
          MemLp (fun x : Vec3 => F i j (x, t)) (ENNReal.ofReal 2) volume := by
        intro i j
        rw [hTensorEq i j]
        exact hF2raw i j
      have hLpEq :
          (fun i j => (hF2 i j).toLp (fun x : Vec3 => F i j (x, t))) =
            (fun i j => (hF2raw i j).toLp
              (fun x : Vec3 => J (x, t) i * u (x, t) j)) := by
        funext i j
        apply Lp.ext
        filter_upwards [(hF2 i j).coeFn_toLp, (hF2raw i j).coeFn_toLp]
          with x hnew hraw
        exact hnew.trans ((congrFun (hTensorEq i j) x).trans hraw.symm)
      have hRepEq := congrArg
        (rieszPressureSliceRepresentative 2 (by norm_num)) hLpEq
      have hPbar : (fun x : Vec3 => pbar (x, t)) =ᵐ[volume]
          (fun x => p (x, t)) := by
        filter_upwards [] with x
        exact hpbarPos x t ht
      refine ⟨hF2, ?_⟩
      exact hPbar.trans (hPressureEq.trans
        (Filter.Eventually.of_forall (fun x => (congrFun hRepEq x).symm)))
    exact regContract_pressure_ae_eq_spaceTimeRiesz
      (5 / 3 : ℝ) (by norm_num) F hF pbar hpbarMeas hR4
  have hpbarActual :
      (fun z : Vec3 × ℝ => pbar z) =ᵐ[regUniformPositiveTimeMeasure]
        (fun z => p z) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact hpbarPos x t hz.2
  have hpActualRep : (fun z : Vec3 × ℝ => p z) =ᵐ[regUniformPositiveTimeMeasure]
      rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF :=
    hpbarActual.symm.trans hpRep
  have hClassBound' :
      ‖rieszPressureSpaceTimeClass (5 / 3 : ℝ) (by norm_num)
        (rieszPressureSpaceTimeTensorToLp (5 / 3 : ℝ) (by norm_num) F hF)‖ ≤
        9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * (B * B) := by
    simpa [F] using hClassBound
  let : Fact (1 ≤ ENNReal.ofReal (5 / 3 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨hp, hpBound⟩ := regContract_pressure_memLp_of_spaceTimeRiesz
    (5 / 3 : ℝ) (by norm_num) F hF p hpActualRep
    (9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * (B * B))
    hClassBound'
  refine ⟨hp, ?_⟩
  have hpNorm : ‖hp.toLp p‖ =
      ENNReal.toReal (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure) := by
    rw [Lp.norm_toLp p hp]
  calc
    ‖hp.toLp (pε a ha ε)‖ ≤
        9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * (B * B) := by
      simpa [p] using hpNorm.le.trans hpBound
    _ = 9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) * (C.toReal ^ 2) := by
      dsimp [B]
      ring
    _ = 9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
        (((3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
          eLpNorm (regUniformSpatialField a) 2 volume).toReal) ^ 2) := by
      rfl

end CKN.Leray

end
