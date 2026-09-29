-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.LerayLimitTenThirds
public import CKN.Leray.RegUniformMomentum
public import CKN.Leray.RegUniformConvolution
public import CKN.Leray.LerayLimitMeasurability
public import CKN.Statements.SpaceTimeSet

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


private theorem regContract_component_tenThirds_norm_bound
    {X K A G : ℝ≥0∞}
    (hX : X ^ (10 / 3 : ℝ) ≤ K ^ (10 / 3 : ℝ) *
      A ^ (4 / 3 : ℝ) * G)
    (hG : G ≤ A ^ (2 : ℝ)) :
    X ≤ K * A := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 10 / 3)).mp
  calc
    X ^ (10 / 3 : ℝ) ≤ K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * G := hX
    _ ≤ K ^ (10 / 3 : ℝ) * A ^ (4 / 3 : ℝ) * A ^ (2 : ℝ) := by
      gcongr
    _ = (K * A) ^ (10 / 3 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg K A (by norm_num)]
      rw [show (10 / 3 : ℝ) = 4 / 3 + 2 by norm_num]
      rw [ENNReal.rpow_add_of_nonneg (x := A) (4 / 3 : ℝ) 2
        (by norm_num) (by norm_num)]
      ac_rfl

private theorem regContract_eLpNorm_rpow_lintegral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ^ (10 / 3 : ℝ) =
      ∫⁻ x, ‖f x‖ₑ ^ (10 / 3 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : ENNReal.ofReal (10 / 3 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 10 / 3),
    ← ENNReal.rpow_mul]
  norm_num

private theorem regContract_mollified_slice_eLpNorm_le
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hSlice : MemLp (fun x : Vec3 => u (x, t)) 2 volume) :
    eLpNorm (fun x : Vec3 => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε u (x, t)))
        (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
  let f : Vec3 → Vec3 := fun x => u (x, t)
  let ψ := regMollifyVector ρ ε hε (regUniformSpatialField f)
  have hcoord := hSlice.comp_measurePreserving
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hf₂ : MemLp (regUniformSpatialField f) 2 volume := by
    have hL2 := hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp (regUniformVelocitySlice u t) 2 volume
    exact hL2
  have hcontract := regMollifyVector_eLpNorm_le ρ ε hε hf₂
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3 : ℝ))
    (by norm_num : ENNReal.ofReal (10 / 3 : ℝ) ≠ ⊤)
  have hraw : AEStronglyMeasurable ψ volume :=
    regMollifyVector_aestronglyMeasurable ρ ε hε hf₂
  have hcomp := hraw.comp_measurePreserving vec3ToL2Vec3_measurePreserving
  have hinput :
      eLpNorm (regUniformL2VectorNormOnVec3 (regUniformSpatialField f))
          (ENNReal.ofReal (10 / 3 : ℝ)) volume =
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp [regUniformL2VectorNormOnVec3, regUniformSpatialField, f,
      vec3EuclideanNorm_eq_l2]
  have houtput :
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm
        (regUniformMollifiedVelocity ρ ε hε u (x, t)))
          (ENNReal.ofReal (10 / 3 : ℝ)) volume = eLpNorm ψ
            (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
    calc
      _ = eLpNorm (fun x : Vec3 => ‖ψ (WithLp.toLp 2 x)‖)
            (ENNReal.ofReal (10 / 3 : ℝ)) volume := by
        apply eLpNorm_congr_ae
        filter_upwards [] with x
        change vec3EuclideanNorm (WithLp.ofLp
            (ψ (WithLp.toLp 2 x))) = ‖ψ (WithLp.toLp 2 x)‖
        rw [vec3EuclideanNorm_eq_l2, WithLp.toLp_ofLp]
      _ = eLpNorm (fun x : Vec3 => ψ (WithLp.toLp 2 x))
            (ENNReal.ofReal (10 / 3 : ℝ)) volume := eLpNorm_norm _ hcomp
      _ = eLpNorm ψ (ENNReal.ofReal (10 / 3 : ℝ)) volume :=
        eLpNorm_comp_measurePreserving hraw vec3ToL2Vec3_measurePreserving
  calc
    _ = eLpNorm ψ (ENNReal.ofReal (10 / 3 : ℝ)) volume := houtput
    _ ≤ eLpNorm (regUniformL2VectorNormOnVec3
        (regUniformSpatialField f)) (ENNReal.ofReal (10 / 3 : ℝ)) volume := hcontract
    _ = eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (10 / 3 : ℝ)) volume := hinput

/-- The velocity in the regularized solution satisfies the space-time
`L^(10/3)` estimate in `lem:reg-ten-thirds`. -/
theorem regContract_velocity_tenThirds
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
    eLpNorm (fun z : ParabolicPoint =>
      vec3EuclideanNorm (uε a ha ε z))
      (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
      3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
        eLpNorm (regUniformSpatialField a) 2 volume := by
  classical
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => u y i) j z
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi (0 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict P
  let A : ℝ≥0∞ := eLpNorm (regUniformSpatialField a) 2 volume
  let K : ℝ≥0∞ := CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  rcases hregularised a ha ε hε with
    ⟨⟨_hSlice, _hSliceContinuous, _hInitialAE, _hWeakDivFree⟩,
      hUcont, hDcont, _hDDcont, _hDtcont, _hPcont, _hDpcont,
      _hUcontDiff, _hDdiff, _hPdiff, _hBounds, _hLocalLp,
      _hEquation, _hPressure, hEnergy⟩
  have hEnergyBounds := lerayLimit_regularised_energy_bounds
    ρ a ha ε hε u D hUcont hDcont hEnergy
  let Ubar : ParabolicPoint → Vec3 := P.piecewise u (fun _ => 0)
  let Dbar : ParabolicPoint → Fin 3 → Vec3 := P.piecewise D (fun _ => 0)
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hUcontinuous : ContinuousOn u P := by
    apply continuousOn_pi.mpr
    intro i
    simpa [u, P] using hUcont i
  have hUbarMeas : Measurable Ubar := by
    exact lerayLimit_measurableOn_extension P hPmeas u (fun _ => 0)
      hUcontinuous continuousOn_const
  have hUbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) :
      Ubar (x, t) = u (x, t) := by
    change P.piecewise u (fun _ => 0) (x, t) = u (x, t)
    rw [Set.piecewise_eq_of_mem P u (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hGraw :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume ∂volume) =
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq Ubar Dbar (x, t)) ∂volume ∂volume) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply lintegral_congr_ae
    filter_upwards [] with x
    have htpos : 0 < t := ht
    have hzt : ((x, t) : ParabolicPoint) ∈ P := by
      change x ∈ Set.univ ∧ 0 < t
      exact ⟨Set.mem_univ _, htpos⟩
    have hDbar : Dbar ((x, t) : ParabolicPoint) = D (x, t) := by
      change P.piecewise D (fun _ => 0) (x, t) = D (x, t)
      rw [Set.piecewise_eq_of_mem P D (fun _ => 0) hzt]
    change ENNReal.ofReal (spatialGradientSq u D ((x, t) : ParabolicPoint)) =
      ENNReal.ofReal (spatialGradientSq Ubar Dbar ((x, t) : ParabolicPoint))
    unfold spatialGradientSq
    rw [← hDbar]
  have hGrawBound :
      (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume ∂volume) ≤ A ^ (2 : ℝ) := by
    rw [hGraw]
    have hBound := hEnergyBounds.2.2
    simpa [A, spatialGradientSq, Dbar, lerayLimitPiecewise, P,
      ENNReal.rpow_natCast] using hBound
  have hComponent : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => u z i) q μ ∧
      eLpNorm (fun z : ParabolicPoint => u z i) q μ ≤ K * A := by
    intro i
    have hTen := lerayLimit_regularised_component_tenThirds
      (ρ := ρ) (uε := uε) (pε := pε)
      (hregularised := hregularised) a ha ε hε i
    have hPower := regContract_component_tenThirds_norm_bound
      (X := eLpNorm (fun z : ParabolicPoint => u z i) q μ)
      (K := K) (A := A)
      (G := ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Vec3,
        ENNReal.ofReal (spatialGradientSq u D (x, t)) ∂volume ∂volume)
      (by simpa [q, μ, P, regUniformPositiveTimeMeasure, A, K] using hTen.2)
      (by simpa [A] using hGrawBound)
    refine ⟨?_, ?_⟩
    · simpa [q, μ, P, regUniformPositiveTimeMeasure] using hTen.1
    · exact hPower
  have hUeuclMeas : Measurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) := by
    exact CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
      hUbarMeas
  have hUeuclAES : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) μ :=
    hUeuclMeas.aestronglyMeasurable
  have hPoint (z : ParabolicPoint) :
      vec3EuclideanNorm (Ubar z) ≤ ∑ i : Fin 3, |Ubar z i| :=
    vec3EuclideanNorm_le_sum_abs (Ubar z)
  have hComponentBar : ∀ i : Fin 3,
      MemLp (fun z : ParabolicPoint => Ubar z i) q μ ∧
      eLpNorm (fun z : ParabolicPoint => Ubar z i) q μ ≤ K * A := by
    intro i
    have hEq : (fun z : ParabolicPoint => Ubar z i) =ᵐ[μ]
        (fun z => u z i) := by
      filter_upwards [ae_restrict_mem hPmeas] with z hz
      rcases z with ⟨x, t⟩
      exact congrArg (fun v : Vec3 => v i) (hUbarPos x t hz.2)
    constructor
    · exact (memLp_congr_ae hEq).2 (hComponent i).1
    · rw [eLpNorm_congr_ae hEq]
      exact (hComponent i).2
  have hSumBound :
      eLpNorm (fun z : ParabolicPoint => ∑ i : Fin 3, |Ubar z i|) q μ ≤
        3 * (K * A) := by
    calc
      eLpNorm (fun z : ParabolicPoint => ∑ i : Fin 3, |Ubar z i|) q μ ≤
          ∑ i : Fin 3, eLpNorm (fun z : ParabolicPoint => |Ubar z i|) q μ := by
        exact eLpNorm_sum_le (p := q) (s := Finset.univ)
          (f := fun i z => |Ubar z i|) (by norm_num [q])
      _ = ∑ i : Fin 3, eLpNorm (fun z : ParabolicPoint => Ubar z i) q μ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          eLpNorm (fun z : ParabolicPoint => |Ubar z i|) q μ =
              eLpNorm (fun z : ParabolicPoint => ‖Ubar z i‖) q μ := by
                apply eLpNorm_congr_ae
                filter_upwards [] with z
                exact (Real.norm_eq_abs _).symm
          _ = eLpNorm (fun z : ParabolicPoint => Ubar z i) q μ :=
              eLpNorm_norm (p := q) (fun z : ParabolicPoint => Ubar z i)
                ((hComponentBar i).1.aestronglyMeasurable)
      _ ≤ ∑ _i : Fin 3, K * A := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hComponentBar i).2
      _ = 3 * (K * A) := by simp
  have hUeuclBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ ≤
        3 * (K * A) := by
    apply (eLpNorm_mono_ae_real hUeuclAES ?_).trans hSumBound
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    exact hPoint z
  have hUrawEq : (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) =ᵐ[μ]
      (fun z => vec3EuclideanNorm (u z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hUbarPos x t hz.2)
  have hRawBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) q μ ≤
        3 * (K * A) := by
    rw [← eLpNorm_congr_ae hUrawEq]
    exact hUeuclBound
  simpa [u, μ, q, A, K, regUniformPositiveTimeMeasure, mul_assoc] using hRawBound

/-- The mollified transport velocity satisfies the companion estimate in
`lem:reg-ten-thirds`. -/
theorem regContract_mollifiedVelocity_tenThirds
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
    eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z))
      (ENNReal.ofReal (10 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
      3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
        eLpNorm (regUniformSpatialField a) 2 volume := by
  classical
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let J : ParabolicPoint → Vec3 := regUniformMollifiedVelocity ρ ε hε u
  let P : Set ParabolicPoint := spaceTimeSet Set.univ (Ioi (0 : ℝ))
  let μ : Measure ParabolicPoint := volume.restrict P
  let μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let q : ℝ≥0∞ := ENNReal.ofReal (10 / 3 : ℝ)
  let qR : ℝ := 10 / 3
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitialAE, _hWeakDivFree⟩,
      _hUcont, _hDcont, _hDDcont, _hDtcont, _hPcont, _hDpcont,
      hUcontDiff, _hDdiff, _hPdiff, _hBounds, _hLocalLp,
      _hEquation, _hPressure, _hEnergy⟩
  have hPmeas : MeasurableSet P := by
    change MeasurableSet (Set.univ ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  let Ubar : ParabolicPoint → Vec3 := P.piecewise u (fun _ => 0)
  have hUcontinuous : ContinuousOn u P := by
    apply continuousOn_pi.mpr
    intro i
    simpa [u, P] using _hUcont i
  have hUbarMeas : Measurable Ubar :=
    lerayLimit_measurableOn_extension P hPmeas u (fun _ => 0)
      hUcontinuous continuousOn_const
  have hUbound := regContract_velocity_tenThirds
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
  have hJcontComp : ∀ i : Fin 3, ContinuousOn (fun z => J z i) P := by
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
    exact hJcontComp i
  let Jbar : ParabolicPoint → Vec3 := P.piecewise J (fun _ => 0)
  have hJbarMeas : Measurable Jbar :=
    lerayLimit_measurableOn_extension P hPmeas J (fun _ => 0)
      hJcontinuous continuousOn_const
  have hUbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) : Ubar (x, t) = u (x, t) := by
    change P.piecewise u (fun _ => 0) (x, t) = u (x, t)
    rw [Set.piecewise_eq_of_mem P u (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hJbarPos (x : Vec3) (t : ℝ) (ht : 0 < t) : Jbar (x, t) = J (x, t) := by
    change P.piecewise J (fun _ => 0) (x, t) = J (x, t)
    rw [Set.piecewise_eq_of_mem P J (fun _ => 0)
      (show ((x, t) : ParabolicPoint) ∈ P by
        change x ∈ Set.univ ∧ 0 < t
        exact ⟨Set.mem_univ _, ht⟩)]
  have hJointMeasure : μ = (volume : Measure Vec3).prod μt := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [μt, Measure.restrict_univ]
  have hUeuclMeas : Measurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hUbarMeas
  have hJeuclMeas : Measurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) :=
    CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp hJbarMeas
  have hUdenMeas : Measurable
      (fun z : ParabolicPoint => ‖vec3EuclideanNorm (Ubar z)‖ₑ ^ qR) := by
    fun_prop
  have hJdenMeas : Measurable
      (fun z : ParabolicPoint => ‖vec3EuclideanNorm (Jbar z)‖ₑ ^ qR) := by
    fun_prop
  have hUdenProd : AEMeasurable
      (fun z : Vec3 × ℝ => ‖vec3EuclideanNorm (Ubar z)‖ₑ ^ qR)
      ((volume : Measure Vec3).prod μt) := hUdenMeas.aemeasurable
  have hJdenProd : AEMeasurable
      (fun z : Vec3 × ℝ => ‖vec3EuclideanNorm (Jbar z)‖ₑ ^ qR)
      ((volume : Measure Vec3).prod μt) := hJdenMeas.aemeasurable
  have hSliceIneq : ∀ᵐ t ∂μt,
      (∫⁻ x : Vec3, ‖vec3EuclideanNorm (Jbar (x, t))‖ₑ ^ qR ∂volume) ≤
      ∫⁻ x : Vec3, ‖vec3EuclideanNorm (Ubar (x, t))‖ₑ ^ qR ∂volume := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hJineq := regContract_mollified_slice_eLpNorm_le ρ ε hε u t
      (hSlice t (le_of_lt ht))
    have hJbarEq : (fun x : Vec3 => vec3EuclideanNorm (Jbar (x, t))) =ᵐ[volume]
        fun x => vec3EuclideanNorm (J (x, t)) := by
      filter_upwards [] with x
      exact congrArg vec3EuclideanNorm (hJbarPos x t ht)
    have hUbarEq : (fun x : Vec3 => vec3EuclideanNorm (Ubar (x, t))) =ᵐ[volume]
        fun x => vec3EuclideanNorm (u (x, t)) := by
      filter_upwards [] with x
      exact congrArg vec3EuclideanNorm (hUbarPos x t ht)
    have hJineqBar :
        eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Jbar (x, t))) q volume ≤
          eLpNorm (fun x : Vec3 => vec3EuclideanNorm (Ubar (x, t))) q volume := by
      rw [eLpNorm_congr_ae hJbarEq, eLpNorm_congr_ae hUbarEq]
      exact hJineq
    have hJid := regContract_eLpNorm_rpow_lintegral
      (α := Vec3) (μ := volume)
      (f := fun x : Vec3 => vec3EuclideanNorm (Jbar (x, t)))
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        ((hJbarMeas.comp measurable_prodMk_right).aestronglyMeasurable))
    have hUid := regContract_eLpNorm_rpow_lintegral
      (α := Vec3) (μ := volume)
      (f := fun x : Vec3 => vec3EuclideanNorm (Ubar (x, t)))
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        ((hUbarMeas.comp measurable_prodMk_right).aestronglyMeasurable))
    have hpow := ENNReal.rpow_le_rpow hJineqBar
      (by norm_num : (0 : ℝ) ≤ 10 / 3)
    rw [hJid, hUid] at hpow
    simpa [q, qR] using hpow
  have hJointIneq :
      (∫⁻ z : ParabolicPoint,
        ‖vec3EuclideanNorm (Jbar z)‖ₑ ^ qR ∂μ) ≤
      ∫⁻ z : ParabolicPoint,
        ‖vec3EuclideanNorm (Ubar z)‖ₑ ^ qR ∂μ := by
    rw [hJointMeasure]
    calc
      (∫⁻ z : Vec3 × ℝ,
        ‖vec3EuclideanNorm (Jbar z)‖ₑ ^ qR
          ∂((volume : Measure Vec3).prod μt)) =
        ∫⁻ t : ℝ, ∫⁻ x : Vec3,
          ‖vec3EuclideanNorm (Jbar (x, t))‖ₑ ^ qR ∂volume ∂μt := by
            rw [MeasureTheory.lintegral_prod _ hJdenProd]
            exact MeasureTheory.lintegral_lintegral_swap
              (μ := (volume : Measure Vec3)) (ν := μt)
              (f := fun x t => ‖vec3EuclideanNorm (Jbar (x, t))‖ₑ ^ qR)
              hJdenProd
      _ ≤ ∫⁻ t : ℝ, ∫⁻ x : Vec3,
          ‖vec3EuclideanNorm (Ubar (x, t))‖ₑ ^ qR ∂volume ∂μt :=
        lintegral_mono_ae hSliceIneq
      _ = ∫⁻ z : Vec3 × ℝ,
          ‖vec3EuclideanNorm (Ubar z)‖ₑ ^ qR
            ∂((volume : Measure Vec3).prod μt) := by
            rw [MeasureTheory.lintegral_prod _ hUdenProd]
            exact (MeasureTheory.lintegral_lintegral_swap
              (μ := (volume : Measure Vec3)) (ν := μt)
              (f := fun x t => ‖vec3EuclideanNorm (Ubar (x, t))‖ₑ ^ qR)
              hUdenProd).symm
  have hJid := regContract_eLpNorm_rpow_lintegral
    (α := ParabolicPoint) (μ := μ)
    (f := fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z))
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hJbarMeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self))
  have hUid := regContract_eLpNorm_rpow_lintegral
    (α := ParabolicPoint) (μ := μ)
    (f := fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z))
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
      (hUbarMeas.aestronglyMeasurable.mono_measure Measure.restrict_le_self))
  have hJbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) q μ ≤
        eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ := by
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < qR)).mp
    calc
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) q μ ^ qR =
          ∫⁻ z : ParabolicPoint,
            ‖vec3EuclideanNorm (Jbar z)‖ₑ ^ qR ∂μ := hJid
      _ ≤ ∫⁻ z : ParabolicPoint,
            ‖vec3EuclideanNorm (Ubar z)‖ₑ ^ qR ∂μ := hJointIneq
      _ = eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ ^ qR :=
          hUid.symm
  have hJbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Jbar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (J z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hJbarPos x t hz.2)
  have hUbarRawEq :
      (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) =ᵐ[μ]
        (fun z => vec3EuclideanNorm (u z)) := by
    filter_upwards [ae_restrict_mem hPmeas] with z hz
    rcases z with ⟨x, t⟩
    exact congrArg vec3EuclideanNorm (hUbarPos x t hz.2)
  have hUrawBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (u z)) q μ ≤
        3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
          eLpNorm (regUniformSpatialField a) 2 volume := by
    simpa [u, μ, P, q, regUniformPositiveTimeMeasure] using hUbound
  have hUbarBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (Ubar z)) q μ ≤
        3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
          eLpNorm (regUniformSpatialField a) 2 volume := by
    rw [eLpNorm_congr_ae hUbarRawEq]
    exact hUrawBound
  have hJrawBound :
      eLpNorm (fun z : ParabolicPoint => vec3EuclideanNorm (J z)) q μ ≤
        3 * (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
          eLpNorm (regUniformSpatialField a) 2 volume := by
    rw [← eLpNorm_congr_ae hJbarRawEq]
    exact hJbarBound.trans hUbarBound
  simpa [J, u, μ, P, q, regUniformPositiveTimeMeasure] using hJrawBound

end CKN.Leray

end
