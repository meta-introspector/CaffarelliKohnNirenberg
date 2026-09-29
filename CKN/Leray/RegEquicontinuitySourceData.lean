-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegEquicontinuitySourceBounds
public import CKN.Leray.RegTailsFinalCore
public import CKN.Leray.RegContractBoundsPressure
public import CKN.Leray.LerayLimitJConvContraction
public import CKN.Leray.Support.VorticityLocalizedEnergyMollifier

/-!
# Uniform data bounds for the regularized time modulus

Bounds with explicit dependence on `A_E = ‖a‖₂` (Euclidean `L²` norm) for the
regularized solutions of the contract, as used in `lem:reg-equicontinuity`:
- every time slice of the velocity and of the transport field has
  components of `L²` norm at most `A_E`;
- on every finite slab the velocity and the transport field are cubically
  integrable and the gradient is square integrable;
- the pressure has space-time `L^{5/3}` norm at most `K_p A_E²`
  (`lem:reg-pressure-bound`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The constant of `lem:reg-pressure-bound`. -/
def regEquiSrcPressureConstant : ℝ :=
  9 * rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) *
    ((3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)).toReal) ^ 2

theorem regEquiSrcPressureConstant_nonneg : 0 ≤ regEquiSrcPressureConstant := by
  have hOp : 0 ≤ rieszPressureOperatorBound (5 / 3 : ℝ) (by norm_num) :=
    le_trans (norm_nonneg _) <|
      rieszPressureSpaceTimeComponent_norm_le (5 / 3 : ℝ) (by norm_num) (0 : Fin 3) (0 : Fin 3)
  unfold regEquiSrcPressureConstant
  positivity

/-- A component of a vector is bounded by its Euclidean length. -/
theorem regEquiSrc_abs_le_euclid (v : Vec3) (i : Fin 3) : |v i| ≤ vec3EuclideanNorm v :=
  (norm_le_pi_norm v i).trans (norm_le_vec3EuclideanNorm v)

/-- Interpolation between `L²` and `L^{10/3}` gives `L³`. -/
private theorem regEquiSrc_memLp_three {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (h2 : MemLp f (ENNReal.ofReal (2 : ℝ)) μ)
    (hhigh : MemLp f (ENNReal.ofReal (10 / 3 : ℝ)) μ) :
    MemLp f (3 : ℝ≥0∞) μ := by
  let θ : ℝ := 1 / 6
  let β : ℝ := 5 / 6
  let f₁ : α → ℝ := fun x => ‖f x‖ ^ θ
  let f₂ : α → ℝ := fun x => ‖f x‖ ^ β
  have hθ : 0 < θ := by norm_num [θ]
  have hβ : 0 < β := by norm_num [β]
  have hsum : θ + β = 1 := by norm_num [θ, β]
  have hp₁coe : ENNReal.ofReal (12 : ℝ) = ENNReal.ofReal (2 : ℝ) / ENNReal.ofReal θ := by
    rw [← ENNReal.ofReal_div_of_pos hθ]
    norm_num [θ]
  have hp₂coe : ENNReal.ofReal (4 : ℝ) =
      ENNReal.ofReal (10 / 3 : ℝ) / ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_div_of_pos hβ]
    norm_num [β]
  have hf₁ : MemLp f₁ (ENNReal.ofReal (12 : ℝ)) μ := by
    rw [hp₁coe]
    have h := h2.norm_rpow_div (ENNReal.ofReal θ)
    simpa [f₁, θ, ENNReal.toReal_ofReal hθ.le] using h
  have hf₂ : MemLp f₂ (ENNReal.ofReal (4 : ℝ)) μ := by
    rw [hp₂coe]
    have h := hhigh.norm_rpow_div (ENNReal.ofReal β)
    simpa [f₂, β, ENNReal.toReal_ofReal hβ.le] using h
  have hT : ENNReal.HolderTriple (ENNReal.ofReal (12 : ℝ)) (ENNReal.ofReal (4 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩
  have hmul : MemLp (f₁ * f₂) (ENNReal.ofReal (3 : ℝ)) μ := hf₁.mul hf₂
  have hproduct (x : α) : f₁ x * f₂ x = ‖f x‖ := by
    show ‖f x‖ ^ θ * ‖f x‖ ^ β = ‖f x‖
    rw [← Real.rpow_add' (norm_nonneg _) (by rw [hsum]; norm_num), hsum, Real.rpow_one]
  have hnorm : MemLp (fun x => ‖f x‖) (ENNReal.ofReal (3 : ℝ)) μ :=
    (memLp_congr_ae (Filter.Eventually.of_forall hproduct)).mp hmul
  have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
  rw [← h3]
  exact (memLp_norm_iff hhigh.aestronglyMeasurable).mp hnorm


/-- A slab field with uniformly bounded slice energies is square integrable on
the slab. -/
theorem regEquiSrc_slab_two {T B : ℝ} {g : ParabolicPoint → ℝ}
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hs : ∀ τ ∈ Ioo 0 T, MemLp (fun x => g (x, τ)) 2 volume ∧ ∫ x, (g (x, τ)) ^ 2 ≤ B) :
    MemLp g 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hμ : (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)) := CKN.vlSlab_measure 0 T
  refine (memLp_two_iff_integrable_sq hg).2 ?_
  rw [hμ] at hg ⊢
  have hsqm : AEStronglyMeasurable (fun p : Vec3 × ℝ => (g p) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := hg.pow 2
  refine (integrable_prod_iff' hsqm).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    exact (hs τ hτ).1.integrable_sq
  · have hB : IntegrableOn (fun _ : ℝ => B) (Ioo 0 T) volume :=
      integrableOn_const (by simp [Real.volume_Ioo])
    refine hB.mono' hsqm.norm.prod_swap.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact (hs τ hτ).2

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


/-- The velocity slices have components of `L²` norm at most `A_E`. -/
theorem regEquiSrc_slice_component
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) (τ : ℝ) (hτ : 0 ≤ τ) (i : Fin 3) :
    MemLp (fun x => uε a ha ε (x, τ) i) 2 volume ∧
      (eLpNorm (fun x => uε a ha ε (x, τ) i) 2 volume).toReal ≤
        (eLpNorm (regUniformSpatialField a) 2 volume).toReal := by
  have hU := regTails_contract_slice_memLp ρ uε pε hregularised a ha ε hε τ hτ
  have hE := (regTails_contract_energy_bounds ρ uε pε hregularised a ha ε hε).1 τ hτ
  have hle : eLpNorm (regUniformVelocitySlice (uε a ha ε) τ) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume :=
    (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hE
  have hslice := regTails_eLpNorm_euclidean_eq_spatialField (fun x => uε a ha ε (x, τ)) hU
  have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
  have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
    rw [← hfield]
    exact (regTailsFinal_euclideanNorm_memLp ha.1).eLpNorm_ne_top
  have hcomp : eLpNorm (fun x => uε a ha ε (x, τ) i) 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (uε a ha ε (x, τ))) 2 volume := by
    refine eLpNorm_mono_real ((continuous_apply i).comp_aestronglyMeasurable hU.aestronglyMeasurable) fun x => ?_
    rw [Real.norm_eq_abs]
    exact regEquiSrc_abs_le_euclid _ i
  have hbound : eLpNorm (fun x => uε a ha ε (x, τ) i) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume := by
    refine hcomp.trans ?_
    rw [hslice]
    exact hle
  exact ⟨hU.eval i, ENNReal.toReal_mono hfin hbound⟩

/-- The transport slices have components of `L²` norm at most `A_E`. -/
theorem regEquiSrc_transport_component
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) (τ : ℝ) (hτ : 0 ≤ τ) (j : Fin 3) :
    MemLp (fun x => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) (x, τ) j) 2 volume ∧
      (eLpNorm (fun x => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) (x, τ) j) 2
        volume).toReal ≤ (eLpNorm (regUniformSpatialField a) 2 volume).toReal := by
  have hU := regTails_contract_slice_memLp ρ uε pε hregularised a ha ε hε τ hτ
  have hJ := lerayLimit_regUniformMollifiedVelocity_slice_eLpNorm_le ρ ε hε (uε a ha ε) τ
    hU.aestronglyMeasurable (p := 2) (by norm_num) (by norm_num)
  have hJmem : MemLp (fun x => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) (x, τ)) 2 volume :=
    lt_of_le_of_lt hJ hU.eLpNorm_lt_top
  have hsup : eLpNorm (fun x => uε a ha ε (x, τ)) 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (uε a ha ε (x, τ))) 2 volume := by
    refine eLpNorm_mono_real hU.aestronglyMeasurable fun x => ?_
    exact norm_le_vec3EuclideanNorm _
  have hE := (regTails_contract_energy_bounds ρ uε pε hregularised a ha ε hε).1 τ hτ
  have hle : eLpNorm (regUniformVelocitySlice (uε a ha ε) τ) 2 volume ≤
      eLpNorm (regUniformSpatialField a) 2 volume :=
    (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hE
  have hslice := regTails_eLpNorm_euclidean_eq_spatialField (fun x => uε a ha ε (x, τ)) hU
  have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
  have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
    rw [← hfield]
    exact (regTailsFinal_euclideanNorm_memLp ha.1).eLpNorm_ne_top
  have hcomp : eLpNorm (fun x => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) (x, τ) j) 2
      volume ≤ eLpNorm (fun x => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) (x, τ)) 2
        volume := by
    refine eLpNorm_mono ((continuous_apply j).comp_aestronglyMeasurable hJmem.aestronglyMeasurable) fun x => ?_
    rw [Real.norm_eq_abs]
    exact (norm_le_pi_norm _ j).trans_eq' (Real.norm_eq_abs _).symm
  refine ⟨hJmem.eval j, ENNReal.toReal_mono hfin ?_⟩
  calc _ ≤ _ := hcomp
    _ ≤ _ := hJ
    _ ≤ _ := hsup
    _ = _ := hslice
    _ ≤ _ := hle

/-- The velocity is cubically integrable on every finite slab. -/
theorem regEquiSrc_velocity_slab_three
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    MemLp (uε a ha ε) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨-, hUc, -⟩ := hregularised a ha ε hε
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    prod_mono subset_rfl Ioo_subset_Ioi_self
  have hμ : (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) ≤ regUniformPositiveTimeMeasure :=
    Measure.restrict_mono hsub le_rfl
  have hPosMeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hcm : ∀ i, AEStronglyMeasurable (fun z => uε a ha ε z i)
      regUniformPositiveTimeMeasure := fun i => (hUc i).aestronglyMeasurable hPosMeas
  have hem : AEStronglyMeasurable (fun z => vec3EuclideanNorm (uε a ha ε z))
      regUniformPositiveTimeMeasure := by
    have hv : AEStronglyMeasurable (uε a ha ε) regUniformPositiveTimeMeasure :=
      (aemeasurable_pi_iff.2 fun i => (hcm i).aemeasurable).aestronglyMeasurable
    exact CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv
  have h103 : MemLp (fun z => vec3EuclideanNorm (uε a ha ε z)) (ENNReal.ofReal (10 / 3 : ℝ))
      regUniformPositiveTimeMeasure := by
    refine lt_of_le_of_lt
      (regContract_velocity_tenThirds ρ uε pε hregularised a ha ε hε) ?_
    have hC : CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) gagliardoNirenbergSobolevConstant_ne_top
    have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
    have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
      rw [← hfield]
      exact (regTailsFinal_euclideanNorm_memLp ha.1).eLpNorm_ne_top
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC.lt_top) hfin.lt_top
  refine memLp_pi_iff.2 fun i => ?_
  have hi103 : MemLp (fun z => uε a ha ε z i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    refine (h103.of_le (hcm i) (Eventually.of_forall fun z => ?_)).mono_measure hμ
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg _)]
    exact regEquiSrc_abs_le_euclid _ i
  have hi2 : MemLp (fun z => uε a ha ε z i) (ENNReal.ofReal (2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [ENNReal.ofReal_ofNat]
    refine regEquiSrc_slab_two (B := (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2)
      ((hcm i).mono_measure hμ) fun τ hτ => ?_
    obtain ⟨hmem, hle⟩ := regEquiSrc_slice_component ρ uε pε hregularised a ha ε hε τ hτ.1.le i
    refine ⟨hmem, ?_⟩
    rw [CKN.vl_integral_sq_eq hmem]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
  exact regEquiSrc_memLp_three hi2 hi103

/-- The transport field is cubically integrable on every finite slab. -/
theorem regEquiSrc_transport_slab_three
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    MemLp (regUniformMollifiedVelocity ρ ε hε (uε a ha ε)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨⟨hSlice, -⟩, -, -, -, -, -, -, hC1, -⟩ := hregularised a ha ε hε
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    prod_mono subset_rfl Ioo_subset_Ioi_self
  have hμ : (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) ≤ regUniformPositiveTimeMeasure :=
    Measure.restrict_mono hsub le_rfl
  have hPosMeas : MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hJc := regUniform_mollified_velocity_continuousOn ρ ε hε (u := uε a ha ε)
    (S := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) (fun t ht => hSlice t ht.le) hC1
    (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hcm : ∀ i, AEStronglyMeasurable
      (fun z => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i)
      regUniformPositiveTimeMeasure := fun i => (hJc i).aestronglyMeasurable hPosMeas
  have h103 : MemLp (fun z => vec3EuclideanNorm
      (regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z)) (ENNReal.ofReal (10 / 3 : ℝ))
      regUniformPositiveTimeMeasure := by
    refine lt_of_le_of_lt
      (regContract_mollifiedVelocity_tenThirds ρ uε pε hregularised a ha ε hε) ?_
    have hC : CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) gagliardoNirenbergSobolevConstant_ne_top
    have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
    have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
      rw [← hfield]
      exact (regTailsFinal_euclideanNorm_memLp ha.1).eLpNorm_ne_top
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hC.lt_top) hfin.lt_top
  refine memLp_pi_iff.2 fun i => ?_
  have hi103 : MemLp (fun z => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i)
      (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    refine (h103.of_le (hcm i) (Eventually.of_forall fun z => ?_)).mono_measure hμ
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg _)]
    exact regEquiSrc_abs_le_euclid _ i
  have hi2 : MemLp (fun z => regUniformMollifiedVelocity ρ ε hε (uε a ha ε) z i)
      (ENNReal.ofReal (2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rw [ENNReal.ofReal_ofNat]
    refine regEquiSrc_slab_two (B := (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2)
      ((hcm i).mono_measure hμ) fun τ hτ => ?_
    obtain ⟨hmem, hle⟩ :=
      regEquiSrc_transport_component ρ uε pε hregularised a ha ε hε τ hτ.1.le i
    refine ⟨hmem, ?_⟩
    rw [CKN.vl_integral_sq_eq hmem]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
  exact regEquiSrc_memLp_three hi2 hi103

/-- The velocity gradient is square integrable on every finite slab. -/
theorem regEquiSrc_gradient_slab_two
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
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    MemLp (fun z (i j : Fin 3) => spatialPartial (fun y => uε a ha ε y i) j z) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  obtain ⟨-, -, hDc, -⟩ := hregularised a ha ε hε
  have hE := (regTails_contract_energy_bounds ρ uε pε hregularised a ha ε hε).2.1
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    prod_mono subset_rfl Ioo_subset_Ioi_self
  have hμ : (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) ≤ regUniformPositiveTimeMeasure :=
    Measure.restrict_mono hsub le_rfl
  have hPosMeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hfield := regTails_eLpNorm_euclidean_eq_spatialField a ha.1
  have hfin : eLpNorm (regUniformSpatialField a) 2 volume ≠ ⊤ := by
    rw [← hfield]
    exact (regTailsFinal_euclideanNorm_memLp ha.1).eLpNorm_ne_top
  have hlin : ∫⁻ z, ENNReal.ofReal (spatialGradientSq (uε a ha ε)
      (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z) z)
      ∂regUniformPositiveTimeMeasure < ⊤ := by
    have h2 : eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) < ⊤ :=
      ENNReal.pow_lt_top hfin.lt_top
    have h := lt_of_le_of_lt hE h2
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at h
    simp at h
  refine memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => ?_
  have hcm : AEStronglyMeasurable
      (fun z => spatialPartial (fun y => uε a ha ε y i) j z) regUniformPositiveTimeMeasure :=
    (hDc i j).aestronglyMeasurable hPosMeas
  refine MemLp.mono_measure hμ ?_
  refine (memLp_two_iff_integrable_sq hcm).2 ⟨hcm.pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => sq_nonneg _)).2 ?_
  refine lt_of_le_of_lt (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_) hlin
  unfold spatialGradientSq
  have hj := Finset.single_le_sum (f := fun j' : Fin 3 =>
    (spatialPartial (fun y => uε a ha ε y i) j' z) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)
  have hi := Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j' : Fin 3,
    (spatialPartial (fun y => uε a ha ε y i') j' z) ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact hj.trans hi

/-- `lem:reg-pressure-bound`: the pressure has space-time `L^{5/3}` norm at most
`K_p A_E²`. -/
theorem regEquiSrc_pressure_bound
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
    MemLp (pε a ha ε) (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure ∧
      eLpNorm (pε a ha ε) (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure ≤
        ENNReal.ofReal (regEquiSrcPressureConstant *
          (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2) := by
  obtain ⟨hp, hbound⟩ := regContract_regPressure_fiveThirds ρ uε pε hregularised a ha ε hε
  refine ⟨hp, ?_⟩
  have hnorm : ‖hp.toLp (pε a ha ε)‖ =
      (eLpNorm (pε a ha ε) (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure).toReal :=
    Lp.norm_toLp _ _
  have heq : (((3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) *
      eLpNorm (regUniformSpatialField a) 2 volume).toReal) ^ 2 =
      ((3 * CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)).toReal) ^ 2 *
        (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2 := by
    rw [ENNReal.toReal_mul, mul_pow]
  rw [← ENNReal.ofReal_toReal hp.eLpNorm_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hnorm]
  refine hbound.trans_eq ?_
  rw [heq, regEquiSrcPressureConstant]
  ring

end CKN.Leray

end
