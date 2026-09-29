-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegEquicontinuitySourceIncrement

/-!
# `lem:reg-equicontinuity` in source form

For every `w ∈ C_c^∞(ℝ³;ℝ³)`, every `0 < ε ≤ 1` and every `0 ≤ s < t`,
`|∫ (u_ε(t) - u_ε(s))·w| ≤ C(A) N(w) |t - s|^{2/5}` with
`N(w) = ‖w‖₂ + ‖Δw‖₂ + ‖∇w‖_∞ + ‖∇w‖_{5/2}`, `A = ‖a‖₂` and
`C(A) = C₀ (A + A²)`, where `C₀` depends only on the Gagliardo–Nirenberg and
Calderón–Zygmund constants.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Integrals of double sums of integrable functions. -/
private theorem regEquiSrc_integral_double_sum {a b : Fin 3 → Fin 3 → Vec3 → ℝ}
    (ha : ∀ i j, Integrable (a i j) volume) (hb : ∀ i j, Integrable (b i j) volume) :
    ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, (a i j x + b i j x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((∫ x, a i j x) + ∫ x, b i j x) := by
  have hab : ∀ i j, Integrable (fun x => a i j x + b i j x) volume := fun i j =>
    (ha i j).add (hb i j)
  have hsum : ∀ i, Integrable (fun x => ∑ j : Fin 3, (a i j x + b i j x)) volume := fun i =>
    integrable_finsetSum _ fun j _ => hab i j
  rw [integral_finsetSum _ fun i _ => hsum i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hab i j]
  exact Finset.sum_congr rfl fun j _ => integral_add (ha i j) (hb i j)

/-- A bound for the first derivatives of a test field by the supremum of its
differential. -/
theorem regEquiSrc_deriv_le {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwc : HasCompactSupport w) (i j : Fin 3) (x : Vec3) :
    |spatialDeriv (fun y => w y i) j x| ≤ ⨆ y, ‖fderiv ℝ w y‖ := by
  have hbddD : BddAbove (Set.range fun y => ‖fderiv ℝ w y‖) :=
    ((hw.continuous_fderiv (by simp)).norm).bddAbove_range_of_hasCompactSupport
      (hwc.fderiv (𝕜 := ℝ)).norm
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
    _ ≤ ⨆ y, ‖fderiv ℝ w y‖ := le_ciSup hbddD x

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


/-- The flux of a positive time slice is bounded by
`A_E Σᵢ ‖Δwᵢ‖₂ + 9 A_E² ‖∇w‖_∞`. -/
theorem regEquiSrc_flux_slice_bound
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
    (w : Vec3 → Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    {r : ℝ} (hr : 0 < r) :
    |∫ x, forcedHopfPairingFlux
        (regUniformMollifiedVelocity ρ ε hε (uε a ha ε)) (uε a ha ε) (fun _ => 0)
        (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z)
        (fun i y => w y i) (x, r)| ≤
      (eLpNorm (regUniformSpatialField a) 2 volume).toReal *
          (∑ i : Fin 3, (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) +
        9 * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2 *
          (⨆ y, ‖fderiv ℝ w y‖) := by
  obtain ⟨⟨hSlice, -⟩, -, -, -, -, -, -, hC1, -⟩ := hregularised a ha ε hε
  have regEquiSrc_integrable_mul_test : ∀ {f g : Vec3 → ℝ}, Continuous f → Continuous g →
      HasCompactSupport g → Integrable (fun x => f x * g x) volume :=
    fun hf hg hgc => (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left
  set U := uε a ha ε with hU_def
  set J := regUniformMollifiedVelocity ρ ε hε U with hJ_def
  set AE := (eLpNorm (regUniformSpatialField a) 2 volume).toReal with hAE_def
  set G := ⨆ y, ‖fderiv ℝ w y‖ with hG_def
  have hAE : 0 ≤ AE := ENNReal.toReal_nonneg
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (regEquiSrc_deriv_le hw hwc 0 0 0)
  let wc : Fin 3 → Vec3 → ℝ := fun i y => w y i
  have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i) := fun i => (contDiff_apply ℝ ℝ i).comp hw
  have hwic : ∀ i, HasCompactSupport (wc i) := fun i => hwc.comp_left (g := fun v : Vec3 => v i) rfl
  have hdw : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (wc i) j) := fun i j =>
    CKN.contDiff_spatialDeriv_smooth (hwi i) j
  have hdwc : ∀ i j, HasCompactSupport (spatialDeriv (wc i) j) := fun i j =>
    (hwic i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hddwc : ∀ i j, HasCompactSupport (spatialDeriv (spatialDeriv (wc i) j) j) := fun i j =>
    (hdwc i j).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  -- slice regularity
  have hC1s := lerayLimit_contDiff_spatial_slices U
    (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) hC1 (fun _ hτ _ => ⟨Set.mem_univ _, hτ⟩)
    r hr
  have hUc : ∀ i, Continuous (fun x => U (x, r) i) := fun i => (hC1s i).continuous
  have hDc : ∀ i j, Continuous (fun x => spatialPartial (fun y => U y i) j (x, r)) :=
    fun i j => ((hC1s i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hJc : ∀ j, Continuous (fun x => J (x, r) j) := by
    intro j
    have h := regUniform_mollified_velocity_continuousOn ρ ε hε (u := U)
      (S := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) (fun t ht => hSlice t ht.le) hC1
      (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩) j
    exact h.comp_continuous (continuous_id.prodMk continuous_const)
      (fun x => ⟨Set.mem_univ _, hr⟩)
  -- integration by parts in each coordinate
  have hIBP : ∀ i j, ∫ x, U (x, r) i * spatialDeriv (spatialDeriv (wc i) j) j x =
      -∫ x, spatialPartial (fun y => U y i) j (x, r) * spatialDeriv (wc i) j x := by
    intro i j
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun x => U (x, r) i) (g := spatialDeriv (wc i) j) (v := CKN.basisVec j)
      (regEquiSrc_integrable_mul_test (hDc i j) (hdw i j).continuous (hdwc i j))
      (regEquiSrc_integrable_mul_test (hUc i)
        (CKN.contDiff_spatialDeriv_smooth (hdw i j) j).continuous (hddwc i j))
      (regEquiSrc_integrable_mul_test (hUc i) (hdw i j).continuous (hdwc i j))
      (fun x _ => ((hC1s i).differentiable (by simp)).differentiableAt)
      (fun x _ => ((hdw i j).differentiable (by simp)).differentiableAt)
  -- the flux as the source form
  have hflux : ∫ x, forcedHopfPairingFlux J U (fun _ => 0)
      (fun z i j => spatialPartial (fun y => U y i) j z) wc (x, r) =
      ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
        (U (x, r) i * spatialDeriv (spatialDeriv (wc i) j) j x +
          U (x, r) i * J (x, r) j * spatialDeriv (wc i) j x) := by
    have hA : ∀ i j, Integrable (fun x => -(spatialPartial (fun y => U y i) j (x, r) *
        spatialDeriv (wc i) j x)) volume := fun i j =>
      (regEquiSrc_integrable_mul_test (hDc i j) (hdw i j).continuous (hdwc i j)).neg
    have hB : ∀ i j, Integrable (fun x => U (x, r) i * J (x, r) j *
        spatialDeriv (wc i) j x) volume := fun i j =>
      regEquiSrc_integrable_mul_test ((hUc i).mul (hJc j)) (hdw i j).continuous (hdwc i j)
    have hA' : ∀ i j, Integrable (fun x => U (x, r) i *
        spatialDeriv (spatialDeriv (wc i) j) j x) volume := fun i j =>
      regEquiSrc_integrable_mul_test (hUc i)
        (CKN.contDiff_spatialDeriv_smooth (hdw i j) j).continuous (hddwc i j)
    have h1 : ∫ x, forcedHopfPairingFlux J U (fun _ => 0)
        (fun z i j => spatialPartial (fun y => U y i) j z) wc (x, r) =
        ∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          (-(spatialPartial (fun y => U y i) j (x, r) * spatialDeriv (wc i) j x) +
            U (x, r) i * J (x, r) j * spatialDeriv (wc i) j x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [forcedHopfPairingFlux, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        add_zero]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h1, regEquiSrc_integral_double_sum hA hB, regEquiSrc_integral_double_sum hA' hB]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hIBP i j, integral_neg]
  rw [hflux]
  refine regEquiSrc_pairing_rhs_bound AE G hAE hG0 (fun i x => U (x, r) i)
    (fun j x => J (x, r) j) (fun i => regEquiSrc_slice_component ρ uε pε hregularised
      a ha ε hε r hr.le i)
    (fun j => regEquiSrc_transport_component ρ uε pε hregularised a ha ε hε r hr.le j)
    wc hwi hwic (fun i j x => regEquiSrc_deriv_le hw hwc i j x)

/-- The increment bound with the linear and the `2/5` terms. -/
theorem regEquiSrc_increment_le
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
    (w : Vec3 → Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    |(∫ x, ∑ i : Fin 3, uε a ha ε (x, t) i * w x i) -
        (∫ x, ∑ i : Fin 3, uε a ha ε (x, s) i * w x i)| ≤
      (t - s) * ((eLpNorm (regUniformSpatialField a) 2 volume).toReal *
          (∑ i : Fin 3, (eLpNorm (spatialLaplacian (fun y => w y i)) 2 volume).toReal) +
        9 * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2 *
          (⨆ y, ‖fderiv ℝ w y‖)) +
      regEquiSrcPressureConstant * (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2 *
        (eLpNorm (fun x => ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x)
          (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal * (t - s) ^ (2 / 5 : ℝ) := by
  obtain ⟨hI1, hI2, heq⟩ := regEquiSrc_pairing_increment ρ uε pε hregularised a ha ε hε w hw hwc
    hs hst
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t)
      (f := fun r => ∫ x, forcedHopfPairingFlux
        (regUniformMollifiedVelocity ρ ε hε (uε a ha ε)) (uε a ha ε) (fun _ => 0)
        (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z)
        (fun i y => w y i) (x, r))
      (fun r hr => by
        rw [uIoc_of_le hst.le] at hr
        rw [Real.norm_eq_abs]
        exact regEquiSrc_flux_slice_bound ρ uε pε hregularised a ha ε hε w hw hwc
          (lt_of_le_of_lt hs hr.1))
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.2 hst)] at hbound
    linarith only [hbound]
  · obtain ⟨hp, hP⟩ := regEquiSrc_pressure_bound ρ uε pε hregularised a ha ε hε
    have hg : MemLp (fun x => ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x)
        (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
      have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => w y i) := fun i =>
        (contDiff_apply ℝ ℝ i).comp hw
      refine Continuous.memLp_of_hasCompactSupport ?_ ?_
      · exact continuous_finsetSum _ fun i _ =>
          (CKN.contDiff_spatialDeriv_smooth (hwi i) i).continuous
      · refine HasCompactSupport.intro hwc fun x hx => ?_
        exact Finset.sum_eq_zero fun i _ => (regEquiSrc_test_zero hx i i).2
    have hP0 : 0 ≤ regEquiSrcPressureConstant *
        (eLpNorm (regUniformSpatialField a) 2 volume).toReal ^ 2 :=
      mul_nonneg regEquiSrcPressureConstant_nonneg (sq_nonneg _)
    exact regEquiSrc_interval_pressure_bound hp _ hP0 hP hg hs hst

end CKN.Leray

end
