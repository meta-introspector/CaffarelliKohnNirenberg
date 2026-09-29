-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureMixedNorm

/-!
# The quantitative mixed norm of the associated pressure

The canonical pressure obeys the slice-wise quadratic estimate in
`lem:assoc-pressure-L3`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The canonical pressure satisfies the quantitative estimate in
`lem:assoc-pressure-L3`; the factor nine counts the spatial tensor components. -/
theorem associatedPressureForSolution_l3_mixed_bound
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hL3 : essSup
      (fun t : ℝ => eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume)
      (volume.restrict (Ioo 0 T)) < ⊤) :
    essSup
      (fun t : ℝ => eLpNorm
        (fun x : Vec3 => associatedPressureForSolution hLH (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      (volume.restrict (Ioo 0 T)) ≤
    ENNReal.ofReal (9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
      (essSup
        (fun t : ℝ => eLpNorm
          (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal (3 : ℝ)) volume)
        (volume.restrict (Ioo 0 T))).toReal ^ 2) := by
  classical
  let M : ℝ≥0∞ := essSup
    (fun t : ℝ => eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (3 : ℝ)) volume)
    (volume.restrict (Ioo 0 T))
  have hMtop : M < ⊤ := by simpa [M] using hL3
  have hF5 : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_fiveThirds hLH i j
  have hF3 : ∀ i j, MemLp (associatedPressureTensor T u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    exact associatedPressureTensor_memLp_threeHalves hLH i j
  have hPressureEqGlobal :=
    associatedPressureForSolution_rieszPressureThreeHalves_ae_eq hLH
  have hPressureEqSlab :
      (fun z : Vec3 × ℝ => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH) z) =ᵐ[
          volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))]
      fun z : Vec3 × ℝ => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_threeHalves hLH) z :=
    ae_restrict_of_ae hPressureEqGlobal
  have hPressureEqProd :
      (fun z : Vec3 × ℝ => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH) z) =ᵐ[
          (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))]
      fun z : Vec3 × ℝ => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_threeHalves hLH) z := by
    have hmeasure' :
        (volume : Measure ParabolicPoint).restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
          ((volume : Measure Vec3).restrict Set.univ).prod
            ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      rfl
    have hmeasure :
        (volume : Measure ParabolicPoint).restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) =
          (volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)) := by
      simpa only [Measure.restrict_univ] using hmeasure'
    rw [← hmeasure]
    exact hPressureEqSlab
  have hPressureEqTime : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)) =ᵐ[volume]
      fun x : Vec3 => rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (associatedPressureTensor T u)
        (associatedPressureTensor_memLp_threeHalves hLH) (x, t) := by
    have hswap := (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ).restrict (Ioo 0 T))
      (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hPressureEqProd
    exact Measure.ae_ae_of_ae_prod hswap
  have hPressure3Slice := ae_restrict_of_ae (s := Ioo 0 T)
    (rieszPressureSpaceTime_slice_ae_eq
      (r := (3 / 2 : ℝ)) (by norm_num) (associatedPressureTensor T u) hF3)
  have huMeas : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    simpa using hLH.2.2.1
  have huProd : AEStronglyMeasurable u
      ((volume.restrict (Set.univ : Set Vec3)).prod
        (volume.restrict (Ioo 0 T))) := by
    rw [Measure.prod_restrict Set.univ (Ioo 0 T)]
    exact huMeas
  have huSliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      AEStronglyMeasurable (fun x : Vec3 => u (x, t)) volume := by
    filter_upwards [huProd.prodMk_right] with t hmeas
    simpa only [Measure.restrict_univ] using hmeas
  have hVelocity3 : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
    filter_upwards [ae_le_essSup (f := fun t : ℝ =>
      eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume)] with t ht
    exact ht
  have hPressureFact : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) := ⟨by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  have hPressureHolder : ENNReal.HolderTriple (ENNReal.ofReal (3 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have h : Real.HolderTriple (3 : ℝ) 3 (3 / 2 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    exact h.ennrealOfReal
  have hBound : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      eLpNorm (fun x : Vec3 => associatedPressureForSolution hLH (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
      ENNReal.ofReal (9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
        M.toReal ^ 2) := by
    filter_upwards [hPressureEqTime, hPressure3Slice, hVelocity3,
      huSliceMeas, ae_restrict_mem measurableSet_Ioo]
      with t hPressureEqT ⟨hFt3, hP3⟩ hVel3 humeas ht
    let n : Vec3 → ℝ := fun x => vec3EuclideanNorm (u (x, t))
    have hNBound : eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
      change eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
        (ENNReal.ofReal (3 : ℝ)) volume ≤ M
      exact hVel3
    have hCoordMeas (i : Fin 3) :
        AEStronglyMeasurable (fun x : Vec3 => u (x, t) i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        humeas
    have hCoordBound (i : Fin 3) :
        eLpNorm (fun x : Vec3 => u (x, t) i)
          (ENNReal.ofReal (3 : ℝ)) volume ≤ M := by
      calc
        eLpNorm (fun x : Vec3 => u (x, t) i)
            (ENNReal.ofReal (3 : ℝ)) volume ≤
          eLpNorm n (ENNReal.ofReal (3 : ℝ)) volume := by
            apply eLpNorm_mono (hCoordMeas i)
            intro x
            rw [Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
            exact abs_apply_le_vec3EuclideanNorm (u (x, t)) i
        _ ≤ M := hNBound
    have hInputEquality (i j : Fin 3) :
        (fun x : Vec3 => associatedPressureTensor T u i j (x, t)) =ᵐ[volume]
          fun x : Vec3 => u (x, t) i * u (x, t) j := by
      filter_upwards [] with x
      have hxmem : (x, t) ∈ parabolicHomeomorph.symm ⁻¹'
          spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
        change (x, t) ∈ (Set.univ : Set Vec3) ×ˢ Ioo 0 T
        exact ⟨Set.mem_univ _, ht⟩
      simp [associatedPressureTensor, parabolicHomeomorph_symm_apply, hxmem]
    have hProductBound (i j : Fin 3) :
        eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
            (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M ^ (2 : ℕ) := by
      have hHolder :
          eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            eLpNorm (fun x : Vec3 => u (x, t) i)
                (ENNReal.ofReal (3 : ℝ)) volume *
              eLpNorm (fun x : Vec3 => u (x, t) j)
                (ENNReal.ofReal (3 : ℝ)) volume := by
        simpa only [ENNReal.coe_one, one_mul] using
          (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
            (p := ENNReal.ofReal (3 : ℝ)) (q := ENNReal.ofReal (3 : ℝ))
            (r := ENNReal.ofReal (3 / 2 : ℝ))
            (fun v w : ℝ => v * w) 1 continuous_mul (hCoordMeas i) (hCoordMeas j)
            (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs]))
      calc
        _ ≤ eLpNorm (fun x : Vec3 => u (x, t) i)
              (ENNReal.ofReal (3 : ℝ)) volume *
            eLpNorm (fun x : Vec3 => u (x, t) j)
              (ENNReal.ofReal (3 : ℝ)) volume := by simpa using hHolder
        _ ≤ M * M := mul_le_mul (hCoordBound i) (hCoordBound j)
            (by positivity) (by positivity)
        _ = M ^ (2 : ℕ) := by rw [pow_two]
    let C3 : PressureTensorLp (3 / 2 : ℝ) := fun i j =>
      (hFt3 i j).toLp (fun x : Vec3 => associatedPressureTensor T u i j (x, t))
    have hC3norm (i j : Fin 3) : ‖C3 i j‖ ≤ M.toReal ^ 2 := by
      rw [Lp.norm_toLp]
      have hRawBound :
          eLpNorm (fun x : Vec3 => associatedPressureTensor T u i j (x, t))
              (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ M ^ (2 : ℕ) := by
        calc
          _ = eLpNorm (fun x : Vec3 => u (x, t) i * u (x, t) j)
                (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
              eLpNorm_congr_ae (hInputEquality i j)
          _ ≤ M ^ (2 : ℕ) := hProductBound i j
      have hM2top : M ^ (2 : ℕ) < ⊤ := by
        simpa [pow_two] using (ENNReal.mul_lt_top hMtop hMtop)
      calc
        _ ≤ (M ^ (2 : ℕ)).toReal := ENNReal.toReal_mono hM2top.ne hRawBound
        _ = M.toReal ^ 2 := by rw [ENNReal.toReal_pow]
    have hCnonneg : 0 ≤ rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) :=
      le_trans (norm_nonneg _) (rieszPressureOperator_norm_le
        (3 / 2 : ℝ) (by norm_num) 0 0)
    have hC3sum : ∑ i : Fin 3, ∑ j : Fin 3, ‖C3 i j‖ ≤
        9 * M.toReal ^ 2 := by
      calc
        _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, M.toReal ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact hC3norm i j
        _ = 9 * M.toReal ^ 2 := by
          simp only [Finset.sum_const, Finset.card_fin]
          ring_nf
    have hPressureClassBound :
        ‖rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3‖ ≤
          rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
            (9 * M.toReal ^ 2) := by
      exact (rieszPressureSlice_norm_le
        (3 / 2 : ℝ) (by norm_num) C3).trans
        (mul_le_mul_of_nonneg_left hC3sum hCnonneg)
    let P3 : Vec3 → ℝ := rieszPressureSliceRepresentative
      (3 / 2 : ℝ) (by norm_num) C3
    have hP3rep : (rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3 :
        Vec3 → ℝ) =ᵐ[volume] P3 :=
      rieszPressureSliceRepresentative_ae_eq (3 / 2 : ℝ) (by norm_num) C3
    have hP3mem : MemLp P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      (memLp_congr_ae hP3rep).mp (Lp.memLp
        (rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3))
    have hP3class : hP3mem.toLp P3 = rieszPressureSlice
        (3 / 2 : ℝ) (by norm_num) C3 := by
      apply Lp.ext
      filter_upwards [hP3mem.coeFn_toLp, hP3rep] with x hto hclass
      exact hto.trans hclass.symm
    have hP3eLpNorm : eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
          (9 * M.toReal ^ 2)) := by
      calc
        eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume =
            ENNReal.ofReal ‖hP3mem.toLp P3‖ := by
          calc
            _ = ENNReal.ofReal (eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal :=
              (ENNReal.ofReal_toReal hP3mem.eLpNorm_lt_top.ne).symm
            _ = ENNReal.ofReal ‖hP3mem.toLp P3‖ :=
              congrArg ENNReal.ofReal (Lp.norm_toLp P3 hP3mem).symm
        _ = ENNReal.ofReal ‖rieszPressureSlice (3 / 2 : ℝ) (by norm_num) C3‖ :=
          congrArg (fun q : Lp ℝ (ENNReal.ofReal (3 / 2 : ℝ))
            (volume : Measure Vec3) => ENNReal.ofReal ‖q‖) hP3class
        _ ≤ ENNReal.ofReal (rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
            (9 * M.toReal ^ 2)) := ENNReal.ofReal_le_ofReal hPressureClassBound
    have hP5toP3 :
        (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)) =ᵐ[volume] P3 :=
      hPressureEqT.trans (hP3.trans hP3rep)
    have hpoint (x : Vec3) :
        associatedPressureForSolution hLH ((x, t) : ParabolicPoint) =
          rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (associatedPressureTensor T u)
            (associatedPressureTensor_memLp_fiveThirds hLH) (x, t) := by
      change rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
          (associatedPressureTensor T u)
          (associatedPressureTensor_memLp_fiveThirds hLH)
          (parabolicHomeomorph ((x, t) : ParabolicPoint)) = _
      rfl
    have hSolutionP :
        (fun x : Vec3 => associatedPressureForSolution hLH (x, t)) =ᵐ[volume] P3 := by
      calc
        _ =ᵐ[volume] (fun x : Vec3 => rieszPressureSpaceTime (5 / 3 : ℝ)
            (by norm_num) (associatedPressureTensor T u)
            (associatedPressureTensor_memLp_fiveThirds hLH) (x, t)) :=
          Filter.Eventually.of_forall fun x => hpoint x
        _ =ᵐ[volume] P3 := hP5toP3
    calc
      eLpNorm (fun x : Vec3 => associatedPressureForSolution hLH (x, t))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume =
        eLpNorm P3 (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
          eLpNorm_congr_ae hSolutionP
      _ ≤ ENNReal.ofReal (9 * rieszPressureOperatorBound
          (3 / 2 : ℝ) (by norm_num) * M.toReal ^ 2) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hP3eLpNorm
  change essSup
      (fun t : ℝ => eLpNorm
        (fun x : Vec3 => associatedPressureForSolution hLH (x, t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume)
      (volume.restrict (Ioo 0 T)) ≤
    ENNReal.ofReal (9 * rieszPressureOperatorBound (3 / 2 : ℝ) (by norm_num) *
      M.toReal ^ 2)
  exact essSup_le_of_ae_le _ hBound

end CKN.Leray

end
