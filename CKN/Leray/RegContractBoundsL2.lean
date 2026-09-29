-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.LerayAssemblyContracts
public import CKN.Leray.RegPressureL2
public import CKN.Statements.SpaceTimeSet

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The R4 pressure of a regularized solution satisfies the source L² estimate
in `lem:reg-pressure-L2`. -/
theorem regContract_regPressure_slice_L2_bound
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
      (hε : 0 < ε),
      let u := uε a ha ε
      let p := pε a ha ε
      let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
        spatialPartial (fun y => u y i) j z
      let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
        spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
      let Dt : ParabolicPoint → Vec3 := fun z i =>
        timePartial (fun y => u y i) z
      let Dp : ParabolicPoint → Vec3 := fun z i =>
        spatialPartial (fun y => p y) i z
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
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
            (∀ i, |Dt z i| ≤ C) ∧
            (∀ i, |Dp z i| ≤ C)) ∧
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
            CKN.Leray.regUniformMollifiedVelocity ρ ε hε u z j * D z i j) +
          Dp z i = 0) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
          2 * CKN.Leray.regUniformDissipation u D t =
            eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (t : ℝ) (ht : 0 < t) :
    ∃ hp : MemLp (fun x : Vec3 => pε a ha ε (x, t))
        (ENNReal.ofReal (2 : ℝ)) volume,
      ‖hp.toLp (fun x : Vec3 => pε a ha ε (x, t))‖ ≤
        9 * rieszPressureOperatorBound (2 : ℝ) (by norm_num) *
          (eLpNorm (fun x : Vec3 =>
            vec3EuclideanNorm (regUniformMollifiedVelocity ρ ε hε
              (uε a ha ε) (x, t))) (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm (fun x : Vec3 =>
            vec3EuclideanNorm (uε a ha ε (x, t)))
              (ENNReal.ofReal (4 : ℝ)) volume).toReal := by
  let u : ParabolicPoint → Vec3 := uε a ha ε
  let p : ParabolicPoint → ℝ := pε a ha ε
  rcases hregularised a ha ε hε with
    ⟨⟨hSlice, _hSliceContinuous, _hInitialAE, _hWeakDivFree⟩,
      _hUcont, _hDcont, _hDDcont, _hDtcont, _hPcont, _hDpcont,
      _hUcontDiff, _hDdiff, _hPdiff, hBounds, _hLocalLp,
      _hEquation, hPressure, _hEnergy⟩
  have hU2 : ∀ s : ℝ, 0 ≤ s →
      MemLp (regUniformVelocitySlice u s) (2 : ℝ≥0∞) volume := by
    intro s hs
    have hcoord := (hSlice s hs).comp_measurePreserving
      (PiLp.volume_preserving_ofLp (Fin 3))
    have hL2 := hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
    change MemLp (regUniformVelocitySlice u s) (2 : ℝ≥0∞) volume
    exact hL2
  have hUbound : ∀ s : ℝ, 0 < s →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec3, vec3EuclideanNorm (u (x, s)) ≤ B := by
    intro s hs
    obtain ⟨B, hB, hBbound⟩ := hBounds (s / 2) (2 * s)
      (by positivity) (by linarith only [hs])
    refine ⟨B, hB, ?_⟩
    intro x
    have hx : ((x, s) : ParabolicPoint) ∈
        spaceTimeSet (Set.univ : Set Vec3) (Icc (s / 2) (2 * s)) := by
      change x ∈ Set.univ ∧ s ∈ Set.Icc (s / 2) (2 * s)
      constructor
      · exact Set.mem_univ x
      · constructor <;> linarith only [hs]
    exact (hBbound (x, s) hx).1
  let hFchoice : ∀ (s : ℝ) (_hs : 0 < s) (i j : Fin 3),
      MemLp (fun x : Vec3 =>
        regUniformMollifiedVelocity ρ ε hε u (x, s) i * u (x, s) j)
        (ENNReal.ofReal (2 : ℝ)) volume :=
    fun s hs => Classical.choose (hPressure s hs)
  let P : ℝ → Lp ℝ (ENNReal.ofReal (2 : ℝ)) (volume : Measure Vec3) :=
    fun s => if hs : 0 < s then
      rieszPressureSlice (2 : ℝ) (by norm_num)
        (fun i j => (hFchoice s hs i j).toLp
          (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, s) i * u (x, s) j))
    else 0
  have hR4 : ∀ s : ℝ, 0 < s → ∃ F : PressureTensorLp (2 : ℝ),
      (∀ i j, (F i j : Vec3 → ℝ) =ᵐ[volume]
        regPressureTensorSlice ρ ε hε u s i j) ∧
      P s = rieszPressureSlice (2 : ℝ) (by norm_num) F := by
    intro s hs
    let F : PressureTensorLp (2 : ℝ) := fun i j =>
      (hFchoice s hs i j).toLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, s) i * u (x, s) j)
    refine ⟨F, ?_, ?_⟩
    · intro i j
      exact (hFchoice s hs i j).coeFn_toLp
    · simp [P, hs, F]
  have hBound := regPressure_slice_L2_bound
    ρ ε hε u P hU2 hUbound hR4
  let Ft : PressureTensorLp (2 : ℝ) := fun i j =>
    (hFchoice t ht i j).toLp
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i * u (x, t) j)
  have hpRep := (Classical.choose_spec (hPressure t ht)).1
  have hClassRep := rieszPressureSliceRepresentative_ae_eq
    (2 : ℝ) (by norm_num) Ft
  have hpClass : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
      (P t : Vec3 → ℝ) := by
    have hRep : (fun x : Vec3 => p (x, t)) =ᵐ[volume]
        (rieszPressureSlice (2 : ℝ) (by norm_num) Ft : Vec3 → ℝ) := by
      exact hpRep.trans hClassRep.symm
    have hP : P t = rieszPressureSlice (2 : ℝ) (by norm_num) Ft := by
      simp [P, ht, Ft]
    filter_upwards [hRep] with x hx
    exact hx.trans (congrFun (congrArg (fun q : Lp ℝ (ENNReal.ofReal (2 : ℝ))
      (volume : Measure Vec3) => (q : Vec3 → ℝ)) hP).symm x)
  have hp : MemLp (fun x : Vec3 => p (x, t))
      (ENNReal.ofReal (2 : ℝ)) volume := by
    exact (memLp_congr_ae hpClass).2 (Lp.memLp (P t))
  have hpToLp : hp.toLp (fun x : Vec3 => p (x, t)) = P t := by
    apply Lp.ext
    filter_upwards [hp.coeFn_toLp, hpClass] with x h₁ h₂
    exact h₁.trans h₂
  refine ⟨hp, ?_⟩
  rw [hpToLp]
  simpa [u] using hBound t ht

end CKN.Leray

end
