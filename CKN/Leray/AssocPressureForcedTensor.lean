-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.ForcedQuadraticTensor
public import CKN.Statements.IsForcedLerayHopfSolution
public import CKN.Leray.AssocPressureForcedEnergy
public import CKN.Leray.AssocPressureMixedNorm
public import CKN.Leray.Support.SerrinPairingLimit

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

private theorem forcedAssociatedPressure_velocity_memLp_three_halves_prep
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) :
    MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have huTen0 := forcedAssociatedPressure_velocity_memLp_tenThirds hF
  rcases hF with ⟨_, _, _, huMeas, _, _, hJointTop, _, _, _, _, _, _⟩
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have huSquare : (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    apply lt_of_le_of_lt _ hJointTop
    exact lintegral_mono fun z => le_add_right le_rfl
  have hu2 : MemLp u 2 (volume.restrict Q) :=
    associatedPressure_memLp_two_of_lintegral_lt_top huMeas huSquare
  have huTen : MemLp u (ENNReal.ofReal (10 / 3 : ℝ)) (volume.restrict Q) := by
    simpa [Q] using huTen0
  have h2le : (2 : ℝ≥0∞) ≤ (3 : ℝ≥0∞) := by norm_num
  have h3le : (3 : ℝ≥0∞) ≤ ENNReal.ofReal (10 / 3 : ℝ) := by norm_num
  exact CKN.serrin_memLp_interpolate (by norm_num) ENNReal.ofReal_ne_top h2le h3le
    hu2 huTen

private theorem forcedAssociatedPressure_tensor_memLp_on_slab
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) (i j : Fin 3) :
    MemLp (fun z : ParabolicPoint => u z i * u z j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hu3 := forcedAssociatedPressure_velocity_memLp_three_halves_prep hF
  have hi : MemLp (fun z : ParabolicPoint => u z i) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hu3) i
  have hj : MemLp (fun z : ParabolicPoint => u z j) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hu3) j
  have : ENNReal.HolderTriple 3 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
    have hh : Real.HolderTriple (3 : ℝ) 3 (3 / 2 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using hh.ennrealOfReal
  have hprod : MemLp (fun z : ParabolicPoint => u z i * u z j)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hfun : (fun z : ParabolicPoint => u z i * u z j) =
        (fun z => u z i) * (fun z => u z j) := by funext z; rfl
    rw [hfun]
    exact hi.mul hj
  exact hprod

/-- Every component of the forced zero-extended quadratic tensor belongs to
space-time `L^(5/3)`, the input required by `def:riesz-pressure`. -/
theorem forcedAssociatedPressure_tensor_memLp_fiveThirds
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) (i j : Fin 3) :
    MemLp (CKN.forcedQuadraticTensor T u i j)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint) := by
  have hTen := forcedAssociatedPressure_velocity_memLp_tenThirds hF
  have hi : MemLp (fun z : ParabolicPoint => u z i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hTen) i
  have hj : MemLp (fun z : ParabolicPoint => u z j) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    (memLp_pi_iff.mp hTen) j
  have : ENNReal.HolderTriple (ENNReal.ofReal (10 / 3 : ℝ))
      (ENNReal.ofReal (10 / 3 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ)) := by
    have hh : Real.HolderTriple (10 / 3 : ℝ) (10 / 3 : ℝ) (5 / 3 : ℝ) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using hh.ennrealOfReal
  have hproduct : MemLp (fun z : ParabolicPoint => u z i * u z j)
      (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hfun : (fun z : ParabolicPoint => u z i * u z j) =
        (fun z => u z i) * (fun z => u z j) := by funext z; rfl
    rw [hfun]
    exact hi.mul hj
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hQ : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hglobal : MemLp (Q.indicator (fun z : ParabolicPoint => u z i * u z j))
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint) :=
    (memLp_indicator_iff_restrict hQ).2 (by simpa [Q] using hproduct)
  have hEq : CKN.forcedQuadraticTensor T u i j =
      Q.indicator (fun z : ParabolicPoint => u z i * u z j) := by
    funext z
    rcases z with ⟨x, t⟩
    let z' : ParabolicPoint := (x, t)
    by_cases ht : t ∈ Ioo 0 T
    · have htQ : z' ∈ Q := by
        change x ∈ (Set.univ : Set Vec3) ∧ t ∈ Ioo 0 T
        exact ⟨Set.mem_univ x, ht⟩
      change (if t ∈ Ioo 0 T then u z' i * u z' j else 0) =
        Q.indicator (fun z : ParabolicPoint => u z i * u z j) z'
      rw [Set.indicator_of_mem htQ]
      simp only [ite_eq_left ht]
    · have hnQ : z' ∉ Q := by
        change ¬ (x ∈ (Set.univ : Set Vec3) ∧ t ∈ Ioo 0 T)
        exact fun hm => ht hm.2
      change (if t ∈ Ioo 0 T then u z' i * u z' j else 0) =
        Q.indicator (fun z : ParabolicPoint => u z i * u z j) z'
      rw [Set.indicator_of_notMem hnQ]
      simp only [ite_eq_right ht]
  rw [hEq]
  exact hglobal

/-- The same quadratic tensor has space-time `L^(3/2)` integrability, used
when testing the canonical pressure against a compactly supported Laplacian. -/
theorem forcedAssociatedPressure_tensor_memLp_threeHalves
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du) (i j : Fin 3) :
    MemLp (CKN.forcedQuadraticTensor T u i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure ParabolicPoint) := by
  have hprod := forcedAssociatedPressure_tensor_memLp_on_slab hF i j
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  have hQ : MeasurableSet Q := by
    dsimp [Q, spaceTimeSet]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioo
  have hglobal : MemLp (Q.indicator (fun z : ParabolicPoint => u z i * u z j))
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume : Measure ParabolicPoint) :=
    (memLp_indicator_iff_restrict hQ).2 (by simpa [Q] using hprod)
  have hEq : CKN.forcedQuadraticTensor T u i j =
      Q.indicator (fun z : ParabolicPoint => u z i * u z j) := by
    funext z
    rcases z with ⟨x, t⟩
    let z' : ParabolicPoint := (x, t)
    by_cases ht : t ∈ Ioo 0 T
    · have htQ : z' ∈ Q := by
        change x ∈ (Set.univ : Set Vec3) ∧ t ∈ Ioo 0 T
        exact ⟨Set.mem_univ x, ht⟩
      change (if t ∈ Ioo 0 T then u z' i * u z' j else 0) =
        Q.indicator (fun z : ParabolicPoint => u z i * u z j) z'
      rw [Set.indicator_of_mem htQ]
      simp only [ite_eq_left ht]
    · have hnQ : z' ∉ Q := by
        change ¬ (x ∈ (Set.univ : Set Vec3) ∧ t ∈ Ioo 0 T)
        exact fun hm => ht hm.2
      change (if t ∈ Ioo 0 T then u z' i * u z' j else 0) =
        Q.indicator (fun z : ParabolicPoint => u z i * u z j) z'
      rw [Set.indicator_of_notMem hnQ]
      simp only [ite_eq_right ht]
  rw [hEq]
  exact hglobal

end CKN.Leray

end
