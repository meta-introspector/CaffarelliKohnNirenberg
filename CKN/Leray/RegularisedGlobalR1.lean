-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedGlobalMild
public import CKN.Leray.RegularisedMildInitialData
public import CKN.Leray.FourierMildLocalParameters
public import CKN.Leray.RegUniformEnergy
public import CKN.Leray.FourierCoordinateL2Bridge
public import CKN.Leray.FourierMildLocalSolution
public import CKN.Leray.FourierMildLocalMap
public import CKN.Leray.FourierMollifierContraction
public import CKN.Leray.FourierMildNonlinearity
public import CKN.Leray.LerayHopfLimitPropEnergy

/-!
# Global L² trace of the regularized mild solution

The coordinate representative of the global mild curve has the spatial
L² continuity, initial trace, and weak divergence properties in (R1).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The coordinate field of the global zero-force mild curve. -/
def regularizedGlobalMildField
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    ParabolicPoint → Vec3 := fun z =>
  realVectorL2Representative
    (regularizedGlobalMildCurve ρ ε hε b hb z.2) z.1

/-- The global mild field has continuous divergence-free spatial L² slices
and satisfies its own Duhamel identity at all nonnegative times. -/
theorem regularizedGlobalMildField_R1_and_mild
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (b : RealVectorL2) (hb : RegularizedMildJData b) :
    let u := regularizedGlobalMildField ρ ε hε b hb
    ∃ hSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        realVectorL2Representative b ∧
      (∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2
        (fun x : Vec3 => u (x, t))) ∧
      (∀ t : ℝ, ∀ ht : 0 ≤ t,
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t)) (hSlice t ht) =
          realHeatOperator t ht b -
            regularizedMildStokesIntegral
              (regularizedMildTensorTrajectory ρ ε hε
                (regularizedGlobalMildCurve ρ ε hε b hb)) t) := by
  dsimp only
  let u := regularizedGlobalMildField ρ ε hε b hb
  let hSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume :=
    fun t ht => (regularizedGlobalMildCurve_mildJData ρ ε hε b hb t ht).1
  have hRep (t : ℝ) (ht : 0 ≤ t) :
      realVectorL2OfCoordinateFunction
        (fun x : Vec3 => u (x, t)) (hSlice t ht) =
        regularizedGlobalMildCurve ρ ε hε b hb t := by
    simpa only [u, regularizedGlobalMildField] using
      realVectorL2OfCoordinateFunction_representation
        (regularizedGlobalMildCurve ρ ε hε b hb t)
  refine ⟨hSlice, ?_, ?_, ?_, ?_⟩
  · have hcont : Continuous (fun t : Set.Ici (0 : ℝ) =>
        regularizedGlobalMildCurve ρ ε hε b hb t.1) :=
      (regularizedGlobalMildCurve_continuous ρ ε hε b hb).comp
        continuous_subtype_val
    convert hcont using 1
    funext t
    exact hRep t.1 t.2
  · change realVectorL2Representative
      (regularizedGlobalMildCurve ρ ε hε b hb 0) =ᵐ[volume]
      realVectorL2Representative b
    rw [regularizedGlobalMildCurve_zero ρ ε hε b hb]
  · intro t ht
    exact CKN.isInJ_weakDivFree
      (regularizedGlobalMildCurve_mildJData ρ ε hε b hb t ht)
  · intro t ht
    rw [hRep t ht]
    exact regularizedGlobalMildCurve_mild ρ ε hε b hb t ht

/-- Mollified Leray data give the global spatial L² trace and initial
condition required in (R1). -/
theorem regUniformMollifiedInitial_globalR1
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) :
    let b := realVectorL2OfCoordinateFunction
      (regUniformMollifiedInitial ρ ε hε a)
      (regMollifiedInitial_isInJ ρ ε hε ha).1
    let u := regularizedGlobalMildField ρ ε hε b
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)
    ∃ hSlice : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2
        (fun x : Vec3 => u (x, t)) := by
  dsimp only
  let b := realVectorL2OfCoordinateFunction
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1
  obtain ⟨hSlice, hCont, hInit, hDiv, -⟩ :=
    regularizedGlobalMildField_R1_and_mild ρ ε hε b
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)
  refine ⟨hSlice, hCont, ?_, hDiv⟩
  exact hInit.trans (realVectorL2OfCoordinateFunction_rep
    (regUniformMollifiedInitial ρ ε hε a)
    (regMollifiedInitial_isInJ ρ ε hε ha).1)

end CKN.Leray

end
