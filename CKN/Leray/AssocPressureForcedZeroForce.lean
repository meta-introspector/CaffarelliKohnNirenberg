-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.AssociatedPressureForced
public import CKN.Main.AssociatedPressure
public import CKN.Leray.ForcedZeroForce
public import CKN.Leray.RegularisedEquationZeroForcePressure

/-!
# The zero-force specialization of associated pressure

When the force vanishes, the force-pressure part of `thm:assoc-pressure-forced`
vanishes on almost every time slice. The remaining pressure is the Riesz
pressure of the velocity tensor, and the solution satisfies the hypotheses of
`thm:assoc-pressure`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The force-pressure selected by `thm:assoc-pressure-forced` is zero on
almost every spatial slice when the force vanishes. -/
theorem forcedAssociatedPressureForcePressure_zero_ae
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (fun x : Vec3 => forcedAssociatedPressureForcePressure
        (T := T) (f := fun _ : ParabolicPoint => (0 : Vec3)) MemLp.zero (x, t))
        =ᵐ[volume] fun _ => 0 := by
  have hcanonical := forcePressure_zero_ae_on_interval T hT
  have hfun : forcedAssociatedPressureForcePressure
      (T := T) (f := fun _ : ParabolicPoint => (0 : Vec3)) MemLp.zero =
      forcePressure (fun _ : ParabolicPoint => (0 : Vec3))
        CKN.isLocallySquareIntegrableForce_zero := by
    unfold forcedAssociatedPressureForcePressure
    congr 1
    · funext z
      simp
  filter_upwards [hcanonical] with t ht
  rw [hfun]
  filter_upwards [ht] with x hx
  simpa using hx

end CKN.Leray

namespace CKN.Main

/-- At zero force, the forced pressure equals its nonlinear Riesz part on
almost every spatial slice, and the same solution has the conclusions of
`thm:assoc-pressure`. -/
theorem associatedPressureForced_zero_force
    {T : ℝ} {a : Vec3 → Vec3} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a (fun _ => 0) u Du) :
    (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      (fun x : Vec3 => CKN.Leray.forcedAssociatedPressureForcePressure
        (T := T) (f := fun _ : ParabolicPoint => (0 : Vec3)) MemLp.zero (x, t))
        =ᵐ[volume] fun _ => 0) ∧
    (∃ hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint),
      ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        (fun x : Vec3 =>
          CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (CKN.forcedQuadraticTensor T u) hN (x, t) +
          CKN.Leray.forcedAssociatedPressureForcePressure
            (T := T) (f := fun _ : ParabolicPoint => (0 : Vec3)) MemLp.zero (x, t)) =ᵐ[volume]
        (fun x : Vec3 =>
          CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (CKN.forcedQuadraticTensor T u) hN (x, t))) ∧
    (∃ p : ParabolicPoint → ℝ,
      MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) ∧
      (essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
        essSup
          (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤)) := by
  have hLH : CKN.IsLerayHopfSolution T a u Du :=
    (CKN.forced_lerayHopf_zero_iff_lerayHopf T a u Du).1 hF
  have hzero := CKN.Leray.forcedAssociatedPressureForcePressure_zero_ae
    (T := T) hF.1
  obtain ⟨hN, _hforced⟩ := CKN.Main.associatedPressureForced T a
    (fun _ : ParabolicPoint => (0 : Vec3)) u Du hF
  have hUnforced := CKN.Main.associatedPressure T a u Du hLH
  refine ⟨hzero, ⟨hN, ?_⟩, hUnforced⟩
  ·
    filter_upwards [hzero] with t ht
    filter_upwards [ht] with x hx
    simp [hx]

end CKN.Main

end
