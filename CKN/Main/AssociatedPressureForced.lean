-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedProvider

/-!
# Forced associated pressure

The proof of `thm:assoc-pressure-forced`: the pressure `p = P[u ⊗ u] + p_f`,
with `p_f` the force pressure of `lem:force-pressure` for the force on the
slab, satisfies the momentum identity against every compactly supported test.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- `thm:assoc-pressure-forced`: the finite-time forced pressure split through
the Riesz operators and the force pressure of `lem:force-pressure`. -/
theorem associatedPressureForced :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ f : ParabolicPoint → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      CKN.IsForcedLerayHopfSolution T a f u Du →
      ∃ hN : ∀ i j : Fin 3,
        MemLp (CKN.forcedQuadraticTensor T u i j)
          (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint),
        let pN : ParabolicPoint → ℝ :=
          CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
            (CKN.forcedQuadraticTensor T u) hN
        ∃ pf : ParabolicPoint → ℝ,
          AEStronglyMeasurable pf
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
          (∫⁻ t in Ioo 0 T,
            eLpNorm (fun x : Vec3 => pf (x, t)) (ENNReal.ofReal (6 : ℝ))
              (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ⊤ ∧
          (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
            ∃ hf : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume,
              HasWeakGradientOn (Set.univ : Set Vec3)
                (fun x : Vec3 => pf (x, t))
                (fun x i => CKN.Leray.forcePressureGradientFunction
                  (fun y : Vec3 => f (y, t)) hf x i)) ∧
          let p : ParabolicPoint → ℝ := pN + pf
          MemLp pN (ENNReal.ofReal (5 / 3 : ℝ))
            (volume.restrict
              (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
          (∀ Ω' J, localBox (Set.univ : Set Vec3) (Ioo 0 T) Ω' J →
            localLp (spaceTimeSet Ω' J) (3 / 2 : ℝ) p) ∧
          (∀ φ : ParabolicPoint → Vec3,
            φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
            ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
                - ∑ i : Fin 3, ∑ j : Fin 3,
                    u z i * u z j * spatialPartial (fun y => φ y i) j z
                + ∑ i : Fin 3, ∑ j : Fin 3,
                    Du z i j * spatialPartial (fun y => φ y i) j z
                - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
                - ∑ i : Fin 3, f z i * φ z i = 0) := by
  intro T a f u Du hF
  have hT : 0 < T := hF.1
  have hf2 := hF.2.2.1
  have hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint) :=
    fun i j => CKN.Leray.forcedAssociatedPressure_tensor_memLp_fiveThirds hF i j
  obtain ⟨hmeas, hL6, hgradF, hcpt, hlocbox, G, hG, hgrad, hres⟩ :=
    CKN.Leray.forcedAssociatedPressureForcePressure_spec hT hf2
  refine ⟨hN, ?_⟩
  intro pN
  refine ⟨CKN.Leray.forcedAssociatedPressureForcePressure hf2, hmeas, hL6, hgradF, ?_⟩
  intro p
  refine ⟨CKN.Leray.forcedAssociatedPressure_rieszPressure_memLp_slab hN, ?_, ?_⟩
  · intro Ω' J hbox
    exact (CKN.Leray.forcedAssociatedPressure_rieszPressure_local_threeHalves hbox hN).add
      (hlocbox Ω' J hbox)
  · intro φ hφ
    exact CKN.Leray.forcedAssociatedPressure_momentum_of_forcePressure hF hN
      (CKN.Leray.forcedAssociatedPressureForcePressure hf2) G hcpt hG hgrad hres φ hφ

end CKN.Main
