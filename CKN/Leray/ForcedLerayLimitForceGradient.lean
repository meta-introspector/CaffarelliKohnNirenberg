-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcePressure
public import CKN.Leray.ForcePressureOperator
public import CKN.Leray.ForcedRegularisedRepresentative
public import CKN.Leray.ForcedRegularisedEnergyForm
public import CKN.Leray.ForcedRegularisedMildEquation

/-!
# The space-time gradient of the force pressure

`lem:force-pressure` gives, on almost every time slice, the weak gradient
`(I - ℙ) f(·, t)` of the force pressure. This file assembles these slice
gradients into one jointly measurable field: the representative of the
measurable curve `t ↦ (I - ℙ) f(t)` of real `L²` fields. It is square
integrable on every finite slab and is the weak gradient of the force pressure
on almost every time slice, which is the form used for the projected force in
`lem:forced-tails` (`eq:forced-projection-cancellation`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The curve of force-pressure gradients `t ↦ (I - ℙ) f(t)` in real `L²`. -/
def forcePressureGradientCurve (f : ParabolicPoint → Vec3)
    (hf : IsLocallySquareIntegrableForce f) (t : ℝ) : RealVectorL2 :=
  forcePressureGradientL2 (forcedForceSlice (forcedForceMod f hf) t)

theorem forcePressureGradientCurve_stronglyMeasurable (f : ParabolicPoint → Vec3)
    (hf : IsLocallySquareIntegrableForce f) :
    StronglyMeasurable (forcePressureGradientCurve f hf) := by
  have hcont : Continuous (forcePressureGradientL2 : RealVectorL2 → RealVectorL2) := by
    have heq : (forcePressureGradientL2 : RealVectorL2 → RealVectorL2) =
        fun v => forcePressureTestGradientSpan.topologicalClosure.starProjection v := by
      funext v
      exact forcePressureGradientL2_eq_starProjection v
    rw [heq]
    exact (forcePressureTestGradientSpan.topologicalClosure.starProjection).continuous
  exact hcont.comp_stronglyMeasurable
    (forcedForceSlice_stronglyMeasurable (forcedForceMod_stronglyMeasurable f hf))

/-- The jointly measurable space-time gradient of the force pressure
(`lem:force-pressure`). -/
def forcePressureGradientField (f : ParabolicPoint → Vec3)
    (hf : IsLocallySquareIntegrableForce f) : ParabolicPoint → Vec3 :=
  forcedCurveRep (forcePressureGradientCurve f hf)
    (forcePressureGradientCurve_stronglyMeasurable f hf)

/-- The space-time gradient of the force pressure from `lem:force-pressure`:
it is jointly measurable and square integrable on every finite slab, and on
almost every time slice it is the pointwise force-pressure gradient
`(I - ℙ) f(·, t)` and the weak gradient of the force pressure. -/
theorem forcePressureGradientField_spec (f : ParabolicPoint → Vec3)
    (hf : IsLocallySquareIntegrableForce f) :
    StronglyMeasurable (forcePressureGradientField f hf) ∧
    ∀ T : ℝ, 0 < T →
      MemLp (forcePressureGradientField f hf) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        (∃ hft : MemLp (fun x : Vec3 => f (x, t)) 2 volume,
          (fun x => forcePressureGradientField f hf (x, t)) =ᵐ[volume]
            forcePressureGradientFunction (fun y : Vec3 => f (y, t)) hft) ∧
        HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, t))
          (fun x => forcePressureGradientField f hf (x, t)) := by
  let G := forcePressureGradientCurve f hf
  let g := forcePressureGradientField f hf
  let F := forcedForceMod f hf
  have hgs : StronglyMeasurable g := forcedCurveRep_stronglyMeasurable _ _
  have hslice : ∀ t, (fun x => g (x, t)) =ᵐ[volume] realVectorL2Representative (G t) :=
    forcedCurveRep_slice _ _
  refine ⟨hgs, fun T hT => ⟨?_, ?_⟩⟩
  · -- square integrability on the slab
    have hfin : ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => g (x, t)) 2 volume ^ (2 : ℝ) < ⊤ := by
      have hint := (integrableOn_forcedForceSlice_sq f hf T).mono_set Ioo_subset_Ioc_self
      have hbound : ∀ t, eLpNorm (fun x : Vec3 => g (x, t)) 2 volume ^ (2 : ℝ) ≤
          ENNReal.ofReal (4 * ‖forcedForceSlice F t‖ ^ 2) := by
        intro t
        rw [eLpNorm_congr_ae (hslice t)]
        have h1 := eLpNorm_realVectorL2Representative_le (G t)
        have h2 : ‖G t‖ ≤ 2 * ‖forcedForceSlice F t‖ := forcePressureGradientL2_norm_le _
        calc eLpNorm (realVectorL2Representative (G t)) 2 volume ^ (2 : ℝ)
            ≤ ENNReal.ofReal ‖G t‖ ^ (2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal (‖G t‖ ^ 2) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
            norm_num
          _ ≤ ENNReal.ofReal (4 * ‖forcedForceSlice F t‖ ^ 2) := by
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith only [h2, norm_nonneg (G t)]
      calc ∫⁻ t in Ioo 0 T, eLpNorm (fun x : Vec3 => g (x, t)) 2 volume ^ (2 : ℝ)
          ≤ ∫⁻ t in Ioo 0 T, ENNReal.ofReal (4 * ‖forcedForceSlice F t‖ ^ 2) :=
            lintegral_mono fun t => hbound t
        _ < ⊤ := by
            rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul 4)
              (Eventually.of_forall fun t => by positivity)]
            exact ENNReal.ofReal_lt_top
    rw [lintegral_eLpNorm_slice_sq_eq hgs] at hfin
    exact memLp_slab_of_prod ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 hfin)
  · -- the slice identification
    have hFf : ∀ᵐ z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))),
        F z = f z := by
      have h := forcedForceMod_ae_eq f hf hT
      rw [← restrict_spaceTimeSet_eq_prod]
      exact h
    have hsl : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
        ∀ᵐ x ∂(volume : Measure Vec3), F (x, t) = f (x, t) := by
      have h' := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ).restrict (Ioo 0 T))
        (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae hFf
      exact Measure.ae_ae_of_ae_prod h'
    obtain ⟨-, -, hgrad, -⟩ := forcePressure_spec f hf T hT
    filter_upwards [hsl, hgrad] with t ht ⟨hft, hW⟩
    have hFt : MemLp (fun x : Vec3 => F (x, t)) 2 volume := hft.ae_eq (ht.mono fun x hx => hx.symm)
    have hclass : forcedForceSlice F t =
        realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, t)) hft := by
      unfold forcedForceSlice
      rw [dite_eq_left hFt]
      apply realVectorL2Representative_injective_ae
      filter_upwards [realVectorL2OfCoordinateFunction_rep _ hFt,
        realVectorL2OfCoordinateFunction_rep _ hft, ht] with x h1 h2 h3
      rw [h1, h2, h3]
    have hGt : (fun x => g (x, t)) =ᵐ[volume]
        forcePressureGradientFunction (fun y : Vec3 => f (y, t)) hft := by
      refine (hslice t).trans ?_
      change realVectorL2Representative (forcePressureGradientL2 (forcedForceSlice F t)) =ᵐ[volume] _
      rw [hclass]
      exact Eventually.of_forall fun x => rfl
    exact ⟨⟨hft, hGt⟩, hasWeakGradientOn_congr_ae_right hGt.symm hW⟩

end CKN.Leray

end
