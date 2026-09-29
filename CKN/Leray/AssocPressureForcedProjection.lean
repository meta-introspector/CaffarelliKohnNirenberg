-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitForceGradient
public import CKN.Leray.ForcePressureOrthogonality
public import CKN.Leray.FourierCoordinateL2Bridge
public import CKN.Leray.RieszPressurePackageForce
public import CKN.Statements.SpaceTimeSet

/-!
# The projected force associated with the force pressure

The pressure gradient is the complement of the Leray projection on almost
every spatial force slice.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Subtracting the force pressure gradient from an `L²` force slice gives
the Leray projection of that slice. -/
theorem forcePressureGradientFunction_complement_ae_isLerayProjection
    {F : Vec3 → Vec3} (hF : MemLp F 2 volume) :
    (fun x : Vec3 => F x - forcePressureGradientFunction F hF x) =ᵐ[volume]
      realVectorL2Representative
        (realLerayProjection (realVectorL2OfCoordinateFunction F hF)) := by
  let v : RealVectorL2 := realVectorL2OfCoordinateFunction F hF
  have hgrad : forcePressureGradientFunction F hF =ᵐ[volume]
      realVectorL2Representative (forcePressureGradientL2 v) := by
    filter_upwards [] with x
    rfl
  have hvrep := realVectorL2OfCoordinateFunction_rep F hF
  have hrepSub : realVectorL2Representative
      (v - realLerayProjection v) =ᵐ[volume]
      fun x => realVectorL2Representative v x -
        realVectorL2Representative (realLerayProjection v) x := by
    let e : L2Vec3 ≃L[ℝ] Vec3 :=
      PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
    have hsub := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae
      (Lp.coeFn_sub v (realLerayProjection v))
    filter_upwards [hsub] with x hx
    change e ((v - realLerayProjection v) (WithLp.toLp 2 x)) =
      e (v (WithLp.toLp 2 x)) -
        e (realLerayProjection v (WithLp.toLp 2 x))
    rw [hx]
    exact e.map_sub _ _
  filter_upwards [hvrep, hgrad, hrepSub] with x hxF hxgrad hxsub
  have hxgrad' := hxgrad
  change forcePressureGradientFunction F hF x =
    realVectorL2Representative (v - realLerayProjection v) x at hxgrad'
  rw [hxgrad', hxsub, hxF]
  ring

/-- Almost every spatial slice of the force residual is weakly
divergence-free. -/
theorem forcePressureResidual_isWeakDivFree_slices
    (f : ParabolicPoint → Vec3) (hf : CKN.IsLocallySquareIntegrableForce f)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      CKN.IsWeakDivFreeL2
        (fun x : Vec3 => f (x, t) - forcePressureGradientField f hf (x, t)) := by
  obtain ⟨-, hspec⟩ := forcePressureGradientField_spec f hf
  obtain ⟨-, hslices⟩ := hspec T hT
  filter_upwards [hslices] with t ht
  rcases ht with ⟨⟨hft, hgradAE⟩, -⟩
  have hcomplement := forcePressureGradientFunction_complement_ae_isLerayProjection hft
  have hres : (fun x : Vec3 => f (x, t) - forcePressureGradientField f hf (x, t)) =ᵐ[volume]
      realVectorL2Representative
        (realLerayProjection (realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft)) := by
    filter_upwards [hgradAE, hcomplement] with x hx hg
    rw [hx, hg]
  have hproj := realLerayProjection_isWeakDivFree
    (realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft)
  refine ⟨hproj.1.ae_eq hres.symm, ?_⟩
  intro ψ
  calc
    ∫ x : Vec3, ∑ i : Fin 3,
        (f (x, t) - forcePressureGradientField f hf (x, t)) i * ψ.partialDeriv i x
        = ∫ x : Vec3, ∑ i : Fin 3,
          realVectorL2Representative
            (realLerayProjection
              (realVectorL2OfCoordinateFunction (fun x => f (x, t)) hft)) x i *
            ψ.partialDeriv i x := by
          apply integral_congr_ae
          filter_upwards [hres] with x hx
          rw [hx]
    _ = 0 := hproj.2 ψ

end CKN.Leray

end
