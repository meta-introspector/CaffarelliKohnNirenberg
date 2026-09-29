-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RieszPressurePackageDistribution

/-!
# Characterization of the pressure extension

The selected measurable representative has the spatial pressure as its slice,
obeys the source norm bounds, and satisfies the distributional sign convention.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

theorem rieszPressure_package
    (r : ℝ) (hr : 1 < r) (s : ℝ) (hs : 1 < s)
    (F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ)
    (hFr : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)))
    (hFs : ∀ i j, MemLp (F i j) (ENNReal.ofReal s)
      (volume : Measure (Vec3 × ℝ))) :
    Measurable (rieszPressureSpaceTime r hr F hFr) ∧
    MemLp (rieszPressureSpaceTime r hr F hFr) (ENNReal.ofReal r)
      (volume : Measure (Vec3 × ℝ)) ∧
    ‖rieszPressureSpaceTimeClass r hr
        (rieszPressureSpaceTimeTensorToLp r hr F hFr)‖ ≤
      rieszPressureOperatorBound r hr * ∑ i : Fin 3, ∑ j : Fin 3,
        ‖(hFr i j).toLp (F i j)‖ ∧
    rieszPressureSpaceTime r hr F hFr =ᵐ[volume]
      rieszPressureSpaceTime s hs F hFs ∧
    (∀ᵐ t ∂(volume : Measure ℝ),
      ∃ hFt : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3),
        (fun x : Vec3 => rieszPressureSpaceTime r hr F hFr (x, t)) =ᵐ[volume]
          (fun x => rieszPressureSlice r hr
            (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y, t))) x) ∧
        ‖rieszPressureSlice r hr
            (fun i j => (hFt i j).toLp (fun y : Vec3 => F i j (y, t)))‖ ≤
          rieszPressureOperatorBound r hr * ∑ i : Fin 3, ∑ j : Fin 3,
            ‖(hFt i j).toLp (fun y : Vec3 => F i j (y, t))‖) ∧
    (∀ᵐ t ∂(volume : Measure ℝ),
      ∃ hFrt : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal r) (volume : Measure Vec3),
      ∃ hFst : ∀ i j, MemLp (fun x : Vec3 => F i j (x, t))
          (ENNReal.ofReal s) (volume : Measure Vec3),
        rieszPressureSlice r hr (fun i j => (hFrt i j).toLp
          (fun x : Vec3 => F i j (x, t))) =ᵐ[volume]
        rieszPressureSlice s hs (fun i j => (hFst i j).toLp
          (fun x : Vec3 => F i j (x, t))) ) ∧
    (∀ᵐ t ∂(volume : Measure ℝ),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, rieszPressureSpaceTime r hr F hFr (x, t) *
            (-CKN.spatialLaplacian ψ x) =
          ∑ i : Fin 3, ∑ j : Fin 3, ∫ x,
            F i j (x, t) * CKN.mixedSecond ψ i j x) := by
  refine ⟨rieszPressureSpaceTime_measurable r hr F hFr,
    rieszPressureSpaceTime_memLp r hr F hFr,
    rieszPressureSpaceTime_bound r hr F hFr,
    rieszPressureSpaceTime_ae_eq_of_memLp_common r hr s hs F hFr hFs,
    ?_,
    rieszPressureSpaceTime_slice_exponent_agreement r hr s hs F hFr hFs,
    rieszPressureSpaceTime_slice_laplacian_identity r hr F hFr⟩
  filter_upwards [rieszPressureSpaceTime_slice_ae_eq r hr F hFr] with t hSlice
  obtain ⟨hFt, hRep⟩ := hSlice
  refine ⟨hFt, ⟨hRep, ?_⟩⟩
  exact rieszPressureSlice_norm_le r hr
    (fun i j => (hFt i j).toLp (fun x : Vec3 => F i j (x, t)))

end CKN.Leray

end
