-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedTensor
public import CKN.Leray.StabilityLocalFinite
public import CKN.Leray.RieszPressureSpaceTimeLp
public import CKN.Leray.RieszPressurePackageAgreement

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The canonical pressure belongs to `L^(5/3)` on the finite slab by the
space-time Riesz estimate `eq:riesz-spacetime-bound`. -/
theorem forcedAssociatedPressure_rieszPressure_memLp_slab
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure ParabolicPoint)) :
    MemLp
      (CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (CKN.forcedQuadraticTensor T u) hN)
      (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hglobal : MemLp
      (CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (CKN.forcedQuadraticTensor T u) hN)
      (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint) := by
    exact rieszPressureSpaceTime_memLp (5 / 3 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN
  exact hglobal.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))

/-- The `(5/3)` and `(3/2)` Riesz realizations of the same forced tensor
agree almost everywhere under the canonical choice in `def:riesz-pressure`. -/
theorem forcedAssociatedPressure_rieszPressure_exponents_ae_eq
    {T : ℝ} {u : ParabolicPoint → Vec3}
    (hN5 : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure ParabolicPoint))
    (hN3 : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume : Measure ParabolicPoint)) :
    (CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN5) =ᵐ[volume]
    (CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN3) := by
  exact rieszPressureSpaceTime_ae_eq_of_memLp_common
    (5 / 3 : ℝ) (by norm_num) (3 / 2 : ℝ) (by norm_num)
    (CKN.forcedQuadraticTensor T u) hN5 hN3

/-- A compact local box inherits the `(3/2)` pressure class from the global
`(5/3)` Riesz bound and finite measure. -/
theorem forcedAssociatedPressure_rieszPressure_local_threeHalves
    {T : ℝ} {u : ParabolicPoint → Vec3} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioo 0 T) Ω' J)
    (hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j) (ENNReal.ofReal (5 / 3 : ℝ))
        (volume : Measure ParabolicPoint)) :
    CKN.localLp (spaceTimeSet Ω' J) (3 / 2 : ℝ)
      (CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
        (CKN.forcedQuadraticTensor T u) hN) := by
  let pN : ParabolicPoint → ℝ :=
    rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
      (CKN.forcedQuadraticTensor T u) hN
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  have hfinite : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hsubset : spaceTimeSet Ω' J ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    rcases hbox with ⟨_, _, _, _, _, hJsub⟩
    exact Set.prod_mono (Set.subset_univ _) (Set.Subset.trans subset_closure hJsub)
  have hslab := forcedAssociatedPressure_rieszPressure_memLp_slab hN
  have hpLocal53 : MemLp pN (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    have hle : μ ≤ volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
      Measure.restrict_mono_set volume hsubset
    have h := hslab.mono_measure hle
    simpa [pN, μ] using h
  have hpLocal32 : MemLp pN (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    @MemLp.mono_exponent _ _ _ μ pN _ _
      (ENNReal.ofReal (3 / 2 : ℝ)) (ENNReal.ofReal (5 / 3 : ℝ))
      hfinite hpLocal53 (by norm_num)
  simpa [CKN.localLp, μ, pN] using hpLocal32

end CKN.Leray

end
