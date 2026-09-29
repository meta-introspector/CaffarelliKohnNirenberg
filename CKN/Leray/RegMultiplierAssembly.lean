-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.FourierHeatJRange
public import CKN.Leray.FourierPhysicalRange
public import CKN.Leray.FourierRealification

/-!
# The regularized multiplier bounds

This file assembles the real `L²` operator bounds and divergence conclusions
of `lem:reg-multiplier-bounds` from their Fourier multiplier constructions.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal FourierTransform
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- Real scalar-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev RealScalarL2 := Lp (α := L2Vec3) ℝ 2

/-- Complex scalar-valued spatial `L²` on the Euclidean three-dimensional carrier. -/
abbrev ComplexScalarL2 := Lp (α := L2Vec3) ℂ 2

/-- Taking real parts of complex scalar-valued spatial `L²`. -/
def realPartScalarL2 : ComplexScalarL2 →L[ℝ] RealScalarL2 :=
  Complex.reCLM.compLpL 2 volume

/-- The real pressure multiplier on tensor-valued spatial `L²`, obtained from
the double-Riesz Fourier multiplier by realification. -/
def realPressureOperator (F : RealTensorL2) : RealScalarL2 :=
  realPartScalarL2 (pressureL2Operator (complexifyTensorL2 F))

/-- Realification does not increase the scalar `L²` norm. -/
theorem real_part_scalar_l2_norm_le (f : ComplexScalarL2) :
    ‖realPartScalarL2 f‖ ≤ ‖f‖ := by
  have hvalue : ‖Complex.reCLM‖ ≤ 1 := by
    apply (ContinuousLinearMap.opNorm_le_iff (by norm_num)).2
    intro z
    simpa [one_mul, Real.norm_eq_abs] using Complex.abs_re_le_norm z
  calc
    ‖realPartScalarL2 f‖ ≤ ‖realPartScalarL2‖ * ‖f‖ :=
      realPartScalarL2.le_opNorm f
    _ ≤ 1 * ‖f‖ := by
      gcongr
      exact (ContinuousLinearMap.norm_compLpL_le Complex.reCLM).trans hvalue
    _ = ‖f‖ := by ring

/-- The real double-Riesz pressure multiplier satisfies the `L²` bound in
`lem:reg-multiplier-bounds`. -/
theorem real_pressure_operator_norm_le (F : RealTensorL2) :
    ‖realPressureOperator F‖ ≤ 3 * ‖F‖ := by
  calc
    ‖realPressureOperator F‖ ≤
        ‖pressureL2Operator (complexifyTensorL2 F)‖ :=
      real_part_scalar_l2_norm_le _
    _ ≤ ‖complexifyTensorL2 F‖ := pressureL2Operator_norm_le _
    _ ≤ ‖F‖ := complexifyTensorL2_norm_le F
    _ = 1 * ‖F‖ := by ring
    _ ≤ 3 * ‖F‖ := mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg F)

/-- The real heat operator, the Leray projection, the Stokes operator, and
the pressure multiplier satisfy all four bounds in
`lem:reg-multiplier-bounds`. -/
theorem reg_multiplier_assembly_l2_bounds
    {t : ℝ} (ht : 0 < t) (v : RealVectorL2) (F : RealTensorL2) :
    ‖realHeatOperator t ht.le v‖ ≤ ‖v‖ ∧
      ‖realStokesOperator ht F‖ ≤
        (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ ∧
      ‖realPressureOperator F‖ ≤ 3 * ‖F‖ ∧
      ‖realLerayProjection v‖ ≤ ‖v‖ := by
  exact ⟨realHeatOperator_norm_le t ht.le v,
    realStokesOperator_norm_le ht F,
      real_pressure_operator_norm_le F,
    realLerayProjection_norm_le v⟩

/-- The heat semigroup preserves weak divergence freedom, the Leray
projection and Stokes operator have weakly divergence-free range, and
`K(t)F` has zero weak divergence, as in `lem:reg-multiplier-bounds`. -/
theorem reg_multiplier_assembly_weak_divergence
    {t : ℝ} (ht : 0 < t) (v : RealVectorL2)
    (hv : IsWeakDivFreeL2 (realVectorL2Representative v))
    (F : RealTensorL2) :
    IsWeakDivFreeL2
        (realVectorL2Representative (realHeatOperator t ht.le v)) ∧
      IsWeakDivFreeL2
        (realVectorL2Representative (realLerayProjection v)) ∧
      IsWeakDivFreeL2
        (realVectorL2Representative (realStokesOperator ht F)) := by
  have hvJ : CKN.IsInJ (realVectorL2Representative v) :=
    CKN.weakDivFreeL2_isInJ hv
  have hheatJ : CKN.IsInJ
      (realVectorL2Representative (realHeatOperator t ht.le v)) :=
    realHeatOperator_isInJ ht.le v hvJ
  exact ⟨(CKN.isInJ_iff_weakDivFree).1 hheatJ,
    realLerayProjection_isWeakDivFree v,
    realStokesOperator_isWeakDivFree ht F⟩

/-- The complete multiplier estimate and divergence-preservation package of
`lem:reg-multiplier-bounds`. -/
theorem reg_multiplier_assembly_source
    {t : ℝ} (ht : 0 < t) (v : RealVectorL2)
    (hv : IsWeakDivFreeL2 (realVectorL2Representative v))
    (F : RealTensorL2) :
    (‖realHeatOperator t ht.le v‖ ≤ ‖v‖ ∧
      ‖realStokesOperator ht F‖ ≤
        (1 / Real.sqrt (2 * Real.exp 1 * t)) * ‖F‖ ∧
      ‖realPressureOperator F‖ ≤ 3 * ‖F‖ ∧
      ‖realLerayProjection v‖ ≤ ‖v‖) ∧
    (IsWeakDivFreeL2
        (realVectorL2Representative (realHeatOperator t ht.le v)) ∧
      IsWeakDivFreeL2
        (realVectorL2Representative (realLerayProjection v)) ∧
      IsWeakDivFreeL2
        (realVectorL2Representative (realStokesOperator ht F))) := by
  exact ⟨reg_multiplier_assembly_l2_bounds ht v F,
    reg_multiplier_assembly_weak_divergence ht v hv F⟩

end CKN.Leray

end
