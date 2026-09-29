-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Square integrability of the force on every finite positive-time slab. -/
def IsLocallySquareIntegrableForce (f : ParabolicPoint → Vec3) : Prop :=
  ∀ T : ℝ, 0 < T →
    MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))

end CKN
