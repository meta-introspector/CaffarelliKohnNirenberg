-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.LocalBox
public import CKN.Statements.LocalVecLp
public import CKN.Statements.SpaceTimeSet

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Local `L^q` integrability of the force on the cylinders in `def:sws`. -/
def IsLocallyQIntegrableForce (q : ℝ) (f : ParabolicPoint → Vec3) : Prop :=
  ∀ Ω' J, localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J →
    localVecLp (spaceTimeSet Ω' J) q f

end CKN
