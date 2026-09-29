-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.IsForcedLerayHopfSolution

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- A global forced Leray--Hopf solution on every finite interval. -/
def IsGlobalForcedLerayHopfSolution (a : Vec3 → Vec3)
    (f : ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) : Prop :=
  ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du

end CKN
