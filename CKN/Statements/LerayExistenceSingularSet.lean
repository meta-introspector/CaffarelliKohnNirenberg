-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistenceSingularSet

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The CKN headline conclusion `cor:ckn-headline` for the global solution
supplied by Leray's theorem. -/
theorem leray_existence_singularSet :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        IsGlobalLerayHopfSolution a u Du ∧
        parabolicHausdorffMeasure 1
          (SingularSet (Set.univ : Set Vec3) (Ioi 0) u) = 0 :=
by exact CKN.Main.leray_existence_singularSet

end CKN
