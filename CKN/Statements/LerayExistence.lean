-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistence

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Leray's existence theorem, including the CKN suitable-solution conclusion
of `thm:leray`. -/
theorem leray_existence :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ, 5 / 2 < q →
          IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
            (0 : ParabolicPoint → Vec3) :=
by exact CKN.Main.leray_existence

end CKN
