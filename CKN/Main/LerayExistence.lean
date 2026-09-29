-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistenceForced
public import CKN.Leray.LerayExistenceZeroForce

/-!
# Leray existence theorem

`thm:leray` from the zero-force case of `thm:leray-forced` (the zero-force
recovery after the proof of `thm:leray-forced-singularSet`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- `thm:leray`: every datum in `J` has a global Leray--Hopf solution that is
suitable, with a pressure and zero force, for every `q > 5/2`. -/
theorem leray_existence :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ, 5 / 2 < q →
          IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
            (0 : ParabolicPoint → Vec3) :=
  CKN.leray_existence_of_lerayExistenceForced CKN.Main.lerayExistenceForced

end CKN.Main
