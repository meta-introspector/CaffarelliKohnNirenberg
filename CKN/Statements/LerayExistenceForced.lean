-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistenceForced

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- One forced solution supplies the same velocity, weak gradient, and
pressure for every locally admissible CKN exponent, as in `thm:leray-forced`.
The existence hypothesis records one exponent above `5/2` as in that theorem. -/
theorem lerayExistenceForced :
    ∀ a : Vec3 → Vec3, IsInJ a →
    ∀ f : ParabolicPoint → Vec3,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        ∀ q : ℝ, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          CKN.IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p f :=
by exact CKN.Main.lerayExistenceForced

end CKN
