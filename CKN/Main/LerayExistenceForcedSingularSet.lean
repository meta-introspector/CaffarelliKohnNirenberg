-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistenceForced
public import CKN.Leray.ForcedSingularSet

/-!
# The forced singular set

`thm:leray-forced-singularSet` from `thm:leray-forced` and CKN Theorem C.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- `thm:leray-forced-singularSet`: the witness of `thm:leray-forced` has a
singular set of zero one-dimensional parabolic Hausdorff measure. -/
theorem lerayExistenceForcedSingularSet :
    ∀ a : Vec3 → Vec3, IsInJ a →
    ∀ f : ParabolicPoint → Vec3,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        (∀ q : ℝ, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          CKN.IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p f) ∧
        parabolicHausdorffMeasure 1
          (SingularSet (Set.univ : Set Vec3) (Ioi 0) u) = 0 :=
  CKN.lerayExistenceForced_singularSet_of_lerayExistenceForced
    CKN.Main.lerayExistenceForced

end CKN.Main
