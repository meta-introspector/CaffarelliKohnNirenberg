-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.LerayExistenceForcedWiring
public import CKN.Leray.RegMollifierProfileStandard
public import CKN.Leray.ForcedLerayLimitPropProvider
public import CKN.Leray.ForcedLerayLimitPropTailsFinal

/-!
# Forced suitable existence

The proof of `thm:leray-forced`: the forced limiting argument
`CKN.Leray.lerayExistenceForced_of_forcedLerayLimit` for the standard mollifier
profile, with the compactness statement `prop:forced-limit` for the forced
regularized solutions.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- `thm:leray-forced`: one velocity, weak gradient and pressure form a global
forced Leray--Hopf solution that is suitable for every admissible exponent. -/
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
  CKN.Leray.lerayExistenceForced_of_forcedLerayLimit
    CKN.Leray.standardRegMollifierProfile
    (CKN.Leray.forcedLerayLimit_of_spatialTails CKN.Leray.standardRegMollifierProfile
      (CKN.Leray.forcedLerayLimit_spatialTails_with_limit
        CKN.Leray.standardRegMollifierProfile))

end CKN.Main
