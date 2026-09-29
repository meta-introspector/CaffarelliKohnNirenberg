-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.IsGlobalForcedLerayHopfSolution
public import CKN.Statements.IsLocallySquareIntegrableForce
public import CKN.Statements.IsLocallyQIntegrableForce
public import CKN.Statements.TheoremC

/-!
# The forced singular set

The singular-set conclusion of `thm:leray-forced-singularSet` from the forced
existence conclusion of `thm:leray-forced` and Theorem C of Caffarelli, Kohn
and Nirenberg (CKN.caffarelliKohnNirenberg), applied with the force and the
exponent supplied by the existence hypothesis.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The same witness as in `thm:leray-forced` has a singular set of zero
one-dimensional parabolic Hausdorff measure, as in
`thm:leray-forced-singularSet`: Theorem C applies at the exponent `q₀` of the
hypothesis. -/
theorem lerayExistenceForced_singularSet_of_lerayExistenceForced
    (hLerayForced : ∀ a : Vec3 → Vec3, IsInJ a →
      ∀ f : ParabolicPoint → Vec3,
        IsLocallySquareIntegrableForce f →
        (∃ q₀ : ℝ, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
        ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        ∃ p : ParabolicPoint → ℝ,
          IsGlobalForcedLerayHopfSolution a f u Du ∧
          ∀ q : ℝ, 5 / 2 < q → IsLocallyQIntegrableForce q f →
            CKN.IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
              f) :
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
          (SingularSet (Set.univ : Set Vec3) (Ioi 0) u) = 0 := by
  intro a ha f hf hq₀
  obtain ⟨u, Du, p, hGlobal, hSuitable⟩ := hLerayForced a ha f hf hq₀
  obtain ⟨q₀, hq₀lt, hfq₀⟩ := hq₀
  exact ⟨u, Du, p, hGlobal, hSuitable,
    CKN.caffarelliKohnNirenberg q₀ hq₀lt (Set.univ : Set Vec3) (Ioi 0) u Du p
      f (hSuitable q₀ hq₀lt hfq₀)⟩

end CKN

end
