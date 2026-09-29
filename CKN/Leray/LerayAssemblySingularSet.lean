-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.IsGlobalLerayHopfSolution
public import CKN.Statements.TheoremC

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The CKN singular-set conclusion follows from the Leray existence conclusion
and Theorem C, as in `cor:ckn-headline`. -/
theorem leray_existence_singularSet_of_leray_existence
    (hLeray : ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ, 5 / 2 < q →
          IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
            (0 : ParabolicPoint → Vec3)) :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        IsGlobalLerayHopfSolution a u Du ∧
        parabolicHausdorffMeasure 1
          (SingularSet (Set.univ : Set Vec3) (Ioi 0) u) = 0 := by
  intro a ha
  obtain ⟨u, Du, p, hGlobal, hSuitable⟩ := hLeray a ha
  refine ⟨u, Du, hGlobal, ?_⟩
  exact CKN.caffarelliKohnNirenberg (3 : ℝ)
    (by norm_num : (5 / 2 : ℝ) < 3)
    (Set.univ : Set Vec3) (Ioi 0) u Du p (0 : ParabolicPoint → Vec3)
    (hSuitable 3 (by norm_num : (5 / 2 : ℝ) < 3))

end CKN

end
