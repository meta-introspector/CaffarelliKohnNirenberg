-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Main.LerayExistence
public import CKN.Leray.LerayAssemblySingularSet

/-!
# Leray existence with the CKN singular-set conclusion

`cor:ckn-headline` from `thm:leray` and CKN Theorem C.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Main

/-- `cor:ckn-headline`: the global solution of `thm:leray` has a singular set of
zero one-dimensional parabolic Hausdorff measure. -/
theorem leray_existence_singularSet :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        IsGlobalLerayHopfSolution a u Du ∧
        parabolicHausdorffMeasure 1
          (SingularSet (Set.univ : Set Vec3) (Ioi 0) u) = 0 :=
  CKN.leray_existence_singularSet_of_leray_existence CKN.Main.leray_existence

end CKN.Main
