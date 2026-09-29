-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import CKN.Main.TheoremC
public import CKN.Main.TheoremCPaper
public import CKN.Statements.SpaceTimeSet
public import CKN.Statements.SuitableWeakSolutionIntegrable
public import CKN.Statements.SuitableWeakSolution
public import CKN.Statements.RegularPoint
public import CKN.Statements.SingularSet

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Theorem C, paper label `thm:C`; as explained in docs/DESIGN_NOTES.md, it uses Mathlib's parabolic Hausdorff measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
by exact CKN.Main.caffarelliKohnNirenbergPaper q hq

end CKN
