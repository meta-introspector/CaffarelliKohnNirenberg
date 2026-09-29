-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Euclidean.SmoothIBP
public import CKN.Foundation.Parabolic.Basic
public import CKN.Foundation.Sobolev.TestFunction
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- Smooth compactly supported approximants to the source space `J` in
`def:leray-hopf`, expressed as a convergent sequence. -/
def IsInJ (a : Vec3 → Vec3) : Prop :=
  MemLp a (2 : ℝ≥0∞) volume ∧
    ∃ aSeq : ℕ → Vec3 → Vec3,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (aSeq k)) ∧
      (∀ k, HasCompactSupport (aSeq k)) ∧
      (∀ k x, ∑ i : Fin 3, spatialDeriv (fun y => aSeq k y i) i x = 0) ∧
      Tendsto
        (fun k => eLpNorm (fun x => aSeq k x - a x) (2 : ℝ≥0∞) volume)
        atTop (nhds 0)

end CKN
