-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Parabolic.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- The quadratic tensor on the finite slab, extended by zero in time. -/
def forcedQuadraticTensor (T : ℝ) (u : ParabolicPoint → Vec3) :
    Fin 3 → Fin 3 → ParabolicPoint → ℝ :=
  fun i j z => if z.2 ∈ Ioo 0 T then u z i * u z j else 0

end CKN
