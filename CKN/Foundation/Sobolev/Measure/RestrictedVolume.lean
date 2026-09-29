-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Sobolev.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Restricted Lebesgue volume

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps the common restricted-volume abbreviations and
drops domain regularity predicates that are not needed by weak derivatives.
-/

@[expose] public section

namespace CKN

/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-- Compatibility name for the restricted volume measure. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  volumeOn U

end CKN
