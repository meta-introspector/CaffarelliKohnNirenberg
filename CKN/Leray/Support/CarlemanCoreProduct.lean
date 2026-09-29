-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.Support.CarlemanCoreDefs

/-!
# Ordinary product calculus on space-time

The Carleman calculations use the ordinary normed product structure on
space-time. These explicit structures keep that choice consistent across
the linear estimates.
-/

@[expose] public section

set_option autoImplicit false

open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The ordinary product normed additive group on space-time. -/
abbrev carlemanProductNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance carlemanCoreProductNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  carlemanProductNormedAddCommGroup

/-- The ordinary product normed real vector space on space-time. -/
abbrev carlemanProductNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

end CKN
