-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.StabilityLocalVelocityLp
public import CKN.ClassEquivalence.TestSupport

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic

set_option autoImplicit false
noncomputable section

namespace CKN

/-- A local box in `def:sws` has finite space-time measure. -/
theorem stability_localBox_finiteMeasure
    {Ω Ω' : Set Vec3} {I J : Set ℝ}
    (hbox : CKN.localBox Ω I Ω' J) :
    IsFiniteMeasure (volume.restrict (CKN.spaceTimeSet Ω' J)) := by
  obtain ⟨_hopen, hΩcompact, _hΩsub, _hconn, hJcompact, _hJsub⟩ := hbox
  let K : Set ParabolicPoint := closure Ω' ×ˢ closure J
  have hK : IsCompact K := by
    apply parabolicHomeomorph.isCompact_preimage.mpr
    change IsCompact (closure Ω' ×ˢ closure J)
    exact hΩcompact.prod hJcompact
  have hsub : CKN.spaceTimeSet Ω' J ⊆ K := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨subset_closure hx, subset_closure ht⟩
  have hfinite : IsFiniteMeasure (volume.restrict K) :=
    CKN.isFiniteMeasure_restrict_of_isCompact hK
  apply isFiniteMeasure_restrict.mpr
  have hμ : (volume : Measure ParabolicPoint) (CKN.spaceTimeSet Ω' J) < ⊤ := by
    calc
      (volume : Measure ParabolicPoint) (CKN.spaceTimeSet Ω' J) ≤ volume K :=
        measure_mono hsub
      _ < ⊤ := by
        simpa using hfinite.measure_univ_lt_top
  exact hμ.ne

end CKN
