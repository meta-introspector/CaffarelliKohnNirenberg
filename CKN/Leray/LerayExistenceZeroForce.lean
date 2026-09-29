-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedZeroForce
public import CKN.Witnesses.ForcedZero
public import CKN.Statements.SuitableWeakSolution

/-!
# Zero-force recovery of Leray's existence theorem

The zero-force case of `thm:leray-forced` gives `thm:leray` with the same
velocity, weak gradient and pressure, as in the zero-force recovery paragraph
after the proof of `thm:leray-forced-singularSet`: the zero force is square
integrable on every slab and locally `L^q` for every `q`, and with zero force
the global forced Leray--Hopf class is the global Leray--Hopf class
(`CKN.forced_globalLerayHopf_zero_iff_globalLerayHopf`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- `thm:leray` from the zero-force case of `thm:leray-forced`. -/
theorem leray_existence_of_lerayExistenceForced
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
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ, 5 / 2 < q →
          IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p
            (0 : ParabolicPoint → Vec3) := by
  intro a ha
  obtain ⟨u, Du, p, hGlobal, hSuitable⟩ :=
    hLerayForced a ha (fun _ : ParabolicPoint => (0 : Vec3))
      isLocallySquareIntegrableForce_zero
      ⟨3, by norm_num, isLocallyQIntegrableForce_zero 3⟩
  refine ⟨u, Du, p,
    (forced_globalLerayHopf_zero_iff_globalLerayHopf a u Du).1 hGlobal, ?_⟩
  intro q hq
  exact hSuitable q hq (isLocallyQIntegrableForce_zero q)

end CKN

end
