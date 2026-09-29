-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.IsForcedLerayHopfSolution
public import CKN.Statements.IsGlobalForcedLerayHopfSolution
public import CKN.Statements.IsLerayHopfSolution
public import CKN.Statements.IsGlobalLerayHopfSolution
public import CKN.Leray.LerayHopfLimitPropEnergyIneq

/-!
# Zero-force recovery

With the zero force, the forced Leray--Hopf conditions of
`def:forced-leray-hopf` are exactly the conditions of `def:leray-hopf`, with
the same time representative. The forced weak equation loses its force term,
and the real form of the forced energy inequality is the extended-real energy
inequality, because the initial energy is finite for data in the source space.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN

/-- With zero force, a finite-time forced Leray--Hopf solution is exactly a
Leray--Hopf solution with the same representative (zero-force recovery in
`sec:forced-leray`). -/
theorem forced_lerayHopf_zero_iff_lerayHopf (T : ℝ) (a : Vec3 → Vec3)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) :
    IsForcedLerayHopfSolution T a (fun _ => 0) u Du ↔
      IsLerayHopfSolution T a u Du := by
  have hR (ha : IsInJ a) :
      ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ))
        ≠ ⊤ := by
    rw [CKN.Leray.lerayHopfLimit_lintegral_euclidean_sq ha.1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  constructor
  · rintro ⟨hT, ha, -, hu, hDu, hess, hjoint, hgrad, hdiv, hcont, hmom, hen,
      htr⟩
    refine ⟨hT, ha, hu, hDu, hess, hjoint, hgrad, hdiv, hcont, ?_, ?_, htr⟩
    · intro φ hφ hdivφ
      simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
        using hmom φ hφ hdivφ
    · intro t₀ ht₀
      obtain ⟨hlt, hle⟩ := hen t₀ ht₀
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        integral_zero, add_zero] at hle
      exact (ENNReal.toReal_le_toReal hlt.ne (hR ha)).mp hle
  · rintro ⟨hT, ha, hu, hDu, hess, hjoint, hgrad, hdiv, hcont, hmom, hen,
      htr⟩
    refine ⟨hT, ha, ?_, hu, hDu, hess, hjoint, hgrad, hdiv, hcont, ?_, ?_,
      htr⟩
    · exact MemLp.zero
    · intro φ hφ hdivφ
      simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
        using hmom φ hφ hdivφ
    · intro t₀ ht₀
      have hle := hen t₀ ht₀
      refine ⟨lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (hR ha)), ?_⟩
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        integral_zero, add_zero]
      exact ENNReal.toReal_mono (hR ha) hle

/-- With zero force, a global forced Leray--Hopf solution is exactly a global
Leray--Hopf solution (`rem:global-LH`) with the same representative. -/
theorem forced_globalLerayHopf_zero_iff_globalLerayHopf (a : Vec3 → Vec3)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) :
    IsGlobalForcedLerayHopfSolution a (fun _ => 0) u Du ↔
      IsGlobalLerayHopfSolution a u Du :=
  forall_congr' fun T => imp_congr_right fun _ =>
    forced_lerayHopf_zero_iff_lerayHopf T a u Du

end CKN

end
