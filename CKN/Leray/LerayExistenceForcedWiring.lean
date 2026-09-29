-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedAssemblyContracts
public import CKN.Leray.ForcedRegularised
public import CKN.Leray.ForcedRegMomentum
public import CKN.Leray.ForcedRegLocalEnergy
public import CKN.Leray.ForcedPressureLimitRegularised
public import CKN.Leray.ForcedHopfLimit
public import CKN.Leray.ForcePressure

/-!
# Forced Leray existence from the forced compactness limit

The proof of `thm:leray-forced` applied to the forced regularized solutions of
`lem:regularised-forced` (`CKN.Leray.forcedRegVelocity`,
`CKN.Leray.forcedRegGradient`, `CKN.Leray.forcedRegPressure`) and the force
pressure of `lem:force-pressure` (`CKN.Leray.forcePressure`). The force
pressure bounds, the regularized solution clauses, the regularized momentum
identity `eq:reg-momentum-forced`, the regularized local energy inequality
`eq:reg-local-energy-forced`, the pressure limit and the forced Leray--Hopf
limit are supplied by their theorems; the only input left is the compactness
statement `prop:forced-limit` for these regularized solutions.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- `thm:leray-forced` from `prop:forced-limit` for the forced regularized
solutions of `lem:regularised-forced` with the mollifier profile `ρ`. -/
theorem lerayExistenceForced_of_forcedLerayLimit
    (ρ : RegMollifierProfile)
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        StrictMono σ ∧ Tendsto σ atTop atTop ∧
        Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
        (∀ x : Vec3, u (x, 0) = a x) ∧
        (∀ T : ℝ, 0 < T →
          let μ : Measure ParabolicPoint :=
            volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
          let U : ℕ → ParabolicPoint → Vec3 :=
            fun n => forcedRegVelocity ρ a ha f hf (εseq (σ n))
          let J : ℕ → ParabolicPoint → Vec3 := fun n =>
            CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
              (by exact (hseq (σ n)).1) (U n)
          let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
            forcedRegGradient ρ a ha f hf (εseq (σ n))
          AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
          MemLp u 2 μ ∧ MemLp Du 2 μ ∧
          Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
          (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
            Tendsto (fun n => ∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
              atTop (nhds (∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
          (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
            Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
              atTop (nhds 0)) ∧
          (∀ n, MemLp (U n) 3 μ) ∧
          (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
          Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
          (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
            MemLp w 2 volume →
            Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
                U n (x, t) i * w x i) atTop
              (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
          (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
            HasWeakGradientOn (Set.univ : Set Vec3)
              (fun x => u (x, t) i) (fun x => Du (x, t) i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y =>
                forcedRegVelocity ρ a ha f hf (εseq (σ n))
                  (parabolicHomeomorph.symm y)) σ z)) :
    ∀ a : Vec3 → Vec3, IsInJ a →
    ∀ f : ParabolicPoint → Vec3,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        ∀ q : ℝ, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          CKN.IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p f :=
  lerayExistenceForced_of_limits ρ forcePressure (forcedRegVelocity ρ)
    (forcedRegGradient ρ) (forcedRegPressure ρ) forcePressure_spec
    (forcedRegularised ρ) (forcedRegMomentum ρ) (forcedRegLocalEnergy ρ)
    hlerayLimit (forcedPressureLimit_forcedRegularised ρ)
    (lerayHopfLimitForced ρ forcePressure (forcedRegVelocity ρ)
      (forcedRegGradient ρ) (forcedRegPressure ρ) (forcedRegularised ρ)
      (forcedRegMomentum ρ) hlerayLimit)

end CKN.Leray

end
