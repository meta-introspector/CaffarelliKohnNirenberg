-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedPressureLimit
public import CKN.Leray.ForcedLerayLimitTenThirds

/-!
# The pressure limit for the forced regularized solutions

The pressure limit of `thm:leray-forced` for the forced regularized solutions
of `lem:regularised-forced` and the force pressure of `lem:force-pressure`:
the quadratic pressures are the Riesz pressures of the regularized tensors
(`lem:regularised-forced`) and every forced regularized velocity lies in `L³`
on finite slabs (`eq:forced-ten-thirds`), so the general pressure limit
applies along the whole sequence.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The pressure limit of `thm:leray-forced` for the forced regularized
solutions: whenever the forced regularized velocities and their
mollifications converge in `L³` on finite slabs to `u` along a subsequence,
the forced regularized pressures converge in `L^{3/2}` on finite slabs to a
pressure `p` for which `p − p_f` is the Riesz pressure of `u ⊗ u`
(`prop:leray-pressure-limit`). -/
theorem forcedPressureLimit_forcedRegularised (ρ : RegMollifierProfile) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (forcedRegVelocity ρ a ha f hf (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (forcedRegVelocity ρ a ha f hf (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0)),
      ∃ p : ParabolicPoint → ℝ,
        ∀ T : ℝ, 0 < T →
          let μ : Measure (Vec3 × ℝ) :=
            (volume : Measure (Vec3 × ℝ)).restrict
              (CKN.Leray.lerayPressureLimitSlab T)
          let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
          let pST : Vec3 × ℝ → ℝ := fun z => p (parabolicHomeomorph.symm z)
          let pFST : Vec3 × ℝ → ℝ := fun z =>
            forcePressure f hf (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            forcedRegPressure ρ a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp (pST - pFST) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST - pFST =ᵐ[μ]
              CKN.Leray.lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0) :=
  forcedPressureLimit_of_regularised_pressure_data ρ forcePressure (forcedRegVelocity ρ)
    (forcedRegPressure ρ)
    (fun a ha f hf ε hε =>
      ⟨fun T hT => ((forcedRegularised ρ a ha f hf ε hε).2.2.1 T hT).2,
        fun t ht =>
          ⟨((forcedRegularised ρ a ha f hf ε hε).2.2.2.1 t ht).choose,
            ((forcedRegularised ρ a ha f hf ε hε).2.2.2.1 t ht).choose_spec.1⟩⟩)
    (fun a ha f hf εseq hseq _ =>
      ⟨id, strictMono_id, tendsto_id, fun T hT n =>
        (forcedRegVelocity_memLp_slab ρ a ha f hf (εseq n) (hseq n).1 T hT).2.2.1⟩)

end CKN.Leray

end
