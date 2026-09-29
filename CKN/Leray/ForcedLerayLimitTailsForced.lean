-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitTailsExterior
public import CKN.Leray.ForcedLerayLimitForceGradient
public import CKN.Leray.ForcedLerayLimitInitialTail
public import CKN.Leray.ForcedLerayLimitPressureBound

/-!
# Spatial tails of the forced regularized solutions

`lem:forced-tails` for the forced regularized solutions of
`lem:regularised-forced`: given their local energy inequality
`eq:reg-local-energy-forced`, the exterior energy outside the ball of radius
`2R` at a time `t ≤ T` is bounded by the exterior energy of the datum outside
the ball of radius `R - 1` (`eq:forced-initial-tail`), cutoff-gradient terms
of order `1/R` and `1/R²` controlled by the slab norms of the solution, the
transport velocity and the quadratic pressure, and the tail of the projected
force `f - (I - ℙ) f` outside the ball of radius `R`
(`eq:forced-projection-cancellation`). The slab norms are bounded
independently of `ε` by `lem:forced-energy-bounds`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- `lem:forced-tails` for the forced regularized solutions, with
`p_f = forcePressure f hf` and `(I - ℙ) f` the space-time force-pressure
gradient `forcePressureGradientField f hf`. -/
theorem forcedLerayLimit_forcedTails
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
    (∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (forcedRegVelocity ρ a ha f hf ε)
            (forcedRegGradient ρ a ha f hf ε) z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
                  regUniformMollifiedVelocity ρ ε hε (forcedRegVelocity ρ a ha f hf ε) z i +
                2 * forcedRegPressure ρ a ha f hf ε z * forcedRegVelocity ρ a ha f hf ε z i) *
                spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * forcedRegVelocity ρ a ha f hf ε z i) * ψ z) →
    ∀ T : ℝ, 0 < T → ∀ R : ℝ, 0 < R → ∀ t ∈ Icc 0 T,
      ∫ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
          vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε (x, t)) ^ (2 : ℕ) ≤
        (∫ x in {x : Vec3 | R - 1 < vec3EuclideanNorm x}, vec3EuclideanNorm (a x) ^ (2 : ℕ)) +
          C / R ^ 2 * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z) ^ (2 : ℕ)) +
          C / R * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z) ^ (2 : ℕ) *
                ∑ i : Fin 3, |regUniformMollifiedVelocity ρ ε hε
                  (forcedRegVelocity ρ a ha f hf ε) z i| +
              2 * |forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z| *
                ∑ i : Fin 3, |forcedRegVelocity ρ a ha f hf ε z i|)) +
          2 * Real.sqrt (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z) ^ (2 : ℕ)) *
            Real.sqrt (∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
              vec3EuclideanNorm (f z - forcePressureGradientField f hf z) ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hbound⟩ := forcedTails_exterior_bound
  refine ⟨C, hC, fun ε hε hε1 hLE T hT R hR t ht => ?_⟩
  let u := forcedRegVelocity ρ a ha f hf ε
  obtain ⟨⟨hSlice, hcont, hinit, hdiv⟩, -, hR2, -, -⟩ := forcedRegularised ρ a ha f hf ε hε
  obtain ⟨hu2, -, hu3, -⟩ := forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T hT
  have hJ3 := forcedRegTransport_memLp_three_slab ρ a ha f hf ε hε T hT
  obtain ⟨-, hgT⟩ := forcePressureGradientField_spec f hf
  obtain ⟨hg2, hgsl⟩ := hgT T hT
  obtain ⟨-, hQfin, -, hpFloc⟩ := forcePressure_spec f hf T hT
  -- the quadratic pressure in `L^{3/2}` on the slab
  obtain ⟨M3, MJ, MP, -, -, hMP, hunif⟩ := forcedLerayLimit_uniform_slab_bounds ρ a ha f hf T hT
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
      lerayPressureLimitSlab T := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hpp : MemLp (fun z => forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    have hm := (hR2 T hT).2.aestronglyMeasurable
    change eLpNorm _ _ _ < ⊤
    have hc := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (3 / 2 : ℝ)) hm hmp
    rw [← hc]
    exact ((hunif ε hε).2.2).trans_lt hMP
  have hpFK : ∀ K : Set Vec3, IsCompact K →
      MemLp (forcePressure f hf) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet K (Ioo 0 T))) := fun K hK =>
      (hpFloc K (Ioo 0 T) hK.measurableSet measurableSet_Ioo subset_rfl).trans_lt
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_lt_top.ne)
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) measure_Ioo_lt_top.ne))
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hQfin.ne))
  have hslices : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) T)),
      MemLp (fun x : Vec3 => forcePressure f hf (x, τ)) 6 volume ∧
        MemLp (fun x : Vec3 => forcePressureGradientField f hf (x, τ)) 2 volume ∧
        HasWeakGradientOn (Set.univ : Set Vec3) (fun x => forcePressure f hf (x, τ))
          (fun x => forcePressureGradientField f hf (x, τ)) := by
    have hPs : StronglyMeasurable (fun q : Vec3 × ℝ => forcePressure f hf q) :=
      (Classical.choose_spec (exists_forcePressure f hf)).1
    have hfin6 : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) T)),
        eLpNorm (fun x : Vec3 => forcePressure f hf (x, τ)) (ENNReal.ofReal (6 : ℝ))
          volume ^ (2 : ℝ) < ⊤ :=
      ae_lt_top' ((measurable_eLpNorm_slice hPs (by norm_num) ENNReal.ofReal_ne_top
        volume).pow_const _).aemeasurable hQfin.ne
    filter_upwards [hfin6, hgsl] with τ h6 hτ
    obtain ⟨⟨hft, hGt⟩, hW⟩ := hτ
    refine ⟨?_, (forcePressureGradientFunction_memLp _ hft).ae_eq hGt.symm, hW⟩
    have hlt : eLpNorm (fun x : Vec3 => forcePressure f hf (x, τ)) (ENNReal.ofReal (6 : ℝ))
        volume < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h6
    rw [ENNReal.ofReal_ofNat] at hlt
    exact hlt
  have hmain := hbound T hT u (regUniformMollifiedVelocity ρ ε hε u) f
    (forcePressureGradientField f hf) (forcedRegGradient ρ a ha f hf ε)
    (forcedRegPressure ρ a ha f hf ε) (forcePressure f hf) hSlice hcont hdiv hu2 hu3 hJ3
    (hR2 T hT).1 (hf T hT) hg2 hpp hpFK hslices hLE R hR t ht
  have hinitial : ∫ x in {x : Vec3 | R < vec3EuclideanNorm x},
      vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) ≤
      ∫ x in {x : Vec3 | R - 1 < vec3EuclideanNorm x}, vec3EuclideanNorm (a x) ^ (2 : ℕ) := by
    refine le_of_eq_of_le ?_ (forcedLerayLimit_initialTail ρ ε hε hε1 a ha.1 R)
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hinit] with x hx
    exact congrArg (fun v => vec3EuclideanNorm v ^ (2 : ℕ)) hx
  linarith only [hmain, hinitial]

end CKN.Leray

end
