-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitTailsForced
public import CKN.Leray.ForcedLerayLimitPropFluxBound
public import CKN.Leray.ForcedRegLocalEnergy
public import CKN.Leray.ForcedLerayLimitPressureBound
public import CKN.Leray.ForcedLerayLimitEnergy
public import CKN.Leray.ForcedHopfSlab
public import CKN.Foundation.ParabolicMeasure

/-!
# Uniform exterior tails of the forced regularized solutions

The sequence half of `lem:forced-tails` in the compactness statement
`prop:forced-limit`: the exterior tail estimate of `lem:forced-tails` for one
forced regularized solution (`CKN.Leray.forcedLerayLimit_forcedTails`, fed by
the local energy inequality `eq:reg-local-energy-forced`) has a right-hand side
that is uniform in `ε ∈ (0,1]`. The slab kinetic energy is bounded by
`lem:forced-energy-bounds`, and the transport and pressure fluxes by the
uniform slab bounds of the velocity, the mollified transport velocity and the
quadratic pressure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The kinetic energy of a forced regularized solution on the slab
`ℝ³ × (0,T)` is at most `T` times the kinetic bound of
`lem:forced-energy-bounds`. -/
private theorem forcedLerayLimitTailsCore_slabKinetic_le
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 < T) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z) ^ (2 : ℕ)) ≤
      T * (Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
        ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)) := by
  let slab : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict slab
  let u : ParabolicPoint → Vec3 := forcedRegVelocity ρ a ha f hf ε
  let kinetic : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, u z i ^ 2
  let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    ∑ i : Fin 3, ∫ z in slab, f z i ^ 2)
  obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, -, henergy⟩ :=
    forcedRegularised ρ a ha f hf ε hε
  have hUmem : MemLp u 2 μ := (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T hT).1
  have hKint : Integrable kinetic μ :=
    integrable_finsetSum _ fun i _ => (hUmem.eval i).integrable_sq
  obtain ⟨hkin, -⟩ := forcedLerayLimit_energy_bounds ρ ε hε a ha.1 f hf u
    (forcedRegGradient ρ a ha f hf ε) hSlice hcont
    (fun S hS => (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε S hS).1)
    (fun S hS => (hR2 S hS).1) (fun t ht => (henergy t ht).2) T hT
  have hpoint (z : ParabolicPoint) :
      vec3EuclideanNorm (u z) ^ (2 : ℕ) = kinetic z := by
    simp only [kinetic, CKN.Foundation.Parabolic.vec3EuclideanNorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u z i))]
  have htimeInt : Integrable
      (fun t : ℝ => ∫ x : Vec3, kinetic (x,t)) (volume.restrict (Ioo 0 T)) := by
    have h := forcedHopf_integrable_timeDensity Set.univ T kinetic hKint
    simp only [Measure.restrict_univ] at h
    exact (integrable_indicator_iff measurableSet_Ioo).1 h
  have htimeBound : ∀ t ∈ Ioo (0 : ℝ) T,
      (∫ x : Vec3, kinetic (x,t)) ≤ E := by
    intro t ht
    calc
      ∫ x : Vec3, kinetic (x,t) =
          ∑ i : Fin 3, ∫ x : Vec3, u (x,t) i ^ 2 := by
        dsimp [kinetic]
        rw [integral_finsetSum Finset.univ
          (fun i _ => ((hSlice t ht.1.le).eval i).integrable_sq)]
      _ ≤ E := hkin t ⟨ht.1.le, ht.2.le⟩
  have htimeIntegral :
      (∫ t in Ioo (0 : ℝ) T, ∫ x : Vec3, kinetic (x,t)) ≤ T * E := by
    calc
      ∫ t in Ioo (0 : ℝ) T, ∫ x : Vec3, kinetic (x,t) ≤
          ∫ t in Ioo (0 : ℝ) T, E := by
        apply integral_mono_ae htimeInt (integrable_const E)
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact htimeBound t ht
      _ = T * E := by
        rw [setIntegral_const]
        simp [smul_eq_mul, hT.le]
  have hslabEq :
      (∫ z in slab, kinetic z) = ∫ t in Ioo (0 : ℝ) T, ∫ x : Vec3, kinetic (x,t) := by
    have h := forcedHopf_setIntegral_slab_eq_intervalIntegral Set.univ T kinetic hKint T
      ⟨hT.le, le_rfl⟩
    simp only [Measure.restrict_univ] at h
    rw [h, intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    exact indicator_of_mem ht _
  calc
    ∫ z in slab, vec3EuclideanNorm (u z) ^ (2 : ℕ) = ∫ z in slab, kinetic z := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = ∫ t in Ioo (0 : ℝ) T, ∫ x : Vec3, kinetic (x,t) := hslabEq
    _ ≤ T * E := htimeIntegral

/-- The sequence half of `lem:forced-tails` in `prop:forced-limit`: on a
finite slab, the exterior slice energy of every forced regularized solution
with `0 < ε ≤ 1` is bounded by the initial tail, the projected-force tail and
constants `C`, `E`, `K` that do not depend on `ε`. -/
theorem forcedLerayLimit_sequenceTail_le
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (T : ℝ) (hT : 0 < T) :
    ∃ C E K : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ 0 ≤ K ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ R : ℝ, 0 < R → ∀ t ∈ Ioo 0 T,
        (∫⁻ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (forcedRegVelocity ρ a ha f hf ε (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
          ∂volume) ≤
        ENNReal.ofReal
          ((∫ x in {x : Vec3 | R - 1 < vec3EuclideanNorm x},
              vec3EuclideanNorm (a x) ^ (2 : ℕ)) +
            C / R ^ 2 * (T * E) + C / R * K +
            2 * Real.sqrt (T * E) *
              Real.sqrt (∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
                vec3EuclideanNorm (f z - forcePressureGradientField f hf z) ^ (2 : ℕ))) := by
  obtain ⟨C, hC, htail⟩ := forcedLerayLimit_forcedTails ρ a ha f hf
  obtain ⟨M3, MJ, MP, hM3, hMJ, hMP, hunif⟩ :=
    forcedLerayLimit_uniform_slab_bounds ρ a ha f hf T hT
  let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
  have hE : 0 ≤ E := by
    have h1 : 0 ≤ ∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2 :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    have h2 : 0 ≤ ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2 :=
      Finset.sum_nonneg fun i _ => setIntegral_nonneg
        (MeasurableSet.univ.prod measurableSet_Ioo) fun z _ => sq_nonneg _
    positivity
  let M3' : ℝ≥0∞ := 3 * M3
  let K : ℝ := (M3' ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3')).toReal
  refine ⟨C, E, K, hC, hE, ENNReal.toReal_nonneg, fun ε hε hε1 R hR t ht => ?_⟩
  let U := forcedRegVelocity ρ a ha f hf ε
  have hS : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  obtain ⟨⟨hSlice, -, -, -⟩, -, hR2, -, -⟩ := forcedRegularised ρ a ha f hf ε hε
  have h := htail ε hε hε1 (forcedRegLocalEnergy ρ a ha f hf ε hε) T hT R hR t
    ⟨ht.1.le, ht.2.le⟩
  -- the slab kinetic energy
  have hI2 := forcedLerayLimitTailsCore_slabKinetic_le ρ a ha f hf ε hε T hT
  have hI2nn : 0 ≤ ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      vec3EuclideanNorm (U z) ^ (2 : ℕ) :=
    setIntegral_nonneg hS fun z _ => by positivity
  -- the flux bound
  have hUmem := forcedRegVelocity_memLp_slab ρ a ha f hf ε hε T hT
  have hUbound : eLpNorm (fun z => vec3EuclideanNorm (U z)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ M3' := by
    have hcomp : ∀ i : Fin 3, MemLp (fun z => U z i) 3
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      fun i => hUmem.2.2.1.eval i
    calc eLpNorm (fun z => vec3EuclideanNorm (U z)) 3 _
        ≤ eLpNorm (fun z => ∑ i : Fin 3, ‖U z i‖) 3
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
          refine eLpNorm_mono
            (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
              hUmem.1.aestronglyMeasurable) (fun z => ?_)
          rw [Real.norm_of_nonneg (show 0 ≤ vec3EuclideanNorm (U z) from Real.sqrt_nonneg _),
            Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
          simpa only [Real.norm_eq_abs] using vec3EuclideanNorm_le_sum_abs (U z)
      _ ≤ ∑ i : Fin 3, eLpNorm (fun z => ‖U z i‖) 3
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
          eLpNorm_sum_le (p := 3) (s := (Finset.univ : Finset (Fin 3)))
            (f := fun i => fun z => ‖U z i‖) (by norm_num)
      _ = ∑ i : Fin 3, eLpNorm (fun z => U z i) 3
            (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact eLpNorm_norm _ (hcomp i).aestronglyMeasurable
      _ ≤ ∑ _i : Fin 3, M3 := Finset.sum_le_sum fun i _ => (hunif ε hε).1 i
      _ = M3' := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num [M3']
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
      lerayPressureLimitSlab T := by
    ext z
    rfl
  have hmp := parabolicHomeomorphSymm_measurePreserving.restrict_preimage hS
  rw [hpre] at hmp
  have hPm := (hR2 T hT).2.aestronglyMeasurable
  have hPbound : eLpNorm (fun z => forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z)
      (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MP := by
    have hc := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (3 / 2 : ℝ)) hPm hmp
    rw [← hc]
    exact (hunif ε hε).2.2
  have hflux := forcedLerayLimit_flux_integral_bound T U
    (regUniformMollifiedVelocity ρ ε hε U)
    (fun z => forcedRegPressure ρ a ha f hf ε z - forcePressure f hf z) M3' MJ MP
    (ENNReal.mul_lt_top (by norm_num) hM3) hMJ hMP hUmem.1.aestronglyMeasurable
    (forcedRegTransport_memLp_three_slab ρ a ha f hf ε hε T hT).aestronglyMeasurable hPm
    hUbound (fun i => (hunif ε hε).2.1 i) hPbound
  -- the left-hand side as a real integral
  have hmem := hSlice t ht.1.le
  have hint : Integrable (fun x : Vec3 => vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ)) := by
    have hsum : Integrable (fun x : Vec3 => ∑ i : Fin 3, U (x, t) i ^ 2) :=
      integrable_finsetSum _ fun i _ => (hmem.eval i).integrable_sq
    refine hsum.congr (Eventually.of_forall fun x => ?_)
    simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hpt : ∀ x : Vec3, ‖(WithLp.toLp 2 (U (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ)) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ← vec3EuclideanNorm_eq_l2, Real.rpow_two]
  have hlhs : (∫⁻ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (U (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (∫ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
        vec3EuclideanNorm (U (x, t)) ^ (2 : ℕ)) := by
    simp only [hpt]
    exact (ofReal_integral_eq_lintegral_ofReal hint.integrableOn
      (Eventually.of_forall fun x => by positivity)).symm
  change (∫⁻ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (U (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ _
  rw [hlhs]
  refine ENNReal.ofReal_le_ofReal (h.trans ?_)
  have hCR2 : 0 ≤ C / R ^ 2 := by positivity
  have hCR : 0 ≤ C / R := by positivity
  have hsq := Real.sqrt_le_sqrt hI2
  have hft : 0 ≤ Real.sqrt (∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
      vec3EuclideanNorm (f z - forcePressureGradientField f hf z) ^ (2 : ℕ)) :=
    Real.sqrt_nonneg _
  gcongr

end CKN.Leray

end
