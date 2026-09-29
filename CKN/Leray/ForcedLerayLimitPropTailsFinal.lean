-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitPropTailsCore
public import CKN.Leray.LerayLimitTailLimit
public import CKN.Leray.CompactnessEnergyLower
public import CKN.Leray.ForcedLerayLimitForceGradient

/-!
# The uniform spatial tails in `prop:forced-limit`

`lem:forced-tails` along the subsequence of the compactness step of
`prop:forced-limit`: the exterior slice energies of the forced regularized
velocities and of their local weak limit are bounded, uniformly in the index
and in time on `(0,T)`, by one sequence `S m → 0`. The sequence bound is the
uniform tail estimate `CKN.Leray.forcedLerayLimit_sequenceTail_le`; its terms
vanish as the radius grows because the datum and the force are square
integrable; the bound passes to the limit by weak lower semicontinuity on the
compact pieces of the exterior.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The compact pieces `{R + 1/(k+1) ≤ |x|} ∩ B̄_k` of the Euclidean
exterior `{R < |x|}`. -/
def forcedLerayLimitTailsFinalPiece (R : ℝ) (k : ℕ) : Set Vec3 :=
  {x : Vec3 | R + ((k : ℝ) + 1)⁻¹ ≤ vec3EuclideanNorm x} ∩
    Metric.closedBall (0 : Vec3) (k : ℝ)

private theorem forcedLerayLimitTailsFinalPiece_isCompact (R : ℝ) (k : ℕ) :
    IsCompact (forcedLerayLimitTailsFinalPiece R k) :=
  (isCompact_closedBall (0 : Vec3) (k : ℝ)).of_isClosed_subset
    ((isClosed_le continuous_const
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).inter Metric.isClosed_closedBall)
    inter_subset_right

private theorem forcedLerayLimitTailsFinalPiece_subset (R : ℝ) (k : ℕ) :
    forcedLerayLimitTailsFinalPiece R k ⊆ {x : Vec3 | R < vec3EuclideanNorm x} := by
  intro x hx
  have hk : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  have hRk : R < R + ((k : ℝ) + 1)⁻¹ := by linarith only [hk]
  exact lt_of_lt_of_le hRk hx.1

/-- A uniform bound on the exterior energy `∫_{|x|>R} |F_n|²` passes to a
measurable limit that is a weak `L²` limit on every compact set. -/
private theorem forcedLerayLimitTailsFinal_exterior_le
    (R : ℝ) (F : ℕ → Vec3 → Vec3) (G : Vec3 → Vec3) (hGmeas : Measurable G)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hFbound : ∀ n, (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ B)
    (hlocal : ∀ C : Set Vec3, IsCompact C →
      ∃ hF : ∀ n, MemLp (fun x : Vec3 => (WithLp.toLp 2 (F n x) : L2Vec3))
        2 (volume.restrict C),
      ∃ hG : MemLp (fun x : Vec3 => (WithLp.toLp 2 (G x) : L2Vec3))
        2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun n => inner ℝ
          ((hF n).toLp (fun x => WithLp.toLp 2 (F n x))) w) atTop
          (nhds (inner ℝ (hG.toLp (fun x => WithLp.toLp 2 (G x))) w))) :
    (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ B := by
  let E : Set Vec3 := {x : Vec3 | R < vec3EuclideanNorm x}
  let K : ℕ → Set Vec3 := forcedLerayLimitTailsFinalPiece R
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  have hK : AECover (volume.restrict E) atTop K := by
    refine aecover_restrict_of_ae_imp hEmeas ?_ ?_
    · filter_upwards [] with x hx
      have hx' : 0 < vec3EuclideanNorm x - R := by
        have : R < vec3EuclideanNorm x := hx
        linarith only [this]
      have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h1 : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1)⁻¹ < vec3EuclideanNorm x - R :=
        hinv.eventually (gt_mem_nhds hx')
      have h2 : ∀ᶠ k : ℕ in atTop, ‖x‖ ≤ (k : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually_ge_atTop _
      filter_upwards [h1, h2] with k hk1 hk2
      refine ⟨?_, ?_⟩
      · show R + ((k : ℝ) + 1)⁻¹ ≤ vec3EuclideanNorm x
        linarith only [hk1]
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hk2
    · intro k
      exact (forcedLerayLimitTailsFinalPiece_isCompact R k).measurableSet
  have hrestr : ∀ k, (volume.restrict E).restrict (K k) = volume.restrict (K k) :=
    fun k => Measure.restrict_restrict_of_subset (forcedLerayLimitTailsFinalPiece_subset R k)
  have hFK : ∀ k n, (∫⁻ x in K k, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
      ∂(volume.restrict E)) ≤ B := by
    intro k n
    rw [hrestr k]
    exact (lintegral_mono_set (forcedLerayLimitTailsFinalPiece_subset R k)).trans (hFbound n)
  have htransfer : ∀ k,
      (∀ n, (∫⁻ x in K k, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict E)) ≤ B) →
      (∫⁻ x in K k, ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict E)) ≤ B := by
    intro k hk
    obtain ⟨hF, hG, hweak⟩ := hlocal (K k) (forcedLerayLimitTailsFinalPiece_isCompact R k)
    have hsource : ∀ n, (∫⁻ x, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict (K k))) ≤ B := by
      intro n
      have h := hk n
      rw [hrestr k] at h
      exact h
    have hlim := lintegral_enorm_sq_le_of_weak_l2_bounded
      (μ := volume.restrict (K k))
      (f := fun n x => (WithLp.toLp 2 (F n x) : L2Vec3))
      (g := hG.toLp (fun x => WithLp.toLp 2 (G x)))
      (hf := hF) (hweak := hweak) (B := B) (hB := hB) (hbound := hsource)
    rw [hrestr k]
    calc (∫⁻ x, ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (K k)))
        = ∫⁻ x, ‖hG.toLp (fun x => WithLp.toLp 2 (G x)) x‖ₑ ^ (2 : ℝ)
            ∂(volume.restrict (K k)) := by
          apply lintegral_congr_ae
          filter_upwards [hG.coeFn_toLp] with x hx
          rw [← hx]
      _ ≤ B := hlim
  have hGae : AEMeasurable (fun x : Vec3 => (WithLp.toLp 2 (G x) : L2Vec3))
      (volume.restrict E) :=
    ((PiLp.continuous_toLp 2 _).measurable.comp hGmeas).aemeasurable
  exact lerayLimit_lintegral_bound_of_compactExhaustion (μ := volume) E K hK
    (fun n x => (WithLp.toLp 2 (F n x) : L2Vec3))
    (fun x => (WithLp.toLp 2 (G x) : L2Vec3)) B hFK htransfer hGae

/-- `lem:forced-tails` in `prop:forced-limit`: along the subsequence `σ` of the
compactness step, with local weak limit `v`, the exterior slice energies
beyond the radius `2(m+1)` of the forced regularized velocities and of `v` are
bounded on `(0,T)` by one sequence `S m → 0`. -/
theorem forcedLerayLimit_spatialTails_with_limit
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (σ : ℕ → ℕ)
    (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
    (T : ℝ) (hT : 0 < T)
    (hlocal : ∀ t : ℝ, 0 < t → ∀ C : Set Vec3, IsCompact C →
      ∃ hs : ∀ k, MemLp
        (fun x : Vec3 => (WithLp.toLp 2
          (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))
        2 (volume.restrict C),
      ∃ hvC : MemLp (fun x : Vec3 => (WithLp.toLp 2 (v (x,t)) : L2Vec3))
        2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun k => inner ℝ ((hs k).toLp
          (fun x => (WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))) w)
          atTop (nhds (inner ℝ (hvC.toLp
            (fun x => (WithLp.toLp 2 (v (x,t)) : L2Vec3))) w))) :
    ∃ S : ℕ → ℝ≥0∞, Tendsto S atTop (𝓝 0) ∧
      (∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
          ∂volume) ≤ S m) ∧
      (∀ (m : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (v (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m) := by
  obtain ⟨C, E, K, hC, hE, hK, hcore⟩ := forcedLerayLimit_sequenceTail_le ρ a ha f hf T hT
  let Ft : ℝ → ℝ := fun R =>
    ∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
      vec3EuclideanNorm (f z - forcePressureGradientField f hf z) ^ (2 : ℕ)
  let B : ℕ → ℝ := fun m =>
    (∫ x in {x : Vec3 | ((m : ℝ) + 1) - 1 < vec3EuclideanNorm x},
        vec3EuclideanNorm (a x) ^ (2 : ℕ)) +
      C / ((m : ℝ) + 1) ^ 2 * (T * E) + C / ((m : ℝ) + 1) * K +
      2 * Real.sqrt (T * E) * Real.sqrt (Ft ((m : ℝ) + 1))
  let S : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (B m)
  have hseqS : ∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
      (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
        ‖(WithLp.toLp 2
          (forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂volume) ≤ S m := fun m n t ht =>
    hcore (εseq (σ n)) (hseq (σ n)).1 (hseq (σ n)).2 ((m : ℝ) + 1) (by positivity) t ht
  refine ⟨S, ?_, hseqS, fun m t ht => ?_⟩
  · -- the initial-data tail vanishes
    have h1 : Tendsto (fun m : ℕ => ∫ x in {x : Vec3 | ((m : ℝ) + 1) - 1 < vec3EuclideanNorm x},
        vec3EuclideanNorm (a x) ^ (2 : ℕ)) atTop (𝓝 0) := by
      let s : ℕ → Set Vec3 := fun m => {x : Vec3 | ((m : ℝ) + 1) - 1 < vec3EuclideanNorm x}
      have hsm : ∀ m, MeasurableSet (s m) := fun m =>
        measurableSet_lt measurable_const
          CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
      have hanti : Antitone s := by
        intro i j hij x hx
        have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
        change ((i : ℝ) + 1) - 1 < vec3EuclideanNorm x
        have : ((j : ℝ) + 1) - 1 < vec3EuclideanNorm x := hx
        linarith only [this, hij']
      have hint : Integrable (fun x : Vec3 => vec3EuclideanNorm (a x) ^ (2 : ℕ)) := by
        have hsum : Integrable (fun x : Vec3 => ∑ i : Fin 3, a x i ^ 2) :=
          integrable_finsetSum _ fun i _ => (ha.1.eval i).integrable_sq
        refine hsum.congr (Eventually.of_forall fun x => ?_)
        simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm]
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      have hempty : (⋂ m, s m) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
        obtain ⟨m, hm⟩ := exists_nat_gt (vec3EuclideanNorm x)
        have h := mem_iInter.1 hx m
        change ((m : ℝ) + 1) - 1 < vec3EuclideanNorm x at h
        linarith only [h, hm]
      have h := tendsto_setIntegral_of_antitone hsm hanti ⟨0, hint.integrableOn⟩
      rwa [hempty, Measure.restrict_empty, integral_zero_measure] at h
    -- the projected-force tail vanishes
    have hforce : Tendsto (fun m : ℕ => Ft ((m : ℝ) + 1)) atTop (𝓝 0) := by
      let g : ParabolicPoint → Vec3 := fun z => f z - forcePressureGradientField f hf z
      let s : ℕ → Set ParabolicPoint := fun m =>
        spaceTimeSet {x : Vec3 | (m : ℝ) + 1 < vec3EuclideanNorm x} (Ioo 0 T)
      have hsm : ∀ m, MeasurableSet (s m) := fun m =>
        (measurableSet_lt measurable_const
          CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable).prod
          measurableSet_Ioo
      have hanti : Antitone s := by
        intro i j hij z hz
        have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
        refine ⟨?_, hz.2⟩
        have : (j : ℝ) + 1 < vec3EuclideanNorm z.1 := hz.1
        change (i : ℝ) + 1 < vec3EuclideanNorm z.1
        linarith only [this, hij']
      have hg : MemLp g 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
        (hf T hT).sub ((forcePressureGradientField_spec f hf).2 T hT).1
      have hint : IntegrableOn (fun z => vec3EuclideanNorm (g z) ^ (2 : ℕ)) (s 0) := by
        have hsum : IntegrableOn (fun z => ∑ i : Fin 3, g z i ^ 2)
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
          integrable_finsetSum _ fun i _ => (hg.eval i).integrable_sq
        have hsub : s 0 ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
          fun z hz => ⟨Set.mem_univ _, hz.2⟩
        refine (hsum.mono_set hsub).congr_fun (fun z _ => ?_) (hsm 0)
        simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm]
        rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      have hempty : (⋂ m, s m) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
        obtain ⟨m, hm⟩ := exists_nat_gt (vec3EuclideanNorm z.1)
        have h := (mem_iInter.1 hz m).1
        change (m : ℝ) + 1 < vec3EuclideanNorm z.1 at h
        linarith only [h, hm]
      have h := tendsto_setIntegral_of_antitone hsm hanti ⟨0, hint⟩
      rw [hempty, Measure.restrict_empty, integral_zero_measure] at h
      exact h
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa [one_div] using h
    have h2 : Tendsto (fun m : ℕ => C / ((m : ℝ) + 1) ^ 2 * (T * E)) atTop (𝓝 0) := by
      have h := ((hinv.pow 2).const_mul C).mul_const (T * E)
      simpa [div_eq_mul_inv, inv_pow] using h
    have h3 : Tendsto (fun m : ℕ => C / ((m : ℝ) + 1) * K) atTop (𝓝 0) := by
      have h := (hinv.const_mul C).mul_const K
      simpa [div_eq_mul_inv] using h
    have h4 : Tendsto (fun m : ℕ => 2 * Real.sqrt (T * E) * Real.sqrt (Ft ((m : ℝ) + 1)))
        atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hforce
      have h' := h.const_mul (2 * Real.sqrt (T * E))
      simpa [Function.comp_def] using h'
    have hB : Tendsto B atTop (𝓝 0) := by
      have h := ((h1.add h2).add h3).add h4
      simpa [B] using h
    have h := ENNReal.tendsto_ofReal hB
    simpa [S] using h
  · -- the limit inherits the bound
    exact forcedLerayLimitTailsFinal_exterior_le (2 * ((m : ℝ) + 1))
      (fun n x => forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x, t)) (fun x => v (x, t))
      (hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3))))
      (S m) ENNReal.ofReal_lt_top (fun n => hseqS m n t ht)
      (fun Cset hCset => hlocal t ht.1 Cset hCset)

end CKN.Leray

end
