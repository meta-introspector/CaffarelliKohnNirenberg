-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitTailsTime
public import CKN.Leray.ForcedHopfPairing
public import CKN.Leray.StabilityBoundedPairing
public import CKN.Core.Endgame.UniformCutoffFamilySeparated

/-!
# The localized energy inequality between two times

In the proof of `lem:forced-tails` the local energy inequality
`eq:reg-local-energy-forced` of a forced regularized solution is tested with
q(x) θ(t) for a fixed smooth, nonnegative, compactly supported spatial weight
q and nonnegative time tests θ. By Fubini this is a distributional
inequality in time for the weighted kinetic energy ∫ |u(t)|² q, and continuity
of that energy turns it into an inequality between the times 0 and t: the
increase is at most the space-time integral of the localized energy density
`forcedTailsLocalDensity` over K × (0,t).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

local instance forcedTailsHolderThreeThree :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using hreal.ennrealOfReal

local instance forcedTailsHolderThreeHalvesThree :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using
    hreal.ennrealOfReal

/-- The localized energy density of `lem:forced-tails` for a spatial weight
q: the right side of `eq:reg-local-energy-forced` for the test q, minus
twice the weighted dissipation. -/
def forcedTailsLocalDensity (u J f : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ) (q : Vec3 → ℝ)
    (z : ParabolicPoint) : ℝ :=
  vec3EuclideanNorm (u z) ^ (2 : ℕ) * (∑ i : Fin 3, mixedSecond q i i z.1) +
    ∑ i : Fin 3, (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
      spatialDeriv q i z.1 +
    2 * (∑ i : Fin 3, f z i * u z i) * q z.1 -
    2 * spatialGradientSq u Du z * q z.1

/-- The squared Euclidean norm on Vec3 is the sum of the squared coordinates. -/
theorem forcedTails_vec3EuclideanNorm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ (2 : ℕ) = ∑ i : Fin 3, v i ^ 2 := by
  rw [vec3EuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]

/-- The localized energy density is integrable on K × (0,T) when the
velocity is in L² and L³, the transport field in L³, the gradient and
the force in L² on the slab, and the pressure in L^{3/2} on K × (0,T). -/
theorem forcedTails_localDensity_integrable {T : ℝ}
    {u J f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {q : Vec3 → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {K : Set Vec3} (hK : IsCompact K) (hqK : tsupport q ⊆ K)
    (hu : MemLp u 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hu2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ : MemLp J 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K (Ioo 0 T)))) :
    Integrable (forcedTailsLocalDensity u J f Du p q)
      (volume.restrict (spaceTimeSet K (Ioo 0 T))) := by
  let νK : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T))
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK T
  have hνK : νK ≤ volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
  have hqc : HasCompactSupport q := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hqK
  have hdq : ∀ i, HasCompactSupport (spatialDeriv q i) := fun i =>
    hqc.fderiv_apply (𝕜 := ℝ) _
  have hbq : MemLp (fun z : ParabolicPoint => q z.1) ∞ νK :=
    forcedHopf_memLp_top_spatial hq.continuous hqc
  have hbd : ∀ i, MemLp (fun z : ParabolicPoint => spatialDeriv q i z.1) ∞ νK := fun i =>
    forcedHopf_spatialDeriv_memLp_top hq hqc i
  have hbm : ∀ i, MemLp (fun z : ParabolicPoint => mixedSecond q i i z.1) ∞ νK := fun i =>
    forcedHopf_spatialDeriv_memLp_top (contDiff_spatialDeriv_smooth hq i) (hdq i) i
  have hU3 : ∀ i, MemLp (fun z => u z i) 3 νK := fun i => (hu.mono_measure hνK).eval i
  have hJ3 : ∀ i, MemLp (fun z => J z i) 3 νK := fun i => (hJ.mono_measure hνK).eval i
  have hN : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) νK := by
    have h : Integrable (fun z => ∑ i : Fin 3, u z i ^ 2) νK :=
      integrable_finsetSum _ fun i _ => ((hu2.mono_measure hνK).eval i).integrable_sq
    exact h.congr (Eventually.of_forall fun z => (forcedTails_vec3EuclideanNorm_sq (u z)).symm)
  have htriple : ∀ i, Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i) νK := by
    intro i
    have h : Integrable (fun z => ∑ k : Fin 3, u z k * u z k * J z i) νK := by
      refine integrable_finsetSum _ fun k _ => ?_
      have h1 : MemLp ((fun z => u z k) * fun z => u z k) (ENNReal.ofReal (3 / 2 : ℝ)) νK :=
        (hU3 k).mul (hU3 k)
      have h2 : MemLp (((fun z => u z k) * fun z => u z k) * fun z => J z i) 1 νK :=
        h1.mul (hJ3 i)
      exact memLp_one_iff_integrable.1 h2
    refine h.congr (Eventually.of_forall fun z => ?_)
    show ∑ k : Fin 3, u z k * u z k * J z i = vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i
    rw [forcedTails_vec3EuclideanNorm_sq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hpu : ∀ i, Integrable (fun z => p z * u z i) νK := fun i =>
    memLp_one_iff_integrable.1 (hp.mul (hU3 i) : MemLp (p * fun z => u z i) 1 νK)
  have hA : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) *
      (∑ i : Fin 3, mixedSecond q i i z.1)) νK := by
    have h : Integrable (fun z => ∑ i : Fin 3,
        vec3EuclideanNorm (u z) ^ (2 : ℕ) * mixedSecond q i i z.1) νK :=
      integrable_finsetSum _ fun i _ =>
        stability_integrable_mul_bounded_test νK le_rfl (memLp_one_iff_integrable.2 hN) (hbm i)
    exact h.congr (Eventually.of_forall fun z => by simp only [Finset.mul_sum])
  have hB : Integrable (fun z => ∑ i : Fin 3,
      (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
        spatialDeriv q i z.1) νK := by
    refine integrable_finsetSum _ fun i _ => ?_
    have h1 := stability_integrable_mul_bounded_test νK le_rfl
      (memLp_one_iff_integrable.2 (htriple i)) (hbd i)
    have h2 := stability_integrable_mul_bounded_test νK le_rfl
      (memLp_one_iff_integrable.2 ((hpu i).const_mul 2)) (hbd i)
    refine (h1.add h2).congr (Eventually.of_forall fun z => ?_)
    show vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i * spatialDeriv q i z.1 +
        2 * (p z * u z i) * spatialDeriv q i z.1 =
      (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * p z * u z i) * spatialDeriv q i z.1
    ring
  have hC : Integrable (fun z => 2 * (∑ i : Fin 3, f z i * u z i) * q z.1) νK := by
    have hfu : Integrable (fun z => ∑ i : Fin 3, f z i * u z i) νK :=
      integrable_finsetSum _ fun i _ =>
        ((hf.mono_measure hνK).eval i).integrable_mul ((hu2.mono_measure hνK).eval i)
    exact stability_integrable_mul_bounded_test νK le_rfl
      (memLp_one_iff_integrable.2 (hfu.const_mul 2)) hbq
  have hD : Integrable (fun z => 2 * spatialGradientSq u Du z * q z.1) νK := by
    have hs : Integrable (fun z => spatialGradientSq u Du z) νK := by
      unfold spatialGradientSq
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (((hDu.mono_measure hνK).eval i).eval j).integrable_sq
    exact stability_integrable_mul_bounded_test νK le_rfl
      (memLp_one_iff_integrable.2 (hs.const_mul 2)) hbq
  exact ((hA.add hB).add hC).sub hD

/-- Fubini on the slab K × (0,T) for a density times a function of time. -/
private theorem forcedTails_slab_fubini {K : Set Vec3} {T : ℝ} {g : ParabolicPoint → ℝ}
    {η : ℝ → ℝ}
    (hg : Integrable (fun z : ParabolicPoint => g z * η z.2)
      (volume.restrict (spaceTimeSet K (Ioo 0 T)))) :
    ∫ z in spaceTimeSet K (Ioo 0 T), g z * η z.2 =
      ∫ τ in Ioo 0 T, (∫ x in K, g (x, τ)) * η τ := by
  have hg' : Integrable (fun z : Vec3 × ℝ => g z * η z.2)
      ((volume.restrict K).prod (volume.restrict (Ioo 0 T))) := by
    rw [← forcedHopf_slab_measure_eq_prod]
    exact hg
  change ∫ z : Vec3 × ℝ, g z * η z.2 ∂((volume : Measure ParabolicPoint).restrict
    (spaceTimeSet K (Ioo 0 T)) : Measure (Vec3 × ℝ)) = _
  rw [forcedHopf_slab_measure_eq_prod]
  refine (integral_prod_symm (fun z : Vec3 × ℝ => g z * η z.2) hg').trans ?_
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  exact integral_mul_const (η τ) _

/-- The localized energy inequality of `lem:forced-tails` between the times
0 and t: for a smooth, nonnegative spatial weight q supported in a
compact K, the local energy inequality `eq:reg-local-energy-forced` and
continuity of the weighted kinetic energy give
∫ |u(t)|² q - ∫ |u(0)|² q ≤ ∫_{K × (0,t)} forcedTailsLocalDensity. -/
theorem forcedTails_localized_energy_le {T : ℝ} (hT : 0 < T)
    {u J f : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {q : Vec3 → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hq0 : ∀ x, 0 ≤ q x) {K : Set Vec3} (hK : IsCompact K) (hqK : tsupport q ⊆ K)
    (hu : MemLp u 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hu2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ : MemLp J 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K (Ioo 0 T))))
    (hY : ContinuousOn (fun τ => ∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ) * q x)
      (Icc 0 T))
    (hLE : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
                spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * u z i) * ψ z) :
    ∀ t ∈ Icc 0 T,
      (∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * q x) -
          ∫ x : Vec3, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) * q x ≤
        ∫ z in spaceTimeSet K (Ioo 0 t), forcedTailsLocalDensity u J f Du p q z := by
  let νK : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T))
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK T
  have hνK : νK ≤ volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
  have hqc : HasCompactSupport q := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hqK
  let G : ParabolicPoint → ℝ := forcedTailsLocalDensity u J f Du p q
  have hG : Integrable G νK :=
    forcedTails_localDensity_integrable hq hK hqK hu hu2 hJ hDu hf hp
  let F : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) * q z.1
  have hF : Integrable F νK := by
    have hN : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) νK := by
      have h : Integrable (fun z => ∑ i : Fin 3, u z i ^ 2) νK :=
        integrable_finsetSum _ fun i _ => ((hu2.mono_measure hνK).eval i).integrable_sq
      exact h.congr (Eventually.of_forall fun z =>
        (forcedTails_vec3EuclideanNorm_sq (u z)).symm)
    exact stability_integrable_mul_bounded_test νK le_rfl (memLp_one_iff_integrable.2 hN)
      (forcedHopf_memLp_top_spatial hq.continuous hqc)
  let S : ParabolicPoint → ℝ := fun z => 2 * spatialGradientSq u Du z * q z.1
  have hS : Integrable S νK := by
    have hs : Integrable (fun z => spatialGradientSq u Du z) νK := by
      unfold spatialGradientSq
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (((hDu.mono_measure hνK).eval i).eval j).integrable_sq
    exact stability_integrable_mul_bounded_test νK le_rfl
      (memLp_one_iff_integrable.2 (hs.const_mul 2))
      (forcedHopf_memLp_top_spatial hq.continuous hqc)
  -- vanishing off K
  have hq0K : ∀ x, x ∉ K → q x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hqK h))
  have hdq0 : ∀ i x, x ∉ K → spatialDeriv q i x = 0 := by
    intro i x hx
    have h : fderiv ℝ q x = 0 := by
      by_contra hne
      exact hx (hqK (support_fderiv_subset ℝ (Function.mem_support.mpr hne)))
    simp only [spatialDeriv, h, zero_apply]
  have hmq0 : ∀ i x, x ∉ K → mixedSecond q i i x = 0 := by
    intro i x hx
    have hts : tsupport (spatialDeriv q i) ⊆ K :=
      (tsupport_fderiv_apply_subset ℝ _).trans hqK
    have h : fderiv ℝ (spatialDeriv q i) x = 0 := by
      by_contra hne
      exact hx (hts (support_fderiv_subset ℝ (Function.mem_support.mpr hne)))
    simp only [mixedSecond, spatialDeriv, h, zero_apply]
  have hGoff : ∀ z : ParabolicPoint, z.1 ∉ K → G z = 0 := by
    intro z hz
    simp only [G, forcedTailsLocalDensity, hq0K _ hz, hdq0 _ _ hz, hmq0 _ _ hz, mul_zero,
      Finset.sum_const_zero, add_zero, sub_zero]
  -- the scalar weak inequality
  let Y : ℝ → ℝ := fun τ => ∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ) * q x
  let H : ℝ → ℝ := fun τ => ∫ x in K, G (x, τ)
  have hYK : ∀ τ, ∫ x in K, F (x, τ) = Y τ := fun τ =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp only [F, hq0K x hx, mul_zero]
  have hbtime : ∀ η : ℝ → ℝ, Continuous η → HasCompactSupport η →
      MemLp (fun z : ParabolicPoint => η z.2) ∞ νK := by
    intro η hη hηc
    obtain ⟨C, hC⟩ := hη.bounded_above_of_compact_support hηc
    exact memLp_top_of_bound (hη.measurable.comp measurable_snd).aestronglyMeasurable C
      (ae_of_all _ fun z => hC z.2)
  have hweak : ∀ θ : ℝ → ℝ, IsIntervalTest (Ioo 0 T) θ → (∀ τ, 0 ≤ θ τ) →
      -(∫ τ in Ioo 0 T, Y τ * deriv θ τ) ≤ ∫ τ in Ioo 0 T, H τ * θ τ := by
    intro θ hθ hθ0
    obtain ⟨hθs, hθc, hθsupp⟩ := hθ
    have hdθs : Continuous (deriv θ) := hθs.continuous_deriv (by simp)
    have hdθc : HasCompactSupport (deriv θ) := hθc.deriv
    let ψ : ParabolicPoint → ℝ := fun z => q z.1 * θ z.2
    have hψtest : ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) := by
      have hts := CKN.Core.Endgame.tsupport_separatedProduct_subset q θ
      refine ⟨CKN.Core.Endgame.contDiff_separatedProduct hq hθs, ?_, ?_⟩
      · exact IsCompact.of_isClosed_subset (hqc.prod hθc) (isClosed_tsupport _) hts
      · exact hts.trans (Set.prod_mono (subset_univ _) (hθsupp.trans Ioo_subset_Ioi_self))
    have hψ0 : ∀ z, 0 ≤ ψ z := fun z => mul_nonneg (hq0 z.1) (hθ0 z.2)
    have h := hLE ψ hψtest hψ0
    have htime : ∀ z : ParabolicPoint, timePartial ψ z = q z.1 * deriv θ z.2 := fun z =>
      CKN.Core.Endgame.timePartial_separatedProduct q hθs z
    have hspace : ∀ i (z : ParabolicPoint), spatialPartial ψ i z = spatialDeriv q i z.1 * θ z.2 :=
      fun i z => CKN.Core.Endgame.spatialPartial_separatedProduct θ hq i z
    have hsecond : ∀ i (z : ParabolicPoint),
        spatialSecondPartial ψ i i z = mixedSecond q i i z.1 * θ z.2 := fun i z =>
      CKN.Core.Endgame.spatialSecondPartial_separatedProduct θ hq i i z
    have hR : ∀ z : ParabolicPoint,
        (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
              spatialPartial ψ i z +
          2 * (∑ i : Fin 3, f z i * u z i) * ψ z =
        F z * deriv θ z.2 + G z * θ z.2 + S z * θ z.2 := by
      intro z
      simp only [htime, hsecond, hspace, F, G, S, ψ, forcedTailsLocalDensity,
        Fin.sum_univ_three]
      ring
    have hL : ∀ z : ParabolicPoint, spatialGradientSq u Du z * ψ z = S z * θ z.2 / 2 := by
      intro z
      simp only [S, ψ]
      ring
    simp only [hR, hL] at h
    -- restrict both integrals to K × (0,T)
    have hsub : spaceTimeSet K (Ioo 0 T) ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      Set.prod_mono (subset_univ K) Ioo_subset_Ioi_self
    have hmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) :=
      MeasurableSet.univ.prod measurableSet_Ioi
    have hoff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)) \ spaceTimeSet K (Ioo 0 T),
        (z.1 ∉ K) ∨ (θ z.2 = 0 ∧ deriv θ z.2 = 0) := by
      intro z hz
      by_cases hzK : z.1 ∈ K
      · right
        have hzt : z.2 ∉ tsupport θ := fun h => hz.2 ⟨hzK, hθsupp h⟩
        refine ⟨image_eq_zero_of_notMem_tsupport hzt, ?_⟩
        by_contra hne
        exact hzt (support_deriv_subset (Function.mem_support.mpr hne))
      · left
        exact hzK
    have hFoff : ∀ z : ParabolicPoint, z.1 ∉ K → F z = 0 := fun z hz => by
      simp only [F, hq0K _ hz, mul_zero]
    have hSoff : ∀ z : ParabolicPoint, z.1 ∉ K → S z = 0 := fun z hz => by
      simp only [S, hq0K _ hz, mul_zero]
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub,
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub] at h
    rotate_left
    · intro z hz
      rcases hoff z hz with h1 | ⟨h1, h2⟩
      · rw [hFoff z h1, hGoff z h1, hSoff z h1]
        ring
      · rw [h1, h2]
        ring
    · intro z hz
      rcases hoff z hz with h1 | ⟨h1, _⟩
      · rw [hSoff z h1]
        ring
      · rw [h1]
        ring
    have hFθ : Integrable (fun z : ParabolicPoint => F z * deriv θ z.2) νK :=
      stability_integrable_mul_bounded_test νK le_rfl (memLp_one_iff_integrable.2 hF)
        (hbtime _ hdθs hdθc)
    have hGθ : Integrable (fun z : ParabolicPoint => G z * θ z.2) νK :=
      stability_integrable_mul_bounded_test νK le_rfl (memLp_one_iff_integrable.2 hG)
        (hbtime _ hθs.continuous hθc)
    have hSθ : Integrable (fun z : ParabolicPoint => S z * θ z.2) νK :=
      stability_integrable_mul_bounded_test νK le_rfl (memLp_one_iff_integrable.2 hS)
        (hbtime _ hθs.continuous hθc)
    have e1 := integral_add (μ := volume.restrict (spaceTimeSet K (Ioo 0 T)))
      (f := fun z : ParabolicPoint => F z * deriv θ z.2 + G z * θ z.2)
      (g := fun z : ParabolicPoint => S z * θ z.2) (hFθ.add hGθ) hSθ
    have e2 := integral_add (μ := volume.restrict (spaceTimeSet K (Ioo 0 T)))
      (f := fun z : ParabolicPoint => F z * deriv θ z.2)
      (g := fun z : ParabolicPoint => G z * θ z.2) hFθ hGθ
    have e3 := integral_div (μ := volume.restrict (spaceTimeSet K (Ioo 0 T)))
      (2 : ℝ) (fun z : ParabolicPoint => S z * θ z.2)
    rw [e1, e2, e3] at h
    have hsum : 0 ≤ (∫ z in spaceTimeSet K (Ioo 0 T), F z * deriv θ z.2) +
        ∫ z in spaceTimeSet K (Ioo 0 T), G z * θ z.2 := by
      linarith only [h]
    rw [forcedTails_slab_fubini hFθ, forcedTails_slab_fubini hGθ] at hsum
    simp only [hYK] at hsum
    linarith only [hsum]
  have hHi : IntegrableOn H (Ioo 0 T) :=
    (integrable_indicator_iff measurableSet_Ioo).1 (forcedHopf_integrable_timeDensity K T G hG)
  intro t ht
  have hinc := forcedTails_increment_le_of_weak hT hY hHi hweak 0 ⟨le_rfl, hT.le⟩ t ht ht.1
  refine hinc.trans_eq ?_
  rw [forcedHopf_setIntegral_slab_eq_intervalIntegral K T G hG t ht]
  have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ T := by
    rw [ae_iff]
    simp
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hne] with τ hτT hτ
  rw [uIoc_of_le ht.1] at hτ
  rw [indicator_of_mem (show τ ∈ Ioo 0 T from ⟨hτ.1, lt_of_le_of_ne (hτ.2.trans ht.2) hτT⟩)]

end CKN.Leray

end
