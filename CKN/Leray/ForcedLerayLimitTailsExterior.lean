-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitTailsBound
public import CKN.Leray.ForcedLerayLimitTailsCutoff
public import CKN.Leray.ForcedLerayLimitTailsContinuity

/-!
# The exterior energy estimate

`eq:forced-tails` in `lem:forced-tails`, for one velocity satisfying the
localized energy inequality `eq:reg-local-energy-forced` with continuous L²
slices: the kinetic energy outside the ball of radius 2R at time t ≤ T is
at most the initial energy outside the ball of radius R, plus C/R² times
the kinetic energy on the slab ℝ³ × (0,T), plus C/R times the transport and
quadratic-pressure flux on the slab, plus twice the product of the L² norm of
the velocity on the slab with the L² norm of the projected force f - g
outside the ball of radius R. The constant C is absolute. The proof tests
the localized energy inequality with ζ_R χ_N, bounds the localized density,
and lets N → ∞.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

private theorem forcedTailsExt_mul_le_one {x y : ℝ} (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1) :
    x * y ≤ 1 := by
  have h := mul_le_mul hx hy hy0 zero_le_one
  rwa [one_mul] at h

/-- The square-integrable Euclidean norm of a square-integrable field. -/
private theorem forcedTailsExt_norm_memLp {μ : Measure ParabolicPoint} {v : ParabolicPoint → Vec3}
    (hv : MemLp v 2 μ) : MemLp (fun z => vec3EuclideanNorm (v z)) (ENNReal.ofReal 2) μ := by
  rw [ENNReal.ofReal_ofNat]
  refine (memLp_two_iff_integrable_sq
    (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hv.aestronglyMeasurable)).2 ?_
  have h : Integrable (fun z => ∑ i : Fin 3, v z i ^ 2) μ :=
    integrable_finsetSum _ fun i _ => (hv.eval i).integrable_sq
  exact h.congr (Eventually.of_forall fun z => (forcedTails_vec3EuclideanNorm_sq (v z)).symm)

/-- `eq:forced-tails` (`lem:forced-tails`) for one velocity field. There is an
absolute constant C such that, for a velocity u with continuous L²
slices that are weakly divergence free, transport field J, weak gradient
Du, force f, pressure p, force pressure pF whose slice weak gradient is
g, satisfying the localized energy inequality `eq:reg-local-energy-forced`,
and every R > 0 and t ∈ [0,T], the energy of u(t) outside the ball of
radius 2R is bounded by the initial energy outside the ball of radius R,
C/R² times the kinetic energy on the slab, C/R times the transport and
quadratic-pressure flux on the slab, and twice the product of the slab L²
norm of u with the L² norm of f - g outside the ball of radius R. -/
theorem forcedTails_exterior_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 < T →
    ∀ (u J f g : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p pF : ParabolicPoint → ℝ)
      (hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume),
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) →
      (∀ t : ℝ, 0 ≤ t → IsWeakDivFreeL2 (fun x : Vec3 => u (x, t))) →
      MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp u 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp J 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp g 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp (fun z => p z - pF z) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      (∀ K : Set Vec3, IsCompact K →
        MemLp pF (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K (Ioo 0 T)))) →
      (∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) T)),
        MemLp (fun x : Vec3 => pF (x, τ)) 6 volume ∧
          MemLp (fun x : Vec3 => g (x, τ)) 2 volume ∧
          HasWeakGradientOn (Set.univ : Set Vec3) (fun x => pF (x, τ)) (fun x => g (x, τ))) →
      (∀ ψ : ParabolicPoint → ℝ,
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
              2 * (∑ i : Fin 3, f z i * u z i) * ψ z) →
      ∀ R : ℝ, 0 < R → ∀ t ∈ Icc 0 T,
        ∫ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
            vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) ≤
          (∫ x in {x : Vec3 | R < vec3EuclideanNorm x},
              vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ)) +
            C / R ^ 2 * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              vec3EuclideanNorm (u z) ^ (2 : ℕ)) +
            C / R * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
              (vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i| +
                2 * |p z - pF z| * ∑ i : Fin 3, |u z i|)) +
            2 * Real.sqrt (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
                vec3EuclideanNorm (u z) ^ (2 : ℕ)) *
              Real.sqrt (∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
                vec3EuclideanNorm (f z - g z) ^ (2 : ℕ)) := by
  obtain ⟨L, hL0, hcut⟩ := forcedTails_cutoff_family
  refine ⟨6 * L + 6 * L ^ 2 + 2 * L, by positivity, ?_⟩
  intro T hT u J f g Du p pF hSlice hcont hdiv hu2 hu3 hJ hDu hf hg hpp hpF hslices hLE R hR
    t ht
  obtain ⟨ζ, hζs, hζ01, hζ0, hζ1, hfam⟩ := hcut R hR
  choose χ hχs hχc hχ01 hχ1 hd1 hd2 using fun n : ℕ =>
    hfam (R + n) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith only [this])
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let E : Set ParabolicPoint := spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T)
  let U2 : ℝ := ∫ z in S, vec3EuclideanNorm (u z) ^ (2 : ℕ)
  let MΦ : ℝ := ∫ z in S, (vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i| +
    2 * |p z - pF z| * ∑ i : Fin 3, |u z i|)
  let MW : ℝ := ∫ z in E, vec3EuclideanNorm (f z - g z) * vec3EuclideanNorm (u z)
  let Bc : ℝ := 3 * ((2 * L + 2 * L ^ 2) / R ^ 2) * U2 + 2 * L / R * MΦ + 2 * MW
  let ext : Set Vec3 := {x : Vec3 | R < vec3EuclideanNorm x}
  have hextm : MeasurableSet ext :=
    measurableSet_lt measurable_const CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  have hsl : ∀ τ, 0 ≤ τ → Integrable (fun x : Vec3 => vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ)) :=
    fun τ hτ => (integrable_finsetSum _ fun i _ => ((hSlice τ hτ).eval i).integrable_sq).congr
      (Eventually.of_forall fun x => (forcedTails_vec3EuclideanNorm_sq _).symm)
  -- the estimate for each interior cutoff
  have hkey : ∀ n : ℕ, ∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * (ζ x * χ n x) ≤
      (∫ x in ext, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ)) + Bc := by
    intro n
    let q : Vec3 → ℝ := fun y => ζ y * χ n y
    have hq : ContDiff ℝ (⊤ : ℕ∞) q := hζs.mul (hχs n)
    have hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1 := fun x =>
      ⟨mul_nonneg (hζ01 x).1 (hχ01 n x).1, forcedTailsExt_mul_le_one (hζ01 x).2 (hχ01 n x).1 (hχ01 n x).2⟩
    have hqR : ∀ x, vec3EuclideanNorm x ≤ R → q x = 0 := fun x hx => by
      simp only [q, hζ0 x hx, zero_mul]
    let K : Set Vec3 := tsupport (χ n)
    have hK : IsCompact K := hχc n
    have hqK : tsupport q ⊆ K := tsupport_mul_subset_right
    have hpK := hpF K hK
    have hνKS : (volume : Measure ParabolicPoint).restrict (spaceTimeSet K (Ioo 0 T)) ≤
        volume.restrict S :=
      Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
    have hpTot : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet K (Ioo 0 T))) := by
      have h := (hpp.mono_measure hνKS).add hpK
      refine (memLp_congr_ae (Eventually.of_forall fun z => ?_)).1 h
      simp only [Pi.add_apply, sub_add_cancel]
    have hY : ContinuousOn (fun τ => ∫ x : Vec3, vec3EuclideanNorm (u (x, τ)) ^ (2 : ℕ) * q x)
        (Icc 0 T) :=
      (forcedTails_weightedEnergy_continuousOn u hSlice hcont hq.continuous.measurable
        (C := 1) fun x => by rw [abs_of_nonneg (hq01 x).1]; exact (hq01 x).2).mono
        Icc_subset_Ici_self
    have hloc := forcedTails_localized_energy_le hT hq (fun x => (hq01 x).1) hK hqK hu3 hu2 hJ
      hDu hf hpTot hY hLE t ht
    have hbound := forcedTails_density_integral_le hq hK hqK hq01 hqR (hd1 n) (hd2 n) hdiv hu2
      hu3 hJ hDu hf hg hpp hpK hslices ht
    have hinit : ∫ x : Vec3, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) * q x ≤
        ∫ x in ext, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) := by
      rw [← integral_indicator hextm]
      refine integral_mono ((hsl 0 le_rfl).mul_bdd hq.continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hq01 x).1]; exact (hq01 x).2))
        ((hsl 0 le_rfl).indicator hextm) fun x => ?_
      have h0 : 0 ≤ vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ) := by positivity
      by_cases hx : x ∈ ext
      · rw [indicator_of_mem hx]
        exact mul_le_of_le_one_right h0 (hq01 x).2
      · rw [indicator_of_notMem hx, hqR x (le_of_not_gt hx), mul_zero]
    change (∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * q x) ≤ _
    change _ ≤ _ + (3 * ((2 * L + 2 * L ^ 2) / R ^ 2) * U2 + 2 * L / R * MΦ + 2 * MW)
    linarith only [hloc, hbound, hinit]
  -- the limit N → ∞
  have hζbdd : Integrable (fun x : Vec3 => vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * ζ x) :=
    (hsl t ht.1).mul_bdd hζs.continuous.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hζ01 x).1]; exact (hζ01 x).2)
  have hlim : Tendsto (fun n : ℕ => ∫ x : Vec3,
      vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * (ζ x * χ n x)) atTop
      (𝓝 (∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * ζ x)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ))
      (fun n => ((hsl t ht.1).mul_bdd (hζs.mul (hχs n)).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hζ01 x).1 (hχ01 n x).1)]
          exact forcedTailsExt_mul_le_one (hζ01 x).2 (hχ01 n x).1 (hχ01 n x).2)).aestronglyMeasurable)
      (hsl t ht.1) (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · have h0 : 0 ≤ vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (mul_nonneg (hζ01 x).1 (hχ01 n x).1))]
      exact mul_le_of_le_one_right h0 (forcedTailsExt_mul_le_one (hζ01 x).2 (hχ01 n x).1 (hχ01 n x).2)
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨m, hm⟩ := exists_nat_ge (vec3EuclideanNorm x)
      filter_upwards [eventually_ge_atTop m] with n hn
      have hxn : vec3EuclideanNorm x ≤ R + n := by
        have : (m : ℝ) ≤ n := by exact_mod_cast hn
        linarith only [hm, this, hR]
      rw [hχ1 n x hxn, mul_one]
  have hζest : ∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * ζ x ≤
      (∫ x in ext, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ)) + Bc :=
    le_of_tendsto' hlim hkey
  have hout : ∫ x in {x : Vec3 | 2 * R < vec3EuclideanNorm x},
      vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) ≤
        ∫ x : Vec3, vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) * ζ x := by
    have hm : MeasurableSet {x : Vec3 | 2 * R < vec3EuclideanNorm x} :=
      measurableSet_lt measurable_const CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
    rw [← integral_indicator hm]
    refine integral_mono ((hsl t ht.1).indicator hm) hζbdd fun x => ?_
    have h0 : 0 ≤ vec3EuclideanNorm (u (x, t)) ^ (2 : ℕ) := by positivity
    by_cases hx : x ∈ {x : Vec3 | 2 * R < vec3EuclideanNorm x}
    · rw [indicator_of_mem hx, hζ1 x (le_of_lt hx), mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg h0 (hζ01 x).1
  -- Cauchy–Schwarz for the force term and the constants
  have hU2 : 0 ≤ U2 := setIntegral_nonneg (MeasurableSet.univ.prod measurableSet_Ioo)
    fun z _ => by positivity
  have hMΦ : 0 ≤ MΦ := setIntegral_nonneg (MeasurableSet.univ.prod measurableSet_Ioo)
    fun z _ => by positivity
  have hES : E ⊆ S := Set.prod_mono (subset_univ _) subset_rfl
  have hμES : (volume : Measure ParabolicPoint).restrict E ≤ volume.restrict S :=
    Measure.restrict_mono_set volume hES
  have hCS : MW ≤ Real.sqrt (∫ z in E, vec3EuclideanNorm (f z - g z) ^ (2 : ℕ)) *
      Real.sqrt U2 := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict E)
      Real.HolderConjugate.two_two
      (f := fun z => vec3EuclideanNorm (f z - g z)) (g := fun z => vec3EuclideanNorm (u z))
      (Eventually.of_forall fun z => Real.sqrt_nonneg _)
      (Eventually.of_forall fun z => Real.sqrt_nonneg _)
      (forcedTailsExt_norm_memLp ((hf.sub hg).mono_measure hμES))
      (forcedTailsExt_norm_memLp (hu2.mono_measure hμES))
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _))
    have hN2 : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) (volume.restrict S) :=
      (integrable_finsetSum _ fun i _ => (hu2.eval i).integrable_sq).congr
        (Eventually.of_forall fun z => (forcedTails_vec3EuclideanNorm_sq (u z)).symm)
    exact setIntegral_mono_set hN2 (Eventually.of_forall fun z => by positivity)
      hES.eventuallyLE
  have hc1 : 3 * ((2 * L + 2 * L ^ 2) / R ^ 2) ≤ (6 * L + 6 * L ^ 2 + 2 * L) / R ^ 2 := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith only [hL0]) (by positivity)
  have hc2 : 2 * L / R ≤ (6 * L + 6 * L ^ 2 + 2 * L) / R :=
    div_le_div_of_nonneg_right (by nlinarith only [hL0]) hR.le
  have h1 := mul_le_mul_of_nonneg_right hc1 hU2
  have h2 := mul_le_mul_of_nonneg_right hc2 hMΦ
  change _ ≤ (∫ x in ext, vec3EuclideanNorm (u (x, 0)) ^ (2 : ℕ)) +
    (6 * L + 6 * L ^ 2 + 2 * L) / R ^ 2 * U2 + (6 * L + 6 * L ^ 2 + 2 * L) / R * MΦ +
    2 * Real.sqrt U2 * Real.sqrt (∫ z in E, vec3EuclideanNorm (f z - g z) ^ (2 : ℕ))
  change _ ≤ _ + (3 * ((2 * L + 2 * L ^ 2) / R ^ 2) * U2 + 2 * L / R * MΦ + 2 * MW) at hζest
  linarith only [hout, hζest, h1, h2, hCS]

end CKN.Leray

end
