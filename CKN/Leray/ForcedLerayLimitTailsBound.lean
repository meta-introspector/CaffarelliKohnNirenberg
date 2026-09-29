-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedLerayLimitTailsLocal
public import CKN.Leray.ForcedLerayLimitTailsProjection
public import CKN.Foundation.Parabolic.Vec3Norm

/-!
# Bounding the localized energy density

In the proof of `lem:forced-tails` the localized energy density of
`forcedTailsLocalDensity`, integrated over K × (0,t), is bounded for a
weight q with values in [0,1] that vanishes on the ball of radius R. The
force-pressure flux cancels against the gradient part of the force
(`eq:forced-projection-cancellation`, applied on almost every time slice), the
dissipation has a sign, and the remaining terms are bounded by the bounds on
the derivatives of q times space-time integrals over the slab ℝ³ × (0,T):
the kinetic energy, the transport and quadratic-pressure fluxes, and the work
of the projected force outside the ball of radius R.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

local instance forcedTailsBoundHolderThree :
    ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (ENNReal.ofReal (3 / 2 : ℝ)) := by
  have hreal : Real.HolderTriple 3 3 (3 / 2) := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using hreal.ennrealOfReal

local instance forcedTailsBoundHolderOne :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using
    hreal.ennrealOfReal

/-- The Cauchy–Schwarz inequality for the Euclidean norm on Vec3. -/
private theorem forcedTailsBound_dot_le (v w : Vec3) :
    ∑ i : Fin 3, v i * w i ≤ vec3EuclideanNorm v * vec3EuclideanNorm w := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w
  have h : |∑ i : Fin 3, v i * w i| ≤
      Real.sqrt ((∑ i : Fin 3, v i ^ 2) * ∑ i : Fin 3, w i ^ 2) := Real.abs_le_sqrt hcs
  rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (v i))] at h
  exact (le_abs_self _).trans h

/-- `lem:forced-tails`: the localized energy density integrated over K × (0,t)
is bounded by 3b times the kinetic energy on the slab, a times the transport
and quadratic-pressure flux on the slab, and twice the work of the projected
force f - g outside the ball of radius R, when the weight q has values in
[0,1], vanishes on the ball of radius R, and has first and pure second
derivatives bounded by a and b; here g is the slice weak gradient of the
force pressure pF. -/
theorem forcedTails_density_integral_le {T : ℝ}
    {u J f g : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p pF : ParabolicPoint → ℝ} {q : Vec3 → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    {K : Set Vec3} (hK : IsCompact K) (hqK : tsupport q ⊆ K)
    (hq01 : ∀ x, 0 ≤ q x ∧ q x ≤ 1) {R a b : ℝ}
    (hqR : ∀ x, vec3EuclideanNorm x ≤ R → q x = 0)
    (hqa : ∀ x i, |spatialDeriv q i x| ≤ a) (hqb : ∀ x i, |mixedSecond q i i x| ≤ b)
    (hdiv : ∀ t : ℝ, 0 ≤ t → IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hu2 : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hu3 : MemLp u 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ : MemLp J 3 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hf : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : MemLp g 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpp : MemLp (fun z => p z - pF z) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hpF : MemLp pF (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet K (Ioo 0 T))))
    (hslices : ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) T)),
      MemLp (fun x : Vec3 => pF (x, τ)) 6 volume ∧
        MemLp (fun x : Vec3 => g (x, τ)) 2 volume ∧
        HasWeakGradientOn (Set.univ : Set Vec3) (fun x => pF (x, τ)) (fun x => g (x, τ)))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ z in spaceTimeSet K (Ioo 0 t), forcedTailsLocalDensity u J f Du p q z ≤
      3 * b * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          vec3EuclideanNorm (u z) ^ (2 : ℕ)) +
        a * (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          (vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i| +
            2 * |p z - pF z| * ∑ i : Fin 3, |u z i|)) +
        2 * ∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T),
          vec3EuclideanNorm (f z - g z) * vec3EuclideanNorm (u z) := by
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μS : Measure ParabolicPoint := volume.restrict S
  let νT : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 T))
  let νt : Measure ParabolicPoint := volume.restrict (spaceTimeSet K (Ioo 0 t))
  have : IsFiniteMeasure νT := forcedHopf_slab_isFiniteMeasure hK T
  have : IsFiniteMeasure νt := forcedHopf_slab_isFiniteMeasure hK t
  have hsubt : spaceTimeSet K (Ioo 0 t) ⊆ spaceTimeSet K (Ioo 0 T) :=
    Set.prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2)
  have hνtT : νt ≤ νT := Measure.restrict_mono_set volume hsubt
  have hνTS : νT ≤ μS := Measure.restrict_mono_set volume (Set.prod_mono (subset_univ K) subset_rfl)
  have hνtS : νt ≤ μS := hνtT.trans hνTS
  have hqc : HasCompactSupport q := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hqK
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (hqa 0 0)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hqb 0 0)
  have hq0K : ∀ x, x ∉ K → q x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hqK h))
  have hdq0 : ∀ i x, x ∉ K → spatialDeriv q i x = 0 := by
    intro i x hx
    have h : fderiv ℝ q x = 0 := by
      by_contra hne
      exact hx (hqK (support_fderiv_subset ℝ (Function.mem_support.mpr hne)))
    simp only [spatialDeriv, h, zero_apply]
  have hbq : MemLp (fun z : ParabolicPoint => q z.1) ∞ νT :=
    forcedHopf_memLp_top_spatial hq.continuous hqc
  have hbd : ∀ i, MemLp (fun z : ParabolicPoint => spatialDeriv q i z.1) ∞ νT := fun i =>
    forcedHopf_spatialDeriv_memLp_top hq hqc i
  -- the full pressure is in L^{3/2} on K × (0,T)
  have hpK : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) νT := by
    have h := (hpp.mono_measure hνTS).add hpF
    refine (memLp_congr_ae (Eventually.of_forall fun z => ?_)).1 h
    simp only [Pi.add_apply, sub_add_cancel]
  have hD : Integrable (forcedTailsLocalDensity u J f Du p q) νt :=
    (forcedTails_localDensity_integrable hq hK hqK hu3 hu2 hJ hDu hf hpK).mono_measure hνtT
  -- the force-pressure flux and the gradient work
  let E : ParabolicPoint → ℝ := fun z =>
    2 * (pF z * ∑ i : Fin 3, u z i * spatialDeriv q i z.1) +
      2 * ∑ i : Fin 3, g z i * u z i * q z.1
  have hEint : Integrable E νT := by
    have h1 : Integrable (fun z => pF z * ∑ i : Fin 3, u z i * spatialDeriv q i z.1) νT := by
      have h : Integrable (fun z => ∑ i : Fin 3, pF z * u z i * spatialDeriv q i z.1) νT := by
        refine integrable_finsetSum _ fun i _ => ?_
        have hpu : MemLp (pF * fun z => u z i) 1 νT := hpF.mul ((hu3.mono_measure hνTS).eval i)
        exact stability_integrable_mul_bounded_test νT le_rfl hpu (hbd i)
      refine h.congr (Eventually.of_forall fun z => ?_)
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : Integrable (fun z => ∑ i : Fin 3, g z i * u z i * q z.1) νT :=
      integrable_finsetSum _ fun i _ => stability_integrable_mul_bounded_test νT le_rfl
        (memLp_one_iff_integrable.2 (((hg.mono_measure hνTS).eval i).integrable_mul
          ((hu2.mono_measure hνTS).eval i))) hbq
    exact (h1.const_mul 2).add (h2.const_mul 2)
  have hE0 : ∫ z in spaceTimeSet K (Ioo 0 t), E z = 0 := by
    have hEt : Integrable (fun q : Vec3 × ℝ => E q)
        ((volume.restrict K).prod (volume.restrict (Ioo 0 t))) := by
      rw [← forcedHopf_slab_measure_eq_prod]
      exact hEint.mono_measure hνtT
    change ∫ z : Vec3 × ℝ, E z ∂((volume : Measure ParabolicPoint).restrict
      (spaceTimeSet K (Ioo 0 t)) : Measure (Vec3 × ℝ)) = 0
    rw [forcedHopf_slab_measure_eq_prod]
    refine (integral_prod_symm (fun z : Vec3 × ℝ => E z) hEt).trans ?_
    refine integral_eq_zero_of_ae ?_
    have hsl := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht.2) hslices
    filter_upwards [hsl, ae_restrict_mem measurableSet_Ioo] with τ hτ hτmem
    obtain ⟨hP6, hG2, hPG⟩ := hτ
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have hP2K : MemLp (fun x : Vec3 => pF (x, τ)) 2 (volume.restrict K) :=
      (hP6.mono_measure Measure.restrict_le_self).mono_exponent (by norm_num)
    have huτ := hdiv τ hτmem.1.le
    have hcancel := forcedTails_projection_cancellation hq hK hqK hP2K hG2 hPG huτ
    -- integrability of the two slice terms
    have hA : Integrable (fun x : Vec3 =>
        pF (x, τ) * ∑ i : Fin 3, u (x, τ) i * spatialDeriv q i x) := by
      have hon : IntegrableOn (fun x : Vec3 =>
          pF (x, τ) * ∑ i : Fin 3, u (x, τ) i * spatialDeriv q i x) K := by
        have h : Integrable (fun x : Vec3 =>
            ∑ i : Fin 3, pF (x, τ) * u (x, τ) i * spatialDeriv q i x) (volume.restrict K) :=
          integrable_finsetSum _ fun i _ => stability_integrable_mul_bounded_test _ le_rfl
            (memLp_one_iff_integrable.2 (hP2K.integrable_mul
              ((huτ.1.eval i).mono_measure Measure.restrict_le_self)))
            (memLp_top_of_bound (contDiff_spatialDeriv_smooth hq i).continuous.aestronglyMeasurable
              a (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hqa x i))
        refine h.congr (Eventually.of_forall fun x => ?_)
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
      intro x hx
      by_contra hxK
      exact hx (by simp [hdq0 _ x hxK])
    have hB : Integrable (fun x : Vec3 => ∑ i : Fin 3, g (x, τ) i * u (x, τ) i * q x) :=
      integrable_finsetSum _ fun i _ =>
        ((hG2.eval i).integrable_mul (huτ.1.eval i)).mul_bdd hq.continuous.aestronglyMeasurable
          (Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hq01 x).1]
            exact (hq01 x).2)
    have hK0 : ∫ x in K, E (x, τ) = ∫ x : Vec3, E (x, τ) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [E, hq0K x hx, hdq0 _ x hx]
    rw [hK0]
    change ∫ x : Vec3, (2 * (pF (x, τ) * ∑ i : Fin 3, u (x, τ) i * spatialDeriv q i x) +
      2 * ∑ i : Fin 3, g (x, τ) i * u (x, τ) i * q x) = 0
    rw [integral_add (hA.const_mul 2) (hB.const_mul 2), integral_const_mul,
      integral_const_mul, hcancel]
    ring
  -- the bounding density
  let X : Set ParabolicPoint := {z | R < vec3EuclideanNorm z.1}
  have hXm : MeasurableSet X :=
    measurableSet_lt measurable_const (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable.comp
      measurable_fst)
  let Φ : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i| +
      2 * |p z - pF z| * ∑ i : Fin 3, |u z i|
  let W : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (f z - g z) * vec3EuclideanNorm (u z)
  let B : ParabolicPoint → ℝ := fun z =>
    3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) + a * Φ z + 2 * X.indicator W z
  have hN2 : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) μS := by
    have h : Integrable (fun z => ∑ i : Fin 3, u z i ^ 2) μS :=
      integrable_finsetSum _ fun i _ => (hu2.eval i).integrable_sq
    exact h.congr (Eventually.of_forall fun z => (forcedTails_vec3EuclideanNorm_sq (u z)).symm)
  have hΦ : Integrable Φ μS := by
    have h1 : Integrable (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i|) μS := by
      have h : Integrable (fun z => ∑ i : Fin 3, ∑ k : Fin 3, u z k * u z k * |J z i|) μS :=
        integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => by
          have h1 : MemLp ((fun z => u z k) * fun z => u z k) (ENNReal.ofReal (3 / 2 : ℝ)) μS :=
            (hu3.eval k).mul (hu3.eval k)
          have h2 : MemLp (((fun z => u z k) * fun z => u z k) * fun z => |J z i|) 1 μS :=
            h1.mul (hJ.eval i).abs
          exact memLp_one_iff_integrable.1 h2
      refine h.congr (Eventually.of_forall fun z => ?_)
      show ∑ i : Fin 3, ∑ k : Fin 3, u z k * u z k * |J z i| =
        vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i|
      rw [forcedTails_vec3EuclideanNorm_sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    have h2 : Integrable (fun z => 2 * |p z - pF z| * ∑ i : Fin 3, |u z i|) μS := by
      have h : Integrable (fun z => ∑ i : Fin 3, |p z - pF z| * |u z i|) μS :=
        integrable_finsetSum _ fun i _ => memLp_one_iff_integrable.1
          (hpp.abs.mul (hu3.eval i).abs :
            MemLp ((fun z => |p z - pF z|) * fun z => |u z i|) 1 μS)
      refine (h.const_mul 2).congr (Eventually.of_forall fun z => ?_)
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact h1.add h2
  have hW : Integrable W μS := by
    have hmeas : AEStronglyMeasurable W μS :=
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        (hf.sub hg).aestronglyMeasurable).mul
      (CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hu2.aestronglyMeasurable)
    have hdom : Integrable (fun z => (∑ i : Fin 3, (f z - g z) i ^ 2 +
        ∑ i : Fin 3, u z i ^ 2) / 2) μS :=
      ((integrable_finsetSum _ fun i _ => ((hf.sub hg).eval i).integrable_sq).add
        (integrable_finsetSum _ fun i _ => (hu2.eval i).integrable_sq)).div_const 2
    refine hdom.mono' hmeas (Eventually.of_forall fun z => ?_)
    have hW0 : 0 ≤ W z := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hW0, ← forcedTails_vec3EuclideanNorm_sq,
      ← forcedTails_vec3EuclideanNorm_sq]
    change vec3EuclideanNorm (f z - g z) * vec3EuclideanNorm (u z) ≤ _
    nlinarith only [sq_nonneg (vec3EuclideanNorm (f z - g z) - vec3EuclideanNorm (u z))]
  have hBint : Integrable B μS :=
    ((hN2.const_mul _).add (hΦ.const_mul a)).add ((hW.indicator hXm).const_mul 2)
  have hB0 : ∀ z, 0 ≤ B z := by
    intro z
    have h1 : 0 ≤ Φ z := add_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => abs_nonneg _))
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _))
    have h2 : 0 ≤ X.indicator W z := Set.indicator_nonneg (fun z _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) z
    have h3 : 0 ≤ vec3EuclideanNorm (u z) ^ (2 : ℕ) := by positivity
    change 0 ≤ 3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) + a * Φ z + 2 * X.indicator W z
    positivity
  -- the pointwise bound
  have hpt : ∀ z, forcedTailsLocalDensity u J f Du p q z - E z ≤ B z := by
    intro z
    have hsplit : forcedTailsLocalDensity u J f Du p q z - E z =
        vec3EuclideanNorm (u z) ^ (2 : ℕ) * (∑ i : Fin 3, mixedSecond q i i z.1) +
        ∑ i : Fin 3, (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i +
          2 * (p z - pF z) * u z i) * spatialDeriv q i z.1 +
        2 * (∑ i : Fin 3, (f z - g z) i * u z i) * q z.1 -
        2 * spatialGradientSq u Du z * q z.1 := by
      simp only [forcedTailsLocalDensity, E, Fin.sum_univ_three, Pi.sub_apply]
      ring
    have hU0 : 0 ≤ vec3EuclideanNorm (u z) ^ (2 : ℕ) := by positivity
    have hT1 : vec3EuclideanNorm (u z) ^ (2 : ℕ) * (∑ i : Fin 3, mixedSecond q i i z.1) ≤
        3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) := by
      have hs : ∑ i : Fin 3, mixedSecond q i i z.1 ≤ 3 * b := by
        have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
          fun i _ => (le_abs_self (mixedSecond q i i z.1)).trans (hqb z.1 i)
        simpa using h
      have := mul_le_mul_of_nonneg_left hs hU0
      linarith only [this]
    have hT2 : ∑ i : Fin 3, (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i +
        2 * (p z - pF z) * u z i) * spatialDeriv q i z.1 ≤ a * Φ z := by
      change _ ≤ a * (vec3EuclideanNorm (u z) ^ (2 : ℕ) * ∑ i : Fin 3, |J z i| +
        2 * |p z - pF z| * ∑ i : Fin 3, |u z i|)
      rw [Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hc : |vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * (p z - pF z) * u z i| ≤
          vec3EuclideanNorm (u z) ^ (2 : ℕ) * |J z i| + 2 * |p z - pF z| * |u z i| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hU0, abs_two]
      have hbnd : 0 ≤ vec3EuclideanNorm (u z) ^ (2 : ℕ) * |J z i| +
          2 * |p z - pF z| * |u z i| := by positivity
      calc (vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * (p z - pF z) * u z i) *
            spatialDeriv q i z.1
          ≤ |(vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * (p z - pF z) * u z i) *
            spatialDeriv q i z.1| := le_abs_self _
        _ = |vec3EuclideanNorm (u z) ^ (2 : ℕ) * J z i + 2 * (p z - pF z) * u z i| *
            |spatialDeriv q i z.1| := abs_mul _ _
        _ ≤ (vec3EuclideanNorm (u z) ^ (2 : ℕ) * |J z i| + 2 * |p z - pF z| * |u z i|) * a :=
            mul_le_mul hc (hqa z.1 i) (abs_nonneg _) hbnd
        _ = a * (vec3EuclideanNorm (u z) ^ (2 : ℕ) * |J z i|) +
            a * (2 * |p z - pF z| * |u z i|) := by ring
    have hT3 : 2 * (∑ i : Fin 3, (f z - g z) i * u z i) * q z.1 ≤ 2 * X.indicator W z := by
      by_cases hz : z ∈ X
      · rw [indicator_of_mem hz]
        have hdot := forcedTailsBound_dot_le (f z - g z) (u z)
        have hW0 : 0 ≤ W z := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have hq0 := (hq01 z.1).1
        have hq1 := (hq01 z.1).2
        have hmul : (∑ i : Fin 3, (f z - g z) i * u z i) * q z.1 ≤ W z := by
          rcases le_total 0 (∑ i : Fin 3, (f z - g z) i * u z i) with h0 | h0
          · exact (mul_le_of_le_one_right h0 hq1).trans hdot
          · exact (mul_nonpos_of_nonpos_of_nonneg h0 hq0).trans hW0
        linarith only [hmul]
      · have hzR : vec3EuclideanNorm z.1 ≤ R := le_of_not_gt hz
        rw [indicator_of_notMem hz, hqR z.1 hzR]
        simp
    have hT4 : 0 ≤ 2 * spatialGradientSq u Du z * q z.1 := by
      have : 0 ≤ spatialGradientSq u Du z := by
        unfold spatialGradientSq
        positivity
      have := (hq01 z.1).1
      positivity
    rw [hsplit]
    change _ ≤ 3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) + a * Φ z + 2 * X.indicator W z
    linarith only [hT1, hT2, hT3, hT4]
  -- integrate
  have hEt : Integrable E νt := hEint.mono_measure hνtT
  have hstep1 : ∫ z in spaceTimeSet K (Ioo 0 t), forcedTailsLocalDensity u J f Du p q z =
      ∫ z in spaceTimeSet K (Ioo 0 t), (forcedTailsLocalDensity u J f Du p q z - E z) := by
    rw [integral_sub hD hEt, hE0, sub_zero]
  have hstep2 : ∫ z in spaceTimeSet K (Ioo 0 t), (forcedTailsLocalDensity u J f Du p q z - E z) ≤
      ∫ z in spaceTimeSet K (Ioo 0 t), B z :=
    integral_mono (hD.sub hEt) (hBint.mono_measure hνtS) hpt
  have hstep3 : ∫ z in spaceTimeSet K (Ioo 0 t), B z ≤ ∫ z in S, B z :=
    setIntegral_mono_set hBint (Eventually.of_forall hB0)
      (Set.prod_mono (subset_univ K) (Ioo_subset_Ioo_right ht.2)).eventuallyLE
  have hXS : X ∩ S = spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T) := by
    ext z
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩
  have hstep4 : ∫ z in S, B z = 3 * b * (∫ z in S, vec3EuclideanNorm (u z) ^ (2 : ℕ)) +
      a * (∫ z in S, Φ z) +
      2 * ∫ z in spaceTimeSet {x : Vec3 | R < vec3EuclideanNorm x} (Ioo 0 T), W z := by
    change ∫ z, (3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) + a * Φ z + 2 * X.indicator W z) ∂μS =
      _
    have e1 := integral_add (μ := μS)
      (f := fun z => 3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ) + a * Φ z)
      (g := fun z => 2 * X.indicator W z) ((hN2.const_mul _).add (hΦ.const_mul a))
      ((hW.indicator hXm).const_mul 2)
    have e2 := integral_add (μ := μS)
      (f := fun z => 3 * b * vec3EuclideanNorm (u z) ^ (2 : ℕ))
      (g := fun z => a * Φ z) (hN2.const_mul _) (hΦ.const_mul a)
    rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_indicator hXm, Measure.restrict_restrict hXm, hXS]
  rw [hstep1]
  exact hstep2.trans (hstep3.trans (le_of_eq hstep4))

end CKN.Leray

end
