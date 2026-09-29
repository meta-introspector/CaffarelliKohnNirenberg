-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedRegLocalEnergyWeights
public import CKN.Leray.RegularisedTransportDivergence

/-!
# The space-time local energy identity of the forced regularized solution

On almost every time slice the sum of the limiting energy pairings of the
forced regularized solution is the weighted dissipation minus half the spatial
flux. The dissipation and flux densities are integrable on every slab, and
integrating the slice identity against the time identity of the mollified
velocity gives the space-time local energy identity
`∫∫ |u|² ∂ₜψ + ∫∫ flux = 2 ∫∫ |Du|² ψ`, which is the equality case of
`eq:reg-local-energy-forced`.
-/

@[expose] public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

section Sum

variable (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε) {a : Vec3 → Vec3} (ha : CKN.IsInJ a)
  {f : ParabolicPoint → Vec3} (hf : CKN.IsLocallySquareIntegrableForce f)

/-- The weighted dissipation density of the forced regularized solution. -/
def leDiss (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  (∑ k : Fin 3, ∑ j : Fin 3, forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z k j ^ 2) * ψ z

/-- The spatial flux density of the local energy identity of the forced
regularized solution. -/
def leFlux (ψ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) : ℝ :=
  (∑ k : Fin 3, forcedRegRep ρ ε hε ha hf z k ^ 2) *
      CKN.spatialLaplacian (fun y => ψ (y, z.2)) z.1 +
    ∑ i : Fin 3, ((∑ k : Fin 3, forcedRegRep ρ ε hε ha hf z k ^ 2) *
        regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i +
      2 * (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z + forcePressure f hf z) *
        forcedRegRep ρ ε hε ha hf z i) * fderiv ℝ (fun y => ψ (y, z.2)) z.1 (CKN.basisVec i) +
    2 * (∑ i : Fin 3, forcedForceMod f hf z i * forcedRegRep ρ ε hε ha hf z i) * ψ z

/-- On almost every time slice the sum of the limiting energy pairings is the
weighted dissipation minus half the spatial flux. -/
theorem ae_sum_leLimitT_eq {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 T)),
      ∑ k : Fin 3, leLimitT ρ ε hε ha hf ψ k t =
        (∫ x, leDiss ρ ε hε ha hf ψ (x, t)) - (1 / 2) * ∫ x, leFlux ρ ε hε ha hf ψ (x, t) := by
  obtain ⟨M, -, hMψ, hMd⟩ := exists_weight_bound hψ hψc
  filter_upwards [ae_leDelta ρ ε hε ha hf hT hψ hψc hMψ hMd 0,
    ae_leDelta ρ ε hε ha hf hT hψ hψc hMψ hMd 1, ae_leDelta ρ ε hε ha hf hT hψ hψc hMψ hMd 2,
    ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (forcedRegRep_weakGradient ρ ε hε ha hf),
    ae_forcedRegGrad_slice ρ ε hε ha hf hT.le, ae_forcedForceMod_slice hf hT,
    ae_forcePressure_slice hf hT, ae_memLp_forcePressure_six hf hT]
    with t h0 h1 h2 ht hw hDu hFF hPF hp6
  obtain ⟨hF2, -⟩ := hFF
  obtain ⟨hpfl, hft, hpf⟩ := hPF
  have hdf := forcedRegRep_weakDivFree ρ ε hε ha hf ht.1.le
  have hJ : CKN.IsInJ fun x => forcedRegRep ρ ε hε ha hf (x, t) := CKN.isInJ_iff_weakDivFree.2 hdf
  have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε hJ
  have hV : ∀ j, ContDiff ℝ 1 fun x =>
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) (x, t) j := fun j =>
    (hsmooth.continuousLinearMap_comp (ContinuousLinearMap.proj (R := ℝ) j)).of_le
      (show (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hdiv := regUniformMollifiedVelocity_divergence_eq_zero ρ ε hε
    (forcedRegRep ρ ε hε ha hf) t hJ
  have hq2 : MemLp (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t)) 2
      volume :=
    (memLp_rieszPressureSliceRepresentative_two _).ae_eq
      (forcedQuadPressure_slice ρ ε hε (forcedRegCurve ρ ε hε ha hf) t).symm
  have hψt : ContDiff ℝ (⊤ : ℕ∞) fun y => ψ (y, t) := hψ.comp (contDiff_id.prodMk contDiff_const)
  have hψtc := hasCompactSupport_scalar_slice hψc t
  have hG : ∀ k, MemLp (fun x => forcePressureGradientFunction (fun x => f (x, t)) hft x k) 2
      volume := fun k => (forcePressureGradientFunction_memLp _ hft).eval k
  have hpψ : ∀ k, MemLp (fun x => forcePressure f hf (x, t) *
      fderiv ℝ (fun y => ψ (y, t)) x (CKN.basisVec k)) 2 volume := fun k =>
    memLp_mul_of_memLp_six hp6 ((hψt.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hψtc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k))
  have hslice := sum_leLimit_slice_eq hdf (fun k j => hDu k j) (fun k => hw k) hV hdiv hq2 hpfl
    hG hpf (fun k => hF2.eval k) hψt hψtc hpψ
  have hk : ∀ k : Fin 3, leLimitT ρ ε hε ha hf ψ k t =
      leLimit (fun y => forcedRegRep ρ ε hε ha hf (y, t) k)
        (fun j y => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) (y, t) k j)
        (fun j y => leTensor ρ ε hε ha hf j k (y, t))
        (fun y => forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) (y, t))
        (fun y => forcePressureGradientFunction (fun x => f (x, t)) hft y k)
        (fun y => forcedForceMod f hf (y, t) k) (fun y => ψ (y, t)) k := by
    intro k
    fin_cases k
    exacts [h0.2.2 hft, h1.2.2 hft, h2.2.2 hft]
  rw [Finset.sum_congr rfl fun k _ => hk k]
  exact hslice

/-- The weighted dissipation density is integrable on every slab. -/
theorem integrable_leDiss {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (leDiss ρ ε hε ha hf ψ)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  obtain ⟨M, hM⟩ := exists_abs_le_of_compact hψ.continuous hψc
  have hD := memLp_forcedRegGrad_prod ρ ε hε ha hf T hT.le
  have hi : ∀ k j, Integrable (fun z => forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z k j *
      (forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) z k j * ψ z))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := fun k j =>
    integrable_mul_mul_of_bound ((hD.eval k).eval j) ((hD.eval k).eval j)
      hψ.continuous.aestronglyMeasurable (Eventually.of_forall hM)
  refine (integrable_finsetSum Finset.univ fun k _ =>
    integrable_finsetSum Finset.univ fun j _ => hi k j).congr
    (Eventually.of_forall fun z => ?_)
  simp only [leDiss, Fin.sum_univ_three]
  ring

/-- The spatial flux density is integrable on every slab. -/
theorem integrable_leFlux {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (leFlux ρ ε hε ha hf ψ)
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have hU := memLp_forcedRegRep_prod ρ ε hε ha hf T
  have hq := memLp_forcedQuadPressure_slab ρ ε hε (continuous_forcedRegCurve ρ ε hε ha hf) T
  have hF := memLp_forcedForceMod_prod f hf hT
  obtain ⟨MV, hMV0, hMV⟩ := forcedRegTransport_bound ρ ε hε ha hf T
  have hLc := continuous_laplacian_prod hψ
  obtain ⟨ML, hML⟩ := exists_abs_le_of_compact hLc (hasCompactSupport_laplacian_prod hψc)
  have hdc : ∀ i : Fin 3, Continuous fun z => fderiv ℝ ψ z (CKN.basisVec i, 0) := fun i =>
    continuous_fderiv_apply_prod hψ _
  have hdcc : ∀ i : Fin 3, HasCompactSupport fun z => fderiv ℝ ψ z (CKN.basisVec i, 0) :=
    fun i => hψc.fderiv_apply (𝕜 := ℝ) _
  choose Md hMd using fun i => exists_abs_le_of_compact (hdc i) (hdcc i)
  obtain ⟨Mψ, hMψ⟩ := exists_abs_le_of_compact hψ.continuous hψc
  have hWm : AEStronglyMeasurable (fun z => ∑ i : Fin 3,
      regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i *
        fderiv ℝ ψ z (CKN.basisVec i, 0))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) :=
    (Finset.measurable_sum _ fun i _ =>
      (measurable_forcedRegTransport ρ ε hε ha hf i).mul (hdc i).measurable).aestronglyMeasurable
  have hWb : ∀ᵐ z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))),
      |∑ i : Fin 3, regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i *
        fderiv ℝ ψ z (CKN.basisVec i, 0)| ≤ ∑ i : Fin 3, MV * Md i := by
    filter_upwards [ae_mem_Ioo_prod T] with z hz
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hMV z ⟨hz.1.le, hz.2.le⟩ i) (hMd i z) (abs_nonneg _) hMV0
  have hall : Integrable (fun z => ∑ k : Fin 3,
      (forcedRegRep ρ ε hε ha hf z k * (forcedRegRep ρ ε hε ha hf z k *
          ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ ψ w (CKN.basisVec i, 0)) z
            (CKN.basisVec i, 0)) +
        forcedRegRep ρ ε hε ha hf z k * (forcedRegRep ρ ε hε ha hf z k *
          ∑ i : Fin 3, regUniformMollifiedVelocity ρ ε hε (forcedRegRep ρ ε hε ha hf) z i *
            fderiv ℝ ψ z (CKN.basisVec i, 0)) +
        2 * (forcedQuadPressure ρ ε hε (forcedRegCurve ρ ε hε ha hf) z *
          (forcedRegRep ρ ε hε ha hf z k * fderiv ℝ ψ z (CKN.basisVec k, 0))) +
        2 * (forcedRegRep ρ ε hε ha hf z k *
          (forcePressure f hf z * fderiv ℝ ψ z (CKN.basisVec k, 0))) +
        2 * (forcedForceMod f hf z k * (forcedRegRep ρ ε hε ha hf z k * ψ z))))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    refine integrable_finsetSum Finset.univ fun k _ => ?_
    have t1 := integrable_mul_mul_of_bound (hU.eval k) (hU.eval k) hLc.aestronglyMeasurable
      (Eventually.of_forall hML)
    have t2 := integrable_mul_mul_of_bound (hU.eval k) (hU.eval k) hWm hWb
    have t3 := (integrable_mul_mul_of_bound hq (hU.eval k) (hdc k).aestronglyMeasurable
      (Eventually.of_forall (hMd k))).const_mul 2
    have t4 := ((hU.eval k).integrable_mul
      (memLp_forcePressure_mul_prod hf hT (hdc k) (hdcc k))).const_mul 2
    have t5 := (integrable_mul_mul_of_bound (hF.eval k) (hU.eval k)
      hψ.continuous.aestronglyMeasurable (Eventually.of_forall hMψ)).const_mul 2
    exact (((t1.add t2).add t3).add t4).add t5
  refine hall.congr (Eventually.of_forall fun z => ?_)
  simp only [leFlux]
  rw [spatialLaplacian_slice_eq hψ z]
  simp only [fderiv_scalar_slice hψ z.1 z.2, Prod.mk.eta, Fin.sum_univ_three]
  ring

/-- The time term of the local energy identity is integrable on every slab. -/
theorem integrable_leTime {T : ℝ} {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (k : Fin 3) :
    Integrable (fun z => forcedRegRep ρ ε hε ha hf z k *
        (forcedRegRep ρ ε hε ha hf z k * CKN.timePartial ψ z))
      ((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have hc : Continuous fun z => fderiv ℝ ψ z (0, 1) := continuous_fderiv_apply_prod hψ _
  obtain ⟨M, hM⟩ := exists_abs_le_of_compact hc (hψc.fderiv_apply (𝕜 := ℝ) _)
  have hU := memLp_forcedRegRep_prod ρ ε hε ha hf T
  refine (integrable_mul_mul_of_bound (hU.eval k) (hU.eval k) hc.aestronglyMeasurable
    (Eventually.of_forall hM)).congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [timePartial_eq_fderiv hψ z]

/-- The space-time local energy identity of the forced regularized solution
on a slab containing the support of the weight. -/
theorem leEnergy_prod_identity {T : ℝ} (hT : 0 < T) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) {c d : ℝ} (hc : 0 < c)
    (hcd : c < d) (hdT : d < T) (hψs : ∀ z ∈ tsupport ψ, z.2 ∈ Ioo c d) :
    (∫ z, (∑ k : Fin 3, forcedRegRep ρ ε hε ha hf z k *
        (forcedRegRep ρ ε hε ha hf z k * CKN.timePartial ψ z))
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) +
      ∫ z, leFlux ρ ε hε ha hf ψ z
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) =
      2 * ∫ z, leDiss ρ ε hε ha hf ψ z
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have iB := integrable_leTime ρ ε hε ha hf (T := T) hψ hψc
  have iD := integrable_leDiss ρ ε hε ha hf hT hψ hψc
  have iF := integrable_leFlux ρ ε hε ha hf hT hψ hψc
  have e0 : ∫ z, (∑ k : Fin 3, forcedRegRep ρ ε hε ha hf z k *
      (forcedRegRep ρ ε hε ha hf z k * CKN.timePartial ψ z))
      ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) =
      ∑ k : Fin 3, 2 * ∫ t in Ioo 0 T, leLimitT ρ ε hε ha hf ψ k t := by
    rw [integral_finsetSum _ fun k _ => iB k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_prod_symm _ (iB k)]
    exact integral_sq_timePartial_eq ρ ε hε ha hf k hT hψ hψc hc hcd hdT hψs
  have hsum : ∑ k : Fin 3, ∫ t in Ioo 0 T, leLimitT ρ ε hε ha hf ψ k t =
      ∫ t in Ioo 0 T, ∑ k : Fin 3, leLimitT ρ ε hε ha hf ψ k t :=
    (integral_finsetSum _ fun k _ => integrableOn_leLimitT ρ ε hε ha hf hT hψ hψc k).symm
  have hslice : ∫ t in Ioo 0 T, ∑ k : Fin 3, leLimitT ρ ε hε ha hf ψ k t =
      (∫ t in Ioo 0 T, ∫ x, leDiss ρ ε hε ha hf ψ (x, t)) -
        (1 / 2) * ∫ t in Ioo 0 T, ∫ x, leFlux ρ ε hε ha hf ψ (x, t) := by
    rw [integral_congr_ae (ae_sum_leLimitT_eq ρ ε hε ha hf hT hψ hψc),
      integral_sub iD.integral_prod_right (iF.integral_prod_right.const_mul _),
      integral_const_mul]
  rw [e0, ← Finset.mul_sum, hsum, hslice, integral_prod_symm _ iD, integral_prod_symm _ iF]
  ring

end Sum

end CKN.Leray

end
