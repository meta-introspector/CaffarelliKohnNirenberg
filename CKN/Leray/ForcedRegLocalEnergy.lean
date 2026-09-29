-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedRegLocalEnergySum

/-!
# The forced regularized local energy inequality

`eq:reg-local-energy-forced`: for every nonnegative smooth compactly supported
weight on positive times, the forced regularized velocity, its weak gradient
and the pressure `P[J_εu_ε ⊗ u_ε] + p_f` satisfy the local energy inequality
with the force work term `2 (f·u) ψ`. The space-time identity of the forced
regularized solution gives it with equality: both sides are integrals over a
slab containing the support of the weight, and there the right-hand side is
the time term plus the spatial flux of the local energy identity.
-/

@[expose] public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- A compactly supported weight on positive times lives in a time window
`(c, d)` with `0 < c < d < T`. -/
theorem exists_time_window {ψ : Vec3 × ℝ → ℝ} (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :
    ∃ c d T : ℝ, 0 < c ∧ c < d ∧ d < T ∧ ∀ z ∈ tsupport ψ, z.2 ∈ Ioo c d := by
  set K : Set ℝ := Prod.snd '' tsupport ψ with hKdef
  have hK : IsCompact K := hψc.image continuous_snd
  have h0 : (0 : ℝ) ∉ K := by
    rintro ⟨z, hz, hz0⟩
    have h := (hψs hz).2
    simp only [mem_Ioi] at h
    rw [hz0] at h
    exact lt_irrefl _ h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl 0 h0
  obtain ⟨b, hb⟩ := hK.bddAbove
  have hc0 : 0 < min (r / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hc1 : min (r / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hc2 : min (r / 2) (1 / 2) ≤ r / 2 := min_le_left _ _
  have hb0 : 0 ≤ max b 0 := le_max_right _ _
  refine ⟨min (r / 2) (1 / 2), max b 0 + 1, max b 0 + 2, hc0,
    by linarith only [hc1, hb0], by linarith only, fun z hz => ⟨?_, ?_⟩⟩
  · have hzK : z.2 ∈ K := ⟨z, hz, rfl⟩
    have hpos : 0 < z.2 := (hψs hz).2
    have hnot : z.2 ∉ Metric.ball (0 : ℝ) r := fun h => hball h hzK
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hpos, not_lt] at hnot
    linarith only [hnot, hc2, hr]
  · have h1 : z.2 ≤ b := hb ⟨z, hz, rfl⟩
    have h2 := le_max_left b 0
    linarith only [h1, h2]

/-- A function vanishing outside a slab has the same integral over positive
times as over the slab. -/
theorem setIntegral_Ioi_eq_prod {g : Vec3 × ℝ → ℝ} {T : ℝ}
    (hg : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo 0 T → g z = 0) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), g z =
      ∫ z, g z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
  have e1 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), g z =
      ∫ z : ParabolicPoint, g z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      hg z fun h => hz ⟨mem_univ _, h.1⟩
  have e2 : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), g z =
      ∫ z : ParabolicPoint, g z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hg z fun h => hz ⟨mem_univ _, h⟩
  rw [e1, ← e2, integral_slab_eq_prod]

/-- The local energy identity of the forced regularized solution: the equality
case of `eq:reg-local-energy-forced`, for every smooth compactly supported
weight on positive times. -/
theorem forcedRegLocalEnergy_eq (ρ : RegMollifierProfile) {a : Vec3 → Vec3} (ha : IsInJ a)
    {f : ParabolicPoint → Vec3} (hf : IsLocallySquareIntegrableForce f) {ε : ℝ} (hε : 0 < ε)
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          ((vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (forcedRegVelocity ρ a ha f hf ε) z i +
            2 * forcedRegPressure ρ a ha f hf ε z * forcedRegVelocity ρ a ha f hf ε z i) *
            spatialPartial ψ i z +
        2 * (∑ i : Fin 3, f z i * forcedRegVelocity ρ a ha f hf ε z i) * ψ z =
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (forcedRegVelocity ρ a ha f hf ε) (forcedRegGradient ρ a ha f hf ε) z *
            ψ z := by
  obtain ⟨c, d, T, hc, hcd, hdT, hsupp⟩ := exists_time_window hψc hψs
  have hT : 0 < T := by linarith only [hc, hcd, hdT]
  have hout : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo 0 T → z ∉ tsupport ψ := fun z hz h =>
    hz ⟨hc.trans (hsupp z h).1, (hsupp z h).2.trans hdT⟩
  have hvel := forcedRegVelocity_eq ρ ha hf hε
  have hL : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      spatialGradientSq (forcedRegVelocity ρ a ha f hf ε) (forcedRegGradient ρ a ha f hf ε) z *
        ψ z = ∫ z, leDiss ρ ε hε ha hf ψ z
          ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    refine (setIntegral_Ioi_eq_prod (g := fun z : Vec3 × ℝ =>
      spatialGradientSq (forcedRegVelocity ρ a ha f hf ε) (forcedRegGradient ρ a ha f hf ε) z *
        ψ z) fun z hz => ?_).trans (integral_congr_ae (Eventually.of_forall fun z => ?_))
    · show _ * ψ z = 0
      rw [(weights_eq_zero_of_notMem_tsupport hψ (hout z hz)).1, mul_zero]
    · have e2 : forcedRegGradient ρ a ha f hf ε =
          forcedMollifiedGrad (forcedRegRep ρ ε hε ha hf) := by
        unfold forcedRegGradient
        rw [hvel]
      show spatialGradientSq _ (forcedRegGradient ρ a ha f hf ε) z * ψ z = _
      rw [e2]
      rfl
  have hF0 : ∀ᵐ z ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))),
      forcedForceMod f hf z = f z :=
    restrict_spaceTimeSet_eq_prod (Ioo 0 T) ▸ forcedForceMod_ae_eq f hf hT
  have hR : ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                    (forcedRegVelocity ρ a ha f hf ε) z i +
                2 * forcedRegPressure ρ a ha f hf ε z * forcedRegVelocity ρ a ha f hf ε z i) *
                spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * forcedRegVelocity ρ a ha f hf ε z i) * ψ z =
      (∫ z, (∑ k : Fin 3, forcedRegRep ρ ε hε ha hf z k *
        (forcedRegRep ρ ε hε ha hf z k * CKN.timePartial ψ z))
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T)))) +
      ∫ z, leFlux ρ ε hε ha hf ψ z
        ∂((volume : Measure Vec3).prod ((volume : Measure ℝ).restrict (Ioo 0 T))) := by
    refine (setIntegral_Ioi_eq_prod (T := T) (g := fun z : Vec3 × ℝ =>
      (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          ((vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (forcedRegVelocity ρ a ha f hf ε) z i +
            2 * forcedRegPressure ρ a ha f hf ε z * forcedRegVelocity ρ a ha f hf ε z i) *
            spatialPartial ψ i z +
        2 * (∑ i : Fin 3, f z i * forcedRegVelocity ρ a ha f hf ε z i) * ψ z)
      fun z hz => ?_).trans ?_
    · obtain ⟨h1, h2, h3, h4⟩ := weights_eq_zero_of_notMem_tsupport hψ (hout z hz)
      simp only [h1, h2, h3, h4, mul_zero, add_zero, Finset.sum_const_zero]
    · rw [← integral_add (integrable_finsetSum Finset.univ fun k _ =>
        integrable_leTime ρ ε hε ha hf hψ hψc k) (integrable_leFlux ρ ε hε ha hf hT hψ hψc)]
      refine integral_congr_ae ?_
      filter_upwards [hF0] with z hz
      have hlap : ∑ i : Fin 3, spatialSecondPartial ψ i i z =
          CKN.spatialLaplacian (fun y => ψ (y, z.2)) z.1 := rfl
      have hpart : ∀ i : Fin 3, spatialPartial ψ i z =
          fderiv ℝ (fun y => ψ (y, z.2)) z.1 (CKN.basisVec i) := fun i => rfl
      rw [forcedRegPressure_apply ρ ha hf hε z]
      simp only [leFlux, hlap, hpart, hvel, CKN.Foundation.Heat.vec3EuclideanNorm_sq, ← hz,
        Fin.sum_univ_three]
      ring
  rw [hL, hR, leEnergy_prod_identity ρ ε hε ha hf hT hψ hψc hc hcd hdT hsupp]

/-- `eq:reg-local-energy-forced`: the local energy inequality of the forced
regularized solutions, in the form used by the limiting argument of
`thm:leray-forced`. -/
theorem forcedRegLocalEnergy (ρ : RegMollifierProfile) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε) (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (forcedRegVelocity ρ a ha f hf ε) (forcedRegGradient ρ a ha f hf ε) z *
            ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf ε z)) ^ (2 : ℕ) *
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                    (forcedRegVelocity ρ a ha f hf ε) z i +
                2 * forcedRegPressure ρ a ha f hf ε z * forcedRegVelocity ρ a ha f hf ε z i) *
                spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * forcedRegVelocity ρ a ha f hf ε z i) * ψ z := by
  intro a ha f hf ε hε ψ hψtest _
  obtain ⟨hψ, hψc, hψs⟩ := hψtest
  exact le_of_eq (forcedRegLocalEnergy_eq ρ ha hf hε hψ hψc hψs).symm

end CKN.Leray

end
