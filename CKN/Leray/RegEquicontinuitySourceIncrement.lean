-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegEquicontinuitySourceData
public import CKN.Leray.ForcedLerayLimitPairing
public import CKN.Leray.StabilityBoundedPairing

/-!
# The pairing increment of a regularized solution

For a smooth compactly supported test field `w` and `0 ≤ s < t`, the increment
`∫ (u_ε(t) - u_ε(s))·w` is the time integral over `(s, t)` of the transport
and viscous flux of `w` plus the pressure pairing with `div w`
(`lem:reg-equicontinuity`). It follows from the weak momentum identity
(`lem:reg-momentum`) and the `L²` continuity of the time slices (R1). The case
`s = 0` needs no separate limit.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- A test field and its derivatives vanish off its closed support. -/
theorem regEquiSrc_test_zero {w : Vec3 → Vec3} {x : Vec3} (hx : x ∉ tsupport w) (i j : Fin 3) :
    w x i = 0 ∧ spatialDeriv (fun y => w y i) j x = 0 := by
  have hwi : x ∉ tsupport (fun y => w y i) := fun h =>
    hx ((tsupport_comp_subset (g := fun v : Vec3 => v i) rfl w) h)
  refine ⟨image_eq_zero_of_notMem_tsupport (f := fun y => w y i) hwi, ?_⟩
  have hd : x ∉ tsupport (fun y => fderiv ℝ (fun y => w y i) y (CKN.basisVec j)) := fun h =>
    hwi (tsupport_fderiv_apply_subset ℝ (CKN.basisVec j) h)
  exact image_eq_zero_of_notMem_tsupport
    (f := fun y => fderiv ℝ (fun y => w y i) y (CKN.basisVec j)) hd

/-- Slab integrals over a compact spatial set, time outside. -/
theorem regEquiSrc_slab_integral {K : Set Vec3} {τ : ℝ} {g : Vec3 × ℝ → ℝ}
    (hg : Integrable g ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ Ioo 0 τ)))
    (hzero : ∀ x r, x ∉ K → g (x, r) = 0) :
    IntegrableOn (fun r => ∫ x, g (x, r)) (Ioo 0 τ) volume ∧
      ∫ z in K ×ˢ Ioo 0 τ, g z = ∫ r in Ioo 0 τ, ∫ x, g (x, r) := by
  have hslice : ∀ r, ∫ x in K, g (x, r) = ∫ x, g (x, r) := fun r =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hzero x r hx
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hg ⊢
  refine ⟨?_, ?_⟩
  · have h := hg.integral_prod_right
    exact h.congr (Eventually.of_forall fun r => hslice r)
  · rw [integral_prod_symm _ hg]
    exact setIntegral_congr_fun measurableSet_Ioo fun r _ => hslice r

variable (ρ : RegMollifierProfile)
variable (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
variable (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)


/-- The pairing increment over `(s, t)`, `0 ≤ s < t`, as the time integral of
the flux and the pressure pairing. -/
theorem regEquiSrc_pairing_increment
(hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ)
    (hε : 0 < ε),
    let u := uε a ha ε
    let p := pε a ha ε
    let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      spatialPartial (fun y => u y i) j z
    let DD : ParabolicPoint → Fin 3 → Fin 3 → Vec3 := fun z i j k =>
      spatialPartial (fun y => spatialPartial (fun x => u x i) j y) k z
    let Dt : ParabolicPoint → Vec3 := fun z i => timePartial (fun y => u y i) z
    let Dp : ParabolicPoint → Vec3 := fun z i => spatialPartial (fun y => p y) i z
    (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
      Continuous (fun t : Set.Ici (0 : ℝ) =>
        realVectorL2OfCoordinateFunction
          (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
      (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
        regUniformMollifiedInitial ρ ε hε a ∧
      ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
    (∀ i : Fin 3, ContinuousOn (fun z => u z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j, ContinuousOn (fun z => D z i j)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i j k, ContinuousOn (fun z => DD z i j k)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ i, ContinuousOn (fun z => Dt z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)) ∧
    (∀ i, ContinuousOn (fun z => Dp z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
     letI : NormedAddCommGroup ParabolicPoint :=
       inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
     letI : NormedSpace ℝ ParabolicPoint :=
       inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
     ∀ i, ContDiffOn ℝ 1 (fun z => u z i)
       (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), ∀ i j,
      DifferentiableAt ℝ (fun x : Vec3 => D (x, z.2) i j) z.1) ∧
    (∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Icc δ T),
          vec3EuclideanNorm (u z) ≤ C ∧ |p z| ≤ C ∧
          (∀ i j, |D z i j| ≤ C) ∧
          (∀ i j k, |DD z i j k| ≤ C) ∧
          (∀ i, |Dt z i| ≤ C) ∧ (∀ i, |Dp z i| ≤ C)) ∧
    (∀ δ T : ℝ, 0 < δ → δ < T →
      (∀ i, MemLp (fun z : ParabolicPoint => u z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j, MemLp (fun z : ParabolicPoint => D z i j) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i j k, MemLp (fun z : ParabolicPoint => DD z i j k) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      (∀ i, MemLp (fun z : ParabolicPoint => Dt z i) 2
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
      MemLp p 2 (volume.restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ T)))) ∧
    (∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      Dt z i - (∑ j : Fin 3, DD z i j j) +
        (∑ j : Fin 3,
          regUniformMollifiedVelocity ρ ε hε u z j * D z i j) + Dp z i = 0) ∧
    (∀ t : ℝ, 0 < t →
      ∃ hF : ∀ i j : Fin 3, MemLp
        (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, t) i *
          u (x, t) j) (ENNReal.ofReal 2) volume,
        (fun x : Vec3 => p (x, t)) =ᵐ[volume]
          rieszPressureSliceRepresentative 2 (by norm_num)
            (fun i j => (hF i j).toLp
              (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u
                (x, t) i * u (x, t) j)) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x : Vec3, p (x, t) * spatialLaplacian ψ x) =
            -∑ i : Fin 3, ∑ j : Fin 3,
              ∫ x : Vec3, regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j * mixedSecond ψ i j x) ∧
    (∀ t : ℝ, 0 ≤ t →
      eLpNorm (regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation u D t =
      eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a))
            2 volume ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
    (w : Vec3 → Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    IntervalIntegrable (fun r => ∫ x, forcedHopfPairingFlux
        (regUniformMollifiedVelocity ρ ε hε (uε a ha ε)) (uε a ha ε) (fun _ => 0)
        (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z)
        (fun i y => w y i) (x, r)) volume s t ∧
    IntervalIntegrable (fun r => ∫ x, pε a ha ε (x, r) *
        ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x) volume s t ∧
    (∫ x, ∑ i : Fin 3, uε a ha ε (x, t) i * w x i) -
        (∫ x, ∑ i : Fin 3, uε a ha ε (x, s) i * w x i) =
      (∫ r in s..t, ∫ x, forcedHopfPairingFlux
        (regUniformMollifiedVelocity ρ ε hε (uε a ha ε)) (uε a ha ε) (fun _ => 0)
        (fun z i j => spatialPartial (fun y => uε a ha ε y i) j z)
        (fun i y => w y i) (x, r)) +
      ∫ r in s..t, ∫ x, pε a ha ε (x, r) *
        ∑ i : Fin 3, spatialDeriv (fun y => w y i) i x := by
  set U := uε a ha ε with hU_def
  set J := regUniformMollifiedVelocity ρ ε hε U with hJ_def
  set P := pε a ha ε with hP_def
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j => spatialPartial (fun y => U y i) j z
  let wc : Fin 3 → Vec3 → ℝ := fun i y => w y i
  let K : Set Vec3 := tsupport w
  set T : ℝ := t + 1 with hT_def
  have hT : 0 < T := by linarith only [hs, hst]
  have hK : IsCompact K := hwc
  have hwi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i) := fun i => (contDiff_apply ℝ ℝ i).comp hw
  have hwK : ∀ i, tsupport (wc i) ⊆ K := fun i =>
    tsupport_comp_subset (g := fun v : Vec3 => v i) rfl w
  have hU3 := regEquiSrc_velocity_slab_three ρ uε pε hregularised a ha ε hε T
  have hJ3 := regEquiSrc_transport_slab_three ρ uε pε hregularised a ha ε hε T
  have hD2 := regEquiSrc_gradient_slab_two ρ uε pε hregularised a ha ε hε T
  have hf2 : MemLp (fun _ : ParabolicPoint => (0 : Vec3)) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := MemLp.zero
  have hfinK := forcedHopf_slab_isFiniteMeasure hK T
  have hsubK : spaceTimeSet K (Ioo 0 T) ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    prod_mono (subset_univ K) Ioo_subset_Ioi_self
  have hPK : Integrable P (volume.restrict (spaceTimeSet K (Ioo 0 T))) :=
    ((regEquiSrc_pressure_bound ρ uε pε hregularised a ha ε hε).1.mono_measure
      (Measure.restrict_mono hsubK le_rfl)).integrable
      (ENNReal.one_le_ofReal.2 (by norm_num))
  obtain ⟨⟨hSlice, hL2c, -, -⟩, -⟩ := hregularised a ha ε hε
  have hwL2 : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hwc
  have hcont : ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * wc i x) (Ici 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Ici (0 : ℝ)).domRestrict (fun t => ∫ x, ∑ i : Fin 3, U (x, t) i * wc i x) =
        fun t : Set.Ici (0 : ℝ) => inner ℝ
          (realVectorL2OfCoordinateFunction (fun x : Vec3 => U (x, t.1)) (hSlice t.1 t.2))
          (realVectorL2OfCoordinateFunction w hwL2) := by
      funext t
      rw [inner_realVectorL2OfCoordinateFunction
        (realVectorL2OfCoordinateFunction_rep _ (hSlice t.1 t.2)).symm w hwL2]
      change ∫ x, ∑ i : Fin 3, U (x, t.1) i * w x i = _
      exact integral_congr_ae (Eventually.of_forall fun x =>
        Finset.sum_congr rfl fun i _ => mul_comm _ _)
    rw [heq]
    exact hL2c.inner continuous_const
  have hmom : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              J z j * U z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              D z i j * spatialPartial (fun y => φ y i) j z
          - P z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, (fun _ : ParabolicPoint => (0 : Vec3)) z i * φ z i = 0 := by
    intro φ hφ
    have h := regMomentum_of_regularised ρ uε pε hregularised a ha ε hε φ hφ
    refine (integral_congr_ae (Eventually.of_forall fun z => ?_)).trans h
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    rfl
  have hkey := forcedLerayLimit_regPairing_sub_eq hT hwi hK hwK hU3 hJ3 hD2 hf2 hPK hcont hmom
  -- integrability of the two parts on `K × (0, T)`
  have hflux := forcedHopf_pairingFlux_integrable (T := T) (f := fun _ => 0) hwi hK hwK hJ3 hU3
    hD2 hf2
  have hdivtop : MemLp (fun z : ParabolicPoint => ∑ i : Fin 3, spatialDeriv (wc i) i z.1) ⊤
      (volume.restrict (spaceTimeSet K (Ioo 0 T))) := by
    have hdc : Continuous (fun x : Vec3 => ∑ i : Fin 3, spatialDeriv (wc i) i x) :=
      continuous_finsetSum _ fun i _ =>
        (CKN.contDiff_spatialDeriv_smooth (hwi i) i).continuous
    have hdcs : HasCompactSupport (fun x : Vec3 => ∑ i : Fin 3, spatialDeriv (wc i) i x) := by
      refine HasCompactSupport.intro hK fun x hx => ?_
      exact Finset.sum_eq_zero fun i _ => (regEquiSrc_test_zero hx i i).2
    exact forcedHopf_memLp_top_spatial hdc hdcs
  have hpress : Integrable (fun z : ParabolicPoint => P z * ∑ i : Fin 3,
      spatialDeriv (wc i) i z.1) (volume.restrict (spaceTimeSet K (Ioo 0 T))) :=
    stability_integrable_mul_bounded_test _ le_rfl (memLp_one_iff_integrable.2 hPK) hdivtop
  have hzeroF : ∀ x r, x ∉ K → forcedHopfPairingFlux J U (fun _ => 0) D wc (x, r) = 0 := by
    intro x r hx
    simp only [forcedHopfPairingFlux, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    simp only [wc, (regEquiSrc_test_zero hx _ _).2, mul_zero, Finset.sum_const_zero, sub_zero]
  have hzeroP : ∀ x r, x ∉ K → P (x, r) * ∑ i : Fin 3, spatialDeriv (wc i) i x = 0 := by
    intro x r hx
    simp only [wc, (regEquiSrc_test_zero hx _ _).2, Finset.sum_const_zero, mul_zero]
  -- the increment from time zero
  have hsubτ : ∀ τ, τ ≤ T → spaceTimeSet K (Ioo 0 τ) ⊆ spaceTimeSet K (Ioo 0 T) := fun τ hτ =>
    prod_mono subset_rfl (Ioo_subset_Ioo_right hτ)
  have hfromzero : ∀ τ, 0 ≤ τ → τ < T →
      (∫ x, ∑ i : Fin 3, U (x, τ) i * w x i) - (∫ x, ∑ i : Fin 3, U (x, 0) i * w x i) =
        (∫ r in (0 : ℝ)..τ, ∫ x, forcedHopfPairingFlux J U (fun _ => 0) D wc (x, r)) +
          ∫ r in (0 : ℝ)..τ, ∫ x, P (x, r) * ∑ i : Fin 3, spatialDeriv (wc i) i x := by
    intro τ hτ0 hτT
    rcases hτ0.eq_or_lt with h0 | hτpos
    · subst h0
      simp
    have hflτ : Integrable (forcedHopfPairingFlux J U (fun _ => 0) D wc)
        (volume.restrict (spaceTimeSet K (Ioo 0 τ))) :=
      hflux.mono_measure (Measure.restrict_mono (hsubτ τ hτT.le) le_rfl)
    have hprτ : Integrable (fun z : ParabolicPoint => P z * ∑ i : Fin 3,
        spatialDeriv (wc i) i z.1) (volume.restrict (spaceTimeSet K (Ioo 0 τ))) :=
      hpress.mono_measure (Measure.restrict_mono (hsubτ τ hτT.le) le_rfl)
    have hF1 := regEquiSrc_slab_integral (g := fun p : Vec3 × ℝ =>
      forcedHopfPairingFlux J U (fun _ => 0) D wc p) hflτ hzeroF
    have hF2 := regEquiSrc_slab_integral (g := fun p : Vec3 × ℝ =>
      P p * ∑ i : Fin 3, spatialDeriv (wc i) i p.1) hprτ hzeroP
    have e1 : ∫ z in spaceTimeSet K (Ioo 0 τ), forcedHopfPairingFlux J U (fun _ => 0) D wc z =
        ∫ r in Ioo 0 τ, ∫ x, forcedHopfPairingFlux J U (fun _ => 0) D wc (x, r) := hF1.2
    have e2 : ∫ z in spaceTimeSet K (Ioo 0 τ), P z * ∑ i : Fin 3, spatialDeriv (wc i) i z.1 =
        ∫ r in Ioo 0 τ, ∫ x, P (x, r) * ∑ i : Fin 3, spatialDeriv (wc i) i x := hF2.2
    have h := hkey τ ⟨hτpos, hτT⟩
    rw [integral_add hflτ hprτ, e1, e2] at h
    rw [intervalIntegral.integral_of_le hτpos.le, intervalIntegral.integral_of_le hτpos.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    exact h
  -- interval integrability on `(0, T)`
  have hIF := (regEquiSrc_slab_integral (g := fun p : Vec3 × ℝ =>
      forcedHopfPairingFlux J U (fun _ => 0) D wc p) hflux hzeroF).1
  have hIP := (regEquiSrc_slab_integral (g := fun p : Vec3 × ℝ =>
      P p * ∑ i : Fin 3, spatialDeriv (wc i) i p.1) hpress hzeroP).1
  have hII : ∀ {g : ℝ → ℝ}, IntegrableOn g (Ioo 0 T) volume → ∀ x y, 0 ≤ x → 0 ≤ y →
      x ≤ T → y ≤ T → IntervalIntegrable g volume x y := by
    intro g hg x y hx hy hxT hyT
    refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2 hg |>.mono_set ?_
    rw [uIcc_of_le hT.le]
    exact uIcc_subset_Icc ⟨hx, hxT⟩ ⟨hy, hyT⟩
  have htT : t ≤ T := by linarith only
  have hsT : s ≤ T := by linarith only [hst]
  refine ⟨hII hIF s t hs (hs.trans hst.le) hsT htT, hII hIP s t hs (hs.trans hst.le) hsT htT, ?_⟩
  have ht := hfromzero t (hs.trans hst.le) (by linarith only)
  have hs' := hfromzero s hs (by linarith only [hst])
  rw [← intervalIntegral.integral_interval_sub_left (hII hIF 0 t le_rfl (hs.trans hst.le)
      hT.le htT) (hII hIF 0 s le_rfl hs hT.le hsT),
    ← intervalIntegral.integral_interval_sub_left (hII hIP 0 t le_rfl (hs.trans hst.le)
      hT.le htT) (hII hIP 0 s le_rfl hs hT.le hsT)]
  linarith only [ht, hs']

end CKN.Leray

end
