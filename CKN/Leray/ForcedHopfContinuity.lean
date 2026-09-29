-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedHopfPairing
public import CKN.Leray.LerayHopfLimitPropLH2

/-!
# Weak continuity of the forced Leray--Hopf limit

This is the weak-continuity clause (LH2) in the proof of `thm:leray-forced`.
For a smooth, compactly supported, divergence-free spatial field, the
increment of the pairing of each forced regularized solution from time `0` is
the space-time integral of the momentum flux (`lem:forced-equicontinuity`).
The strong `L³` convergence of the velocities and of their mollifications and
the weak `L²` convergence of the gradients pass the flux integrals to the
limit, so the limit pairing is its initial value plus the flux integral of the
limit, which is continuous in time. The uniform energy bound on `[0,T]` and
the density of solenoidal tests in the weakly divergence-free fields extend
continuity to every `L²` field.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The weak-continuity clause (LH2) on `[0,T]` from continuity of the
pairings with smooth compactly supported solenoidal fields, a bound on
`[0,T]`, and weak divergence freedom on `[0,T]`. -/
theorem forcedHopf_weakContinuity
    (T : ℝ) (u : ParabolicPoint → Vec3) (M : ℝ) (hM : 0 ≤ M)
    (hdiv : ∀ t ∈ Icc 0 T, IsWeakDivFreeL2 (fun x => u (x, t)))
    (hnorm : ∀ t (ht : t ∈ Icc 0 T), ‖(lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3))‖ ≤ M)
    (hcontTest : ∀ wc : Fin 3 → Vec3 → ℝ, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i)) →
      (∀ i, HasCompactSupport (wc i)) →
      (∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0) →
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) (Icc 0 T)) :
    ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * w x i) (Icc 0 T) := by
  classical
  let v : ℝ → Lp L2Vec3 2 (volume : Measure Vec3) := fun t =>
    if ht : t ∈ Icc 0 T then (lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3)) else 0
  have hv : ∀ t (ht : t ∈ Icc 0 T), v t = (lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3)) := by
    intro t ht
    change (if h : t ∈ Icc 0 T then _ else _) = _
    split_ifs
    rfl
  have hpair : ∀ t (ht : t ∈ Icc 0 T) (w : Vec3 → Vec3) (hw : MemLp w 2 volume),
      inner ℝ (v t) ((lerayHopfLimit_toLp_memLp hw).toLp
        (fun x => (WithLp.toLp 2 (w x) : L2Vec3))) =
        ∫ x, ∑ i : Fin 3, u (x, t) i * w x i := by
    intro t ht w hw
    rw [hv t ht]
    exact lerayHopfLimit_inner_toLp_eq (hdiv t ht).1 hw
  have hcont : ∀ s ∈ lerayHopfLimitSolenoidalTests,
      ContinuousOn (fun t => inner ℝ (v t) s) (Icc 0 T) := by
    rintro s ⟨wc, hwc, hwcc, hwdiv, hw, rfl⟩
    refine (hcontTest wc hwc hwcc hwdiv).congr (fun t ht => ?_)
    exact hpair t ht _ hw
  have hmemS : ∀ t ∈ Icc 0 T,
      v t ∈ (Submodule.span ℝ lerayHopfLimitSolenoidalTests).topologicalClosure := by
    intro t ht
    rw [hv t ht]
    exact closure_mono Submodule.subset_span
      (lerayHopfLimit_mem_closure_solenoidalTests (hdiv t ht))
  have hbound : ∀ t ∈ Icc 0 T, ‖v t‖ ≤ M := by
    intro t ht
    rw [hv t ht]
    exact hnorm t ht
  intro w hw
  have h := lerayHopfLimit_continuousOn_inner_of_mem_closure_span
    lerayHopfLimitSolenoidalTests T M hM v hbound hmemS hcont
    ((lerayHopfLimit_toLp_memLp hw).toLp (fun x => (WithLp.toLp 2 (w x) : L2Vec3)))
  exact h.congr (fun t ht => (hpair t ht w hw).symm)

/-- The flux integrals over `K × (0,t)` of the regularized solutions converge
to the flux integral of the limit: strong `L³` convergence of the velocities
and of their mollifications passes the transport term, weak `L²` convergence
of the gradients passes the viscous term, and the force term is fixed. -/
theorem forcedHopf_flux_tendsto
    {t : ℝ} {K : Set Vec3} (hK : IsCompact K)
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i))
    (hwK : ∀ i, tsupport (wc i) ⊆ K)
    (U Jv : ℕ → ParabolicPoint → Vec3) (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hU3 : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hJ3 : ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hu3 : MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) atTop (𝓝 0))
    (hJconv : Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) atTop (𝓝 0))
    (hD : ∀ n, MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hDu : MemLp Du 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))))
    (hweak : ∀ i j, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) →
      Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
          Dseq n z i j * w z)
        atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Du z i j * w z)))
    (hf : MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) :
    Tendsto (fun n => ∫ z in spaceTimeSet K (Ioo 0 t),
        forcedHopfPairingFlux (Jv n) (U n) f (Dseq n) wc z) atTop
      (𝓝 (∫ z in spaceTimeSet K (Ioo 0 t), forcedHopfPairingFlux u u f Du wc z)) := by
  have hwc : ∀ i, HasCompactSupport (wc i) := fun i =>
    IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hwK i)
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)
  let SK : Set ParabolicPoint := spaceTimeSet K (Ioo 0 t)
  let μ : Measure ParabolicPoint := volume.restrict S
  let νK : Measure ParabolicPoint := volume.restrict SK
  have : IsFiniteMeasure νK := forcedHopf_slab_isFiniteMeasure hK t
  have hSK : SK ⊆ S := Set.prod_mono (subset_univ K) subset_rfl
  have hSKmeas : MeasurableSet SK := hK.isClosed.measurableSet.prod measurableSet_Ioo
  have hνK : νK ≤ μ := Measure.restrict_mono_set volume hSK
  have hUK : ∀ n, MemLp (U n) 3 νK := fun n => (hU3 n).mono_measure hνK
  have hJK : ∀ n, MemLp (Jv n) 3 νK := fun n => (hJ3 n).mono_measure hνK
  have huK : MemLp u 3 νK := hu3.mono_measure hνK
  have hDK : ∀ n, MemLp (Dseq n) 2 νK := fun n => (hD n).mono_measure hνK
  have hDuK : MemLp Du 2 νK := hDu.mono_measure hνK
  have hfK : MemLp f 2 νK := hf.mono_measure hνK
  have hUconvK : Tendsto (fun n => eLpNorm (U n - u) 3 νK) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUconv
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ hνK)
  have hJconvK : Tendsto (fun n => eLpNorm (Jv n - u) 3 νK) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJconv
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ hνK)
  have hwtop : ∀ i, MemLp (fun z : ParabolicPoint => wc i z.1) ∞ νK := fun i =>
    forcedHopf_memLp_top_spatial (hw i).continuous (hwc i)
  have hdwtop : ∀ i j, MemLp (fun z : ParabolicPoint => spatialDeriv (wc i) j z.1) ∞ νK :=
    fun i j => forcedHopf_spatialDeriv_memLp_top (hw i) (hwc i) j
  have hrestrict : μ.restrict SK = νK := by
    change (volume.restrict S).restrict SK = volume.restrict SK
    rw [Measure.restrict_restrict hSKmeas, inter_eq_left.mpr hSK]
  have hweakK : ∀ i j (w : ParabolicPoint → ℝ), MemLp w 2 νK →
      Tendsto (fun n => ∫ z, Dseq n z i j * w z ∂νK) atTop
        (𝓝 (∫ z, Du z i j * w z ∂νK)) := by
    intro i j w hw'
    have hwS : MemLp (SK.indicator w) 2 μ := by
      rw [memLp_indicator_iff_restrict hSKmeas, hrestrict]
      exact hw'
    have hloc : ∀ F : ParabolicPoint → ℝ,
        ∫ z in S, F z * SK.indicator w z = ∫ z, F z * w z ∂νK := by
      intro F
      have hpt : (fun z => F z * SK.indicator w z) = SK.indicator (fun z => F z * w z) := by
        funext z
        rw [indicator_mul_right]
      change ∫ z, F z * SK.indicator w z ∂μ = _
      rw [hpt, integral_indicator hSKmeas, hrestrict]
    have hconv := hweak i j (SK.indicator w) hwS
    have e1 : (fun n => ∫ z in S, Dseq n z i j * SK.indicator w z) =
        fun n => ∫ z, Dseq n z i j * w z ∂νK := funext fun n => hloc _
    have e2 : ∫ z in S, Du z i j * SK.indicator w z = ∫ z, Du z i j * w z ∂νK := hloc _
    rw [e1, e2] at hconv
    exact hconv
  have hA := lerayHopfLimit_advectiveTerm_tendsto νK U Jv u hUK hJK huK hUconvK hJconvK
    (fun i j z => spatialDeriv (wc i) j z.1) hdwtop
  have hB := lerayHopfLimit_weakGradientTerm_tendsto νK Dseq Du
    (fun n i j => ((hDK n).eval i).eval j) (fun i j => (hDuK.eval i).eval j) hweakK
    (fun i j z => spatialDeriv (wc i) j z.1) (fun i j => (hdwtop i j).mono_exponent le_top)
  have hsplit : ∀ (J V : ParabolicPoint → Vec3) (E : ParabolicPoint → Fin 3 → Vec3),
      MemLp J 3 νK → MemLp V 3 νK → MemLp E 2 νK →
      ∫ z in SK, forcedHopfPairingFlux J V f E wc z =
        (∫ z, ∑ i : Fin 3, ∑ j : Fin 3, V z i * J z j * spatialDeriv (wc i) j z.1 ∂νK)
          - (∫ z, ∑ i : Fin 3, ∑ j : Fin 3, E z i j * spatialDeriv (wc i) j z.1 ∂νK)
          + ∫ z, ∑ i : Fin 3, f z i * wc i z.1 ∂νK := by
    intro J V E hJ hV hE
    have h1 : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        V z i * J z j * spatialDeriv (wc i) j z.1) νK :=
      (forcedHopf_transport_integrable νK hJ hV hdwtop).congr (ae_of_all _ fun z =>
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring)))
    have h2 : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
        E z i j * spatialDeriv (wc i) j z.1) νK :=
      integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        stability_integrable_mul_bounded_test νK (by norm_num)
          ((hE.eval i).eval j) (hdwtop i j)))
    have h3 : Integrable (fun z => ∑ i : Fin 3, f z i * wc i z.1) νK :=
      integrable_finsetSum _ (fun i _ =>
        stability_integrable_mul_bounded_test νK (by norm_num) (hfK.eval i) (hwtop i))
    calc ∫ z in SK, forcedHopfPairingFlux J V f E wc z
        = ∫ z, ((∑ i : Fin 3, ∑ j : Fin 3, V z i * J z j * spatialDeriv (wc i) j z.1)
            - ∑ i : Fin 3, ∑ j : Fin 3, E z i j * spatialDeriv (wc i) j z.1)
            + ∑ i : Fin 3, f z i * wc i z.1 ∂νK := by
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          simp only [forcedHopfPairingFlux]
          congr 2
          exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      _ = _ := (integral_add (h1.sub h2) h3).trans
          (congrArg (· + ∫ z, ∑ i : Fin 3, f z i * wc i z.1 ∂νK) (integral_sub h1 h2))
  change Tendsto (fun n => ∫ z in SK, forcedHopfPairingFlux (Jv n) (U n) f (Dseq n) wc z)
    atTop (𝓝 (∫ z in SK, forcedHopfPairingFlux u u f Du wc z))
  simp only [hsplit _ _ _ (hJK _) (hUK _) (hDK _), hsplit u u Du huK huK hDuK]
  exact (hA.sub hB).add tendsto_const_nhds

/-- The limit pairing with a smooth, compactly supported, divergence-free
field is continuous on `[0,T]`: it equals its initial value plus the flux
integral of the limit over `K × (0,t)`, by `lem:forced-equicontinuity` for the
regularized solutions and the convergence of the flux integrals. -/
theorem forcedHopf_limitPairing_continuousOn
    {T : ℝ} (hT : 0 < T)
    {wc : Fin 3 → Vec3 → ℝ} (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (wc i))
    (hwc : ∀ i, HasCompactSupport (wc i))
    (hdivw : ∀ x, ∑ i : Fin 3, spatialDeriv (wc i) i x = 0)
    (U Jv : ℕ → ParabolicPoint → Vec3) (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (P : ℕ → ParabolicPoint → ℝ)
    (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hmom : ∀ n, ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              Jv n z j * U n z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Dseq n z i j * spatialPartial (fun y => φ y i) j z
          - P n z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (hcont : ∀ n, ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, U n (x, t) i * wc i x)
      (Ici 0))
    (hU3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hJ3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hu3 : ∀ s : ℝ, 0 < s → MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hUconv : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0))
    (hJconv : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0))
    (hD : ∀ s : ℝ, 0 < s → ∀ n, MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hDu : ∀ s : ℝ, 0 < s → MemLp Du 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hweak : ∀ s : ℝ, 0 < s → ∀ i j, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) →
      Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
          Dseq n z i j * w z)
        atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s), Du z i j * w z)))
    (hf : ∀ s : ℝ, 0 < s → MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hlim : ∀ t ∈ Icc 0 T,
      Tendsto (fun n => ∫ x, ∑ i : Fin 3, U n (x, t) i * wc i x) atTop
        (𝓝 (∫ x, ∑ i : Fin 3, u (x, t) i * wc i x))) :
    ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * wc i x) (Icc 0 T) := by
  let K : Set Vec3 := ⋃ i, tsupport (wc i)
  have hK : IsCompact K := isCompact_iUnion (fun i => hwc i)
  have hwK : ∀ i, tsupport (wc i) ⊆ K := fun i => subset_iUnion (fun i => tsupport (wc i)) i
  let Q : ℝ → ℝ := fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * wc i x
  let Ψ : ℝ → ℝ := fun t => ∫ z in spaceTimeSet K (Ioo 0 t),
    forcedHopfPairingFlux u u f Du wc z
  have hΨ : ContinuousOn Ψ (Icc 0 T) :=
    forcedHopf_continuousOn_setIntegral_slab K T _
      (forcedHopf_pairingFlux_integrable hw hK hwK (hu3 T hT) (hu3 T hT) (hDu T hT) (hf T hT))
  have hQ : ∀ t ∈ Icc 0 T, Q t = Q 0 + Ψ t := by
    intro t ht
    rcases ht.1.lt_or_eq with htpos | hzero
    · have hT1 : 0 < T + 1 := by linarith only [hT]
      have hincr : ∀ n, (∫ x, ∑ i : Fin 3, U n (x, t) i * wc i x) -
          ∫ x, ∑ i : Fin 3, U n (x, 0) i * wc i x =
            ∫ z in spaceTimeSet K (Ioo 0 t),
              forcedHopfPairingFlux (Jv n) (U n) f (Dseq n) wc z := fun n =>
        forcedHopf_regPairing_sub_eq hT1 hw hK hwK hdivw (hU3 _ hT1 n) (hJ3 _ hT1 n)
          (hD _ hT1 n) (hf _ hT1) (hcont n) (hmom n) t ⟨htpos, by linarith only [ht.2]⟩
      have hflux := forcedHopf_flux_tendsto hK hw hwK U Jv Dseq u f Du (hU3 t htpos)
        (hJ3 t htpos) (hu3 t htpos) (hUconv t htpos) (hJconv t htpos) (hD t htpos)
        (hDu t htpos) (hweak t htpos) (hf t htpos)
      have hsub := (hlim t ht).sub (hlim 0 ⟨le_rfl, hT.le⟩)
      simp only [hincr] at hsub
      have heq := tendsto_nhds_unique hsub hflux
      change Q t - Q 0 = Ψ t at heq
      linarith only [heq]
    · subst hzero
      have hΨ0 : Ψ 0 = 0 := by
        change ∫ z in spaceTimeSet K (Ioo 0 0), forcedHopfPairingFlux u u f Du wc z = 0
        rw [Ioo_self, show spaceTimeSet K (∅ : Set ℝ) = ∅ from Set.prod_empty,
          Measure.restrict_empty, integral_zero_measure]
      rw [hΨ0, add_zero]
  exact (continuousOn_const.add hΨ).congr hQ

end CKN.Leray

end
