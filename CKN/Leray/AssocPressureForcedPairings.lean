-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedProjection
public import CKN.Leray.AssocPressureCompactGradientCore
public import CKN.Leray.ForcedHopfSlab
public import CKN.Statements.SpaceTimeTestFunction
public import CKN.Statements.SpatialPartial

/-!
# Pairings for the projected force and force pressure

These integration-by-parts identities are used on the two components of the
Helmholtz decomposition of a compact test.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

def forcedPressureScalarSliceWeakTest
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (t : ℝ) :
    CKN.WeakTestFunction (Set.univ : Set Vec3) := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  have hK : IsCompact K := hgc.isCompact.image continuous_fst
  have hgSlice : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => g (x, t)) :=
    hg.comp (contDiff_id.prodMk contDiff_const)
  have hgcSlice : HasCompactSupport (fun x : Vec3 => g (x, t)) :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro x hx
      have hx' : (x, t) ∈ Function.support g := by
        change g (x, t) ≠ 0
        exact Function.mem_support.mp hx
      exact ⟨(x, t), (subset_tsupport (f := g)) hx', rfl⟩)
  exact ⟨fun x => g (x, t), hgSlice, hgcSlice, Set.subset_univ _⟩

/-- A space-time scalar gradient pairs to zero with a square-integrable field
whose almost-everywhere time slices satisfy the weak-divergence identity. -/
theorem forcedField_pairing_scalarGradient_zero
    {T : ℝ} {R : Vec3 × ℝ → Vec3}
    (hR : MemLp R 2 ((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 T))))
    (hdiv : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3, R (x, t) i * ψ.partialDeriv i x = 0)
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∫ z : Vec3 × ℝ, ∑ i : Fin 3,
      R z i * CKN.spatialPartialProd g i z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F : Vec3 × ℝ → ℝ := fun z =>
    ∑ i : Fin 3, R z i * CKN.spatialPartialProd g i z
  have hGrad (i : Fin 3) : MemLp (CKN.spatialPartialProd g i) 2 μ := by
    have hglobal : MemLp (CKN.spatialPartialProd g i) 2
        (volume : Measure (Vec3 × ℝ)) := by
      change MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) 2 _
      have hcont : Continuous (fun z : Vec3 × ℝ => CKN.spatialPartial g i z) :=
        (CKN.spatialPartial_contDiff hg i).continuous
      have hcompact := CKN.hasCompactSupport_spatialPartial hgc i
      simpa [CKN.spatialPartialProd] using hcont.memLp_of_hasCompactSupport hcompact
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have hFint : Integrable F μ := by
    apply integrable_finsetSum (s := Finset.univ)
    intro i hi
    have hRi : MemLp (fun z : Vec3 × ℝ => R z i) 2 μ :=
      (memLp_pi_iff.mp hR) i
    have hprod : MemLp
        (fun z : Vec3 × ℝ => R z i * CKN.spatialPartialProd g i z) 1 μ :=
      hRi.mul (hGrad i)
    exact memLp_one_iff_integrable.mp (by simpa [F] using hprod)
  have hFubini : ∫ z : Vec3 × ℝ, F z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, F z ∂μ =
          ∫ z : ℝ × Vec3, F z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) F).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => F z.swap) hFint.swap
  have hzeroSlice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x, t) ∂volume = 0 := by
    filter_upwards [hdiv] with t ht
    let htest := forcedPressureScalarSliceWeakTest hg hgc t
    have hzero := ht htest
    have hpartial (i : Fin 3) (x : Vec3) :
        htest.partialDeriv i x = CKN.spatialPartialProd g i (x, t) := by
      rfl
    have hfun : (fun x : Vec3 => F (x, t)) =
        (fun x => ∑ i : Fin 3, R (x, t) i * htest.partialDeriv i x) := by
      funext x
      simp [F, hpartial]
    rw [hfun]
    exact hzero
  rw [hFubini, integral_congr_ae hzeroSlice]
  simp

/-- The forced weak-gradient clause gives the space-time integration-by-parts
identity against a compact smooth scalar test. -/
theorem forcedWeakGradient_pairing
    {T : ℝ} {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    (hU : MemLp u 2 ((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 T))))
    (hDu : MemLp Du 2 ((volume : Measure Vec3).prod
      (volume.restrict (Ioo 0 T))))
    (hweak : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (i j : Fin 3) :
    ∫ z : Vec3 × ℝ, Du z i j * g z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
    -∫ z : Vec3 × ℝ, u z i * CKN.spatialPartialProd g j z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let F : Vec3 × ℝ → ℝ := fun z => Du z i j * g z
  let G : Vec3 × ℝ → ℝ := fun z => u z i * CKN.spatialPartialProd g j z
  have hpartial : MemLp (CKN.spatialPartialProd g j) 2 μ := by
    have hglobal : MemLp (CKN.spatialPartialProd g j) 2
        (volume : Measure (Vec3 × ℝ)) := by
      change MemLp (fun z : Vec3 × ℝ => CKN.spatialPartial g j z) 2 _
      have hcont : Continuous (fun z : Vec3 × ℝ => CKN.spatialPartial g j z) :=
        (CKN.spatialPartial_contDiff hg j).continuous
      have hcompact := CKN.hasCompactSupport_spatialPartial hgc j
      simpa [CKN.spatialPartialProd] using hcont.memLp_of_hasCompactSupport hcompact
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have hFint : Integrable F μ := by
    have hDui : MemLp (fun z : Vec3 × ℝ => Du z i j) 2 μ :=
      (memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j
    change Integrable ((fun z : Vec3 × ℝ => Du z i j) * g) μ
    exact memLp_one_iff_integrable.mp
      (hDui.mul (associatedPressureCompact_memLp_two (T := T) hg hgc))
  have hGint : Integrable G μ := by
    have hui : MemLp (fun z : Vec3 × ℝ => u z i) 2 μ :=
      (memLp_pi_iff.mp hU) i
    change Integrable ((fun z : Vec3 × ℝ => u z i) *
      CKN.spatialPartialProd g j) μ
    exact memLp_one_iff_integrable.mp (hui.mul hpartial)
  have hFubini : ∫ z : Vec3 × ℝ, F z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, F z ∂μ =
          ∫ z : ℝ × Vec3, F z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) F).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, F (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => F z.swap) hFint.swap
  have hGfubini : ∫ z : Vec3 × ℝ, G z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, G (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, G z ∂μ =
          ∫ z : ℝ × Vec3, G z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) G).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, G (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => G z.swap) hGint.swap
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, F (x, t) ∂volume = -∫ x : Vec3, G (x, t) ∂volume := by
    filter_upwards [hweak] with t ht
    let htest := forcedPressureScalarSliceWeakTest hg hgc t
    have hpair := (hasWeakPartialDerivOn_iff_forall_testFunction.mp
      ((ht i) j)) htest
    have htestFun : htest.toFun = fun x : Vec3 => g (x, t) := rfl
    have hpartial' (x : Vec3) : htest.partialDeriv j x =
        CKN.spatialPartialProd g j (x, t) := by rfl
    have hpair' : ∫ x : Vec3, G (x, t) ∂volume =
        -∫ x : Vec3, F (x, t) ∂volume := by
      simpa [F, G, htestFun, hpartial', parabolicHomeomorph_symm_apply] using hpair
    linarith only [hpair']
  rw [hFubini, hGfubini, integral_congr_ae hslice, integral_neg]
/-- The force-pressure gradient pairs with a compact vector test as minus
the pressure paired with its divergence. -/
theorem forcePressureGradient_pairing
    {T : ℝ} {K : Set Vec3} {I : Set ℝ}
    (hK : MeasurableSet K) (hI : MeasurableSet I)
    (hIinside : I ⊆ Ioo 0 T)
    {p : Vec3 × ℝ → ℝ} {G : Vec3 × ℝ → Vec3}
    {g : Vec3 × ℝ → Vec3}
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))).restrict
        (K ×ˢ I)))
    (hG : MemLp G 2
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => p (x, t))
        (fun x => G (x, t)))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hsupp : tsupport g ⊆ K ×ˢ I) :
    ∫ z : Vec3 × ℝ, ∑ i : Fin 3, G z i * g z i
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) =
      -∫ z : Vec3 × ℝ, p z *
        (∑ i : Fin 3, CKN.spatialPartialProd (fun q => g q i) i z)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let Q : Set (Vec3 × ℝ) := K ×ˢ I
  let P : Vec3 × ℝ → ℝ := fun z =>
    p z * (∑ i : Fin 3, CKN.spatialPartialProd (fun q => g q i) i z)
  let H : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, G z i * g z i
  have hQmeas : MeasurableSet Q := by
    dsimp [Q]
    exact MeasurableSet.prod hK hI
  have hgsuppSlab : tsupport g ⊆ Set.univ ×ˢ Ioo 0 T :=
    hsupp.trans (Set.prod_mono (Set.subset_univ _) hIinside)
  have hgt : g ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) :=
    ⟨hg, hgc, hgsuppSlab⟩
  have hcomponent (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hgt i
  have hPind : MemLp (Q.indicator p) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    rw [memLp_indicator_iff_restrict hQmeas]
    simpa [μ, Q] using hp
  have hpartMem (i : Fin 3) : MemLp
      (CKN.spatialPartialProd (fun q => g q i) i) (ENNReal.ofReal (3 : ℝ)) μ := by
    have hglobal : MemLp (CKN.spatialPartialProd (fun q => g q i) i)
        (ENNReal.ofReal (3 : ℝ)) (volume : Measure (Vec3 × ℝ)) := by
      have hsm := CKN.spatialPartial_contDiff (hcomponent i).1 i
      have hcs := CKN.hasCompactSupport_spatialPartial (hcomponent i).2.1 i
      exact hsm.continuous.memLp_of_hasCompactSupport hcs
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  let forcedPressurePairingHolderTriple : ENNReal.HolderTriple
      (ENNReal.ofReal (3 / 2 : ℝ))
      (ENNReal.ofReal (3 : ℝ)) 1 := by
    have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hPterm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => p z * CKN.spatialPartialProd
        (fun q => g q i) i z) μ := by
    have hcomponentSupport : tsupport (fun q : Vec3 × ℝ => g q i) ⊆
        tsupport g :=
      CKN.tsupport_component_subset (V := ℝ) g i (fun z hz =>
        congrArg (fun v : Vec3 => v i) hz)
    have hprod : MemLp ((Q.indicator p) *
        CKN.spatialPartialProd (fun q => g q i) i) 1 μ :=
      hPind.mul (hpartMem i)
    have hAE : (fun z : Vec3 × ℝ => p z * CKN.spatialPartialProd
        (fun q => g q i) i z) =ᵐ[μ]
        fun z => Q.indicator p z * CKN.spatialPartialProd (fun q => g q i) i z := by
      filter_upwards [] with z
      by_cases hz : z ∈ Q
      · simp [hz]
      · have hnot : z ∉ tsupport (fun q : Vec3 × ℝ => g q i) := by
          intro hm
          exact hz (hsupp (hcomponentSupport hm))
        have hzpart := CKN.spatialPartial_eq_zero_off_tsupport hnot i
        have hzpart' : CKN.spatialPartialProd
            (fun q => g q i) i z = 0 := by
          simpa [CKN.spatialPartialProd] using hzpart
        rw [hzpart']
        simp [hz]
    exact (memLp_one_iff_integrable.mp hprod).congr hAE.symm
  have hGcomponent (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => G z i) 2 μ :=
    (memLp_pi_iff.mp hG) i
  have hgcomponent (i : Fin 3) : MemLp (fun z : Vec3 × ℝ => g z i) 2 μ := by
    have hglobal : MemLp (fun z : Vec3 × ℝ => g z i) 2
        (volume : Measure (Vec3 × ℝ)) :=
      (hcomponent i).1.continuous.memLp_of_hasCompactSupport (hcomponent i).2.1
    have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa [μ] using hrestrict
  have hHterm (i : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => G z i * g z i) μ := by
    exact memLp_one_iff_integrable.mp ((hGcomponent i).mul (hgcomponent i))
  have hPint : Integrable P μ := by
    dsimp [P]
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro i hi
    exact hPterm i
  have hHint : Integrable H μ := by
    dsimp [H]
    apply integrable_finsetSum
    intro i hi
    exact hHterm i
  have hPae : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ i : Fin 3,
      Integrable (fun x : Vec3 => p (x, t) *
        CKN.spatialPartialProd (fun q => g q i) i (x, t)) volume :=
    ae_all_iff.2 fun i => (hPterm i).prod_left_ae
  have hHae : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)), ∀ i : Fin 3,
      Integrable (fun x : Vec3 => G (x, t) i * g (x, t) i) volume :=
    ae_all_iff.2 fun i => (hHterm i).prod_left_ae
  have hPfubini : ∫ z : Vec3 × ℝ, P z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, P (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, P z ∂μ =
          ∫ z : ℝ × Vec3, P z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) P).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, P (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => P z.swap) hPint.swap
  have hHfubini : ∫ z : Vec3 × ℝ, H z ∂μ =
      ∫ t : ℝ, ∫ x : Vec3, H (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) := by
    calc
      ∫ z : Vec3 × ℝ, H z ∂μ =
          ∫ z : ℝ × Vec3, H z.swap
            ∂((volume.restrict (Ioo 0 T)).prod (volume : Measure Vec3)) := by
        simpa [μ, Function.comp_def] using
          (MeasureTheory.integral_prod_swap (μ := (volume : Measure Vec3))
            (ν := volume.restrict (Ioo 0 T)) H).symm
      _ = ∫ t : ℝ, ∫ x : Vec3, H (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T)) := by
        simpa using MeasureTheory.integral_prod
          (fun z : ℝ × Vec3 => H z.swap) hHint.swap
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∫ x : Vec3, P (x, t) ∂volume = -∫ x : Vec3, H (x, t) ∂volume := by
    filter_upwards [hgrad, hPae, hHae] with t ht hpint hhint
    have hpair (i : Fin 3) : ∫ x : Vec3,
        p (x, t) * CKN.spatialPartialProd (fun q => g q i) i (x, t) ∂volume =
        -∫ x : Vec3, G (x, t) i * g (x, t) i ∂volume := by
      let ψ := fun q : Vec3 × ℝ => g q i
      let htest := forcedPressureScalarSliceWeakTest
        (hcomponent i).1 (hcomponent i).2.1 t
      have hweak := (hasWeakPartialDerivOn_iff_forall_testFunction.mp (ht i)) htest
      have htestFun : htest.toFun = fun x : Vec3 => g (x, t) i := rfl
      have hpartial (x : Vec3) : htest.partialDeriv i x =
          CKN.spatialPartialProd ψ i (x, t) := by
        rfl
      simpa [htestFun, hpartial, ψ, mul_comm] using hweak
    have hPsum : ∫ x : Vec3, p (x, t) *
        (∑ i : Fin 3, CKN.spatialPartialProd (fun q => g q i) i (x, t))
        ∂volume = ∑ i : Fin 3, ∫ x : Vec3, p (x, t) *
          CKN.spatialPartialProd (fun q => g q i) i (x, t) ∂volume := by
      calc
        _ = ∫ x : Vec3, ∑ i : Fin 3, p (x, t) *
            CKN.spatialPartialProd (fun q => g q i) i (x, t) ∂volume := by
              congr 1
              funext x
              exact Finset.mul_sum _ _ _
        _ = _ := integral_finsetSum _ (fun i hi => hpint i)
    have hHsum : ∫ x : Vec3, (∑ i : Fin 3, G (x, t) i * g (x, t) i)
        ∂volume = ∑ i : Fin 3, ∫ x : Vec3, G (x, t) i * g (x, t) i ∂volume :=
      integral_finsetSum _ (fun i hi => hhint i)
    dsimp [P, H]
    rw [hPsum, hHsum]
    simp_rw [hpair]
    rw [Finset.sum_neg_distrib]
  rw [hPfubini, hHfubini]
  have houter : ∫ t : ℝ, ∫ x : Vec3, P (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T)) =
      -(∫ t : ℝ, ∫ x : Vec3, H (x, t) ∂volume
        ∂(volume.restrict (Ioo 0 T))) := by
    calc
      _ = ∫ t : ℝ, -(∫ x : Vec3, H (x, t) ∂volume)
          ∂(volume.restrict (Ioo 0 T)) := integral_congr_ae hslice
      _ = -(∫ t : ℝ, ∫ x : Vec3, H (x, t) ∂volume
          ∂(volume.restrict (Ioo 0 T))) := by rw [integral_neg]
  linarith only [houter]

end CKN.Leray

end
