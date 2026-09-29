-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureProviderEventual

/-!
# Removing the Helmholtz cutoffs in the forced momentum identity

In the proof of `thm:assoc-pressure-forced` the momentum identity is first
proved on the compact Helmholtz cutoffs `Φ_n` of a test `φ`, in the residual
form `∫ I(Φ_n) = ∫ r · Φ_n`, where `I` is the velocity--gradient--pressure
momentum integrand and `r = f - ∇p_f` is the square-integrable force residual.
Dominated convergence removes the cutoffs: the derivatives and the values of
`Φ_n` are bounded by fixed multiples of spatial decay profiles and agree with
those of `φ` for large `n` at every point.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The forced momentum integrand in residual form: the unforced momentum
integrand minus the pairing of the force residual with the test. -/
def forcedAssociatedPressureResidualIntegrand
    (u : Vec3 × ℝ → Vec3) (Du : Vec3 × ℝ → Fin 3 → Vec3)
    (p : Vec3 × ℝ → ℝ) (r : Vec3 × ℝ → Vec3) (φ : Vec3 × ℝ → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  associatedPressureMomentumProductIntegrand u Du p φ z - ∑ i : Fin 3, r z i * φ z i

private theorem forcedAssociatedPressureLimit_compact_memLp
    {T : ℝ} {q : ℝ≥0∞} {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    MemLp g q
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  have hglobal : MemLp g q (volume : Measure (Vec3 × ℝ)) :=
    hg.continuous.memLp_of_hasCompactSupport hgc
  have hrestrict := hglobal.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
  simpa using hrestrict

/-- The forced momentum integrand in residual form is integrable on the slab
for every compactly supported test. -/
theorem forcedAssociatedPressureResidualIntegrand_integrable
    {T : ℝ} {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {r : Vec3 × ℝ → Vec3} {Φ : Vec3 × ℝ → Vec3}
    (hU : MemLp u 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hDu : MemLp Du 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hTensor : ∀ i j, MemLp (fun z => u z i * u z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hr : MemLp r 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hΦ : Φ ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T)) :
    Integrable (fun z => associatedPressureMomentumProductIntegrand u Du p Φ z)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) ∧
      Integrable (fun z => ∑ i : Fin 3, r z i * Φ z i)
        ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  let μ : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let dTime (i : Fin 3) : Vec3 × ℝ → ℝ := CKN.timePartialProd (fun z => Φ z i)
  let dSpace (i j : Fin 3) : Vec3 × ℝ → ℝ := CKN.spatialPartialProd (fun z => Φ z i) j
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 3 : ℝ)) (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : Real.HolderTriple (5 / 3 : ℝ) (5 / 2 : ℝ) 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hComp (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hΦ i
  have hValMem (i : Fin 3) : MemLp (fun z => Φ z i) 2 μ := by
    simpa using forcedAssociatedPressureLimit_compact_memLp (T := T) (q := ENNReal.ofReal 2)
      (hComp i).1 (hComp i).2.1
  have hTimeMem (i : Fin 3) (s : ℝ) : MemLp (dTime i) (ENNReal.ofReal s) μ :=
    forcedAssociatedPressureLimit_compact_memLp (CKN.contDiff_timePartial (hComp i).1)
      (CKN.hasCompactSupport_timePartial (hComp i).2.1)
  have hSpaceMem (i j : Fin 3) (s : ℝ) : MemLp (dSpace i j) (ENNReal.ofReal s) μ :=
    forcedAssociatedPressureLimit_compact_memLp (CKN.spatialPartial_contDiff (hComp i).1 j)
      (CKN.hasCompactSupport_spatialPartial (hComp i).2.1 j)
  have hTimeSum : Integrable (fun z => ∑ i : Fin 3, u z i * dTime i z) μ := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hprod : MemLp ((fun z => u z i) * dTime i) 1 μ :=
      ((memLp_pi_iff.mp hU) i).mul (by simpa using hTimeMem i 2)
    exact memLp_one_iff_integrable.mp hprod
  have hConvSum : Integrable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j z) μ := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have hprod : MemLp ((fun z => u z i * u z j) * dSpace i j) 1 μ :=
      (hTensor i j).mul (hSpaceMem i j (5 / 2))
    exact memLp_one_iff_integrable.mp hprod
  have hGradSum : Integrable
      (fun z => ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j z) μ := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    have hprod : MemLp ((fun z => Du z i j) * dSpace i j) 1 μ :=
      ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j).mul (by simpa using hSpaceMem i j 2)
    exact memLp_one_iff_integrable.mp hprod
  have hPressure : Integrable (fun z => p z * ∑ i : Fin 3, dSpace i i z) μ := by
    have hsum : Integrable (fun z => ∑ i : Fin 3, p z * dSpace i i z) μ := by
      refine integrable_finsetSum _ fun i _ => ?_
      have hprod : MemLp (p * dSpace i i) 1 μ := hp.mul (hSpaceMem i i (5 / 2))
      exact memLp_one_iff_integrable.mp hprod
    simpa only [Finset.mul_sum] using hsum
  have hRes : Integrable (fun z => ∑ i : Fin 3, r z i * Φ z i) μ := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hprod : MemLp ((fun z => r z i) * fun z => Φ z i) 1 μ :=
      ((memLp_pi_iff.mp hr) i).mul (hValMem i)
    exact memLp_one_iff_integrable.mp hprod
  refine ⟨?_, hRes⟩
  change Integrable (fun z : Vec3 × ℝ =>
    -(∑ i : Fin 3, u z i * dTime i z)
      - ∑ i : Fin 3, ∑ j : Fin 3, u z i * u z j * dSpace i j z
      + ∑ i : Fin 3, ∑ j : Fin 3, Du z i j * dSpace i j z
      - p z * ∑ i : Fin 3, dSpace i i z) μ
  exact (hTimeSum.neg.sub hConvSum).add hGradSum |>.sub hPressure

/-- Dominated convergence for the forced momentum identity in residual form:
if the residual identity holds for a family `Φ_n` of compact tests whose
derivatives and values are bounded by fixed multiples of spatial decay
profiles and eventually agree with those of `φ` at every point, then it holds
for `φ`. -/
theorem forcedAssociatedPressureResidual_integral_eq_zero_of_cutoffs
    {T : ℝ} {u : Vec3 × ℝ → Vec3} {Du : Vec3 × ℝ → Fin 3 → Vec3}
    {p : Vec3 × ℝ → ℝ} {r : Vec3 × ℝ → Vec3} {φ : Vec3 × ℝ → Vec3}
    (hU : MemLp u 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hDu : MemLp Du 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hTensor : ∀ i j, MemLp (fun z => u z i * u z j)
      (ENNReal.ofReal (5 / 3 : ℝ)) ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (hr : MemLp r 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))))
    (Φ : ℕ → Vec3 × ℝ → Vec3)
    (hΦ : ∀ n, Φ n ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T))
    (Kd Kv : Set ℝ) (hKd : IsCompact Kd) (hKv : IsCompact Kv) (Cd Cv : ℝ)
    (hderiv : ∀ (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3),
      |CKN.timePartialProd (fun q => Φ n q i) z| ≤
          Cd * associatedPressureSpatialProfile Kd 2 z ∧
      |CKN.spatialPartialProd (fun q => Φ n q i) j z| ≤
          Cd * associatedPressureSpatialProfile Kd 2 z)
    (hvalue : ∀ (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3),
      |Φ n z i| ≤ Cv * associatedPressureSpatialProfile Kv 2 z)
    (htimeEv : ∀ (i : Fin 3) (z : Vec3 × ℝ), ∀ᶠ n : ℕ in atTop,
      CKN.timePartialProd (fun q => Φ n q i) z = CKN.timePartialProd (fun q => φ q i) z)
    (hspaceEv : ∀ (i j : Fin 3) (z : Vec3 × ℝ), ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd (fun q => Φ n q i) j z =
        CKN.spatialPartialProd (fun q => φ q i) j z)
    (hvalueEv : ∀ (i : Fin 3) (z : Vec3 × ℝ), ∀ᶠ n : ℕ in atTop, Φ n z i = φ z i)
    (hcutoff : ∀ n, ∫ z, forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0) :
    ∫ z, forcedAssociatedPressureResidualIntegrand u Du p r φ z
      ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) = 0 := by
  let μ : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  let Sd : Vec3 × ℝ → ℝ := associatedPressureSpatialProfile Kd 2
  let Sv : Vec3 × ℝ → ℝ := associatedPressureSpatialProfile Kv 2
  have hprofile : ∀ {K : Set ℝ}, IsCompact K → ∀ s : ℝ, 0 < s → 3 < 2 * s →
      MemLp (associatedPressureSpatialProfile K 2) (ENNReal.ofReal s) μ := by
    intro K hK s hs hms
    have hbase := associatedPressureSpatialProfile_memLp hK (m := 2) hs hms
    have hrestrict := hbase.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict] at hrestrict
    simpa using hrestrict
  have hSd2 : MemLp Sd 2 μ := by
    simpa [Sd] using hprofile hKd 2 (by norm_num) (by norm_num)
  have hSd52 : MemLp Sd (ENNReal.ofReal (5 / 2 : ℝ)) μ :=
    hprofile hKd (5 / 2) (by norm_num) (by norm_num)
  have hSv2 : MemLp Sv 2 μ := by
    simpa [Sv] using hprofile hKv 2 (by norm_num) (by norm_num)
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 := ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have : ENNReal.HolderTriple (ENNReal.ofReal (5 / 3 : ℝ)) (ENNReal.ofReal (5 / 2 : ℝ)) 1 := by
    have h : Real.HolderTriple (5 / 3 : ℝ) (5 / 2 : ℝ) 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  -- the dominating function
  let M : Vec3 × ℝ → ℝ := fun z =>
    associatedPressureMomentumProfileMajorant Cd Sd u Du p z +
      ∑ i : Fin 3, |r z i| * (Cv * Sv z)
  have hMint : Integrable M μ := by
    have h2 (g : Vec3 × ℝ → ℝ) (hg : MemLp g 2 μ) :
        Integrable (fun z => |g z| * Sd z) μ := by
      have hprod : MemLp ((fun z => |g z|) * Sd) 1 μ := by
        simpa only [Real.norm_eq_abs] using hg.norm.mul hSd2
      exact memLp_one_iff_integrable.mp hprod
    have h53 (g : Vec3 × ℝ → ℝ) (hg : MemLp g (ENNReal.ofReal (5 / 3 : ℝ)) μ) :
        Integrable (fun z => |g z| * Sd z) μ := by
      have hprod : MemLp ((fun z => |g z|) * Sd) 1 μ := by
        simpa only [Real.norm_eq_abs] using hg.norm.mul hSd52
      exact memLp_one_iff_integrable.mp hprod
    have hUsum : Integrable (fun z => ∑ i : Fin 3, |u z i| * Sd z) μ :=
      integrable_finsetSum _ fun i _ => h2 _ ((memLp_pi_iff.mp hU) i)
    have hNsum : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, |u z i * u z j| * Sd z) μ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h53 _ (hTensor i j)
    have hVsum : Integrable (fun z => ∑ i : Fin 3, ∑ j : Fin 3, |Du z i j| * Sd z) μ :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        h2 _ ((memLp_pi_iff.mp ((memLp_pi_iff.mp hDu) i)) j)
    have hPsum : Integrable (fun z => 3 * (|p z| * Sd z)) μ := (h53 p hp).const_mul 3
    have hMaj : Integrable (associatedPressureMomentumProfileMajorant Cd Sd u Du p) μ := by
      have hsum := ((hUsum.add hNsum).add hVsum).add hPsum
      have h := hsum.const_mul Cd
      refine h.congr (Eventually.of_forall fun z => ?_)
      simp only [associatedPressureMomentumProfileMajorant, Pi.add_apply]
    have hRsum : Integrable (fun z => ∑ i : Fin 3, |r z i| * (Cv * Sv z)) μ := by
      refine integrable_finsetSum _ fun i _ => ?_
      have hprod : MemLp ((fun z => |r z i|) * Sv) 1 μ := by
        simpa only [Real.norm_eq_abs] using ((memLp_pi_iff.mp hr) i).norm.mul hSv2
      have h := (memLp_one_iff_integrable.mp hprod).const_mul Cv
      refine h.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.mul_apply]
      ring
    exact hMaj.add hRsum
  have hbound : ∀ n z, |forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z| ≤ M z := by
    intro n z
    have h1 := associatedPressureMomentumProductIntegrand_abs_le_profileMajorant
      (u := u) (Du := Du) (p := p)
      (fun z i => (hderiv n z i 0).1) (fun z i j => (hderiv n z i j).2) z
    have h2 : |∑ i : Fin 3, r z i * Φ n z i| ≤ ∑ i : Fin 3, |r z i| * (Cv * Sv z) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hvalue n z i) (abs_nonneg _)
    exact (associatedPressureAbs_sub_le _ _).trans (add_le_add h1 h2)
  have hInt : ∀ n, Integrable
      (fun z => forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z) μ := by
    intro n
    obtain ⟨h1, h2⟩ := forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hp hr
      (hΦ n)
    exact h1.sub h2
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun n => forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z) atTop
      (𝓝 (forcedAssociatedPressureResidualIntegrand u Du p r φ z)) := by
    filter_upwards [] with z
    have hall : ∀ᶠ n : ℕ in atTop, (∀ i : Fin 3,
        CKN.timePartialProd (fun q => Φ n q i) z = CKN.timePartialProd (fun q => φ q i) z) ∧
        (∀ i j : Fin 3, CKN.spatialPartialProd (fun q => Φ n q i) j z =
          CKN.spatialPartialProd (fun q => φ q i) j z) ∧
        (∀ i : Fin 3, Φ n z i = φ z i) := by
      have hfin : ∀ {P : Fin 3 → ℕ → Prop}, (∀ i, ∀ᶠ n in atTop, P i n) →
          ∀ᶠ n in atTop, ∀ i, P i n := by
        intro P hP
        simpa only [eventually_all] using hP
      refine (hfin fun i => htimeEv i z).and ((hfin fun i => hfin fun j => hspaceEv i j z).and
        (hfin fun i => hvalueEv i z))
    have heq : ∀ᶠ n : ℕ in atTop,
        forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z =
          forcedAssociatedPressureResidualIntegrand u Du p r φ z := by
      filter_upwards [hall] with n ⟨ht, hs, hv⟩
      simp [forcedAssociatedPressureResidualIntegrand, associatedPressureMomentumProductIntegrand,
        ht, hs, hv]
    exact tendsto_const_nhds.congr' (EventuallyEq.symm heq)
  have hDCT := tendsto_integral_of_dominated_convergence M
    (fun n => (hInt n).aestronglyMeasurable) hMint
    (fun n => Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hbound n z) hlim
  have hzero : Tendsto (fun n => ∫ z,
      forcedAssociatedPressureResidualIntegrand u Du p r (Φ n) z ∂μ) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun n => (hcutoff n).symm)
  exact tendsto_nhds_unique hDCT hzero

end CKN.Leray

end
