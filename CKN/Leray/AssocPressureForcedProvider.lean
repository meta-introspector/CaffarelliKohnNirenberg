-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureForcedLimit
public import CKN.Leray.AssocPressureForcedCutoffValue
public import CKN.Leray.AssocPressureForcedValueEventual
public import CKN.Leray.AssocPressureForcedGradient
public import CKN.Leray.AssocPressureForcedPairings
public import CKN.Leray.AssocPressureForcedTensor
public import CKN.Leray.AssocPressureForcedPressure
public import CKN.Leray.AssocPressureForcedProjection
public import CKN.Leray.ForcePressure
public import CKN.Foundation.ParabolicMeasure

/-!
# The forced associated pressure

The pressure of `thm:assoc-pressure-forced` for a forced Leray--Hopf solution
on `ℝ³ × [0,T]` is `p = p_N + p_f`, where `p_N = P[u ⊗ u]` is the canonical
space-time Riesz pressure of the quadratic tensor and `p_f` is the force
pressure of `lem:force-pressure` for the force restricted to the slab. The
momentum identity against every compactly supported test is proved in the
residual form `∫ I(φ) = ∫ r · φ`, with `I` the momentum integrand for `p_N` and
`r = f - ∇p_f` the square-integrable, weakly divergence-free force residual:
on the solenoidal part of the Helmholtz cutoffs it is the forced momentum
identity (the gradient of `p_f` pairs to zero with a divergence-free test),
and on the gradient part both sides vanish. The cutoffs are removed by
dominated convergence, and the residual pairing is finally split back into the
force and the force-pressure terms.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The slab `ℝ³ × (0,T)` in CKN coordinates is the product slab. -/
private theorem forcedAssocProv_measure_eq (T : ℝ) :
    ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)) := by
  change (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) = _
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict, Measure.restrict_univ]

/-- A space-time set integral over the slab is a product-slab integral. -/
private theorem forcedAssocProv_setIntegral_eq (T : ℝ) (F : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), F z
      ∂(volume : Measure ParabolicPoint)) =
      ∫ z : Vec3 × ℝ, F (parabolicHomeomorph.symm z)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))) := by
  rw [setIntegral_parabolic_to_product, Measure.volume_eq_prod Vec3 ℝ,
    ← Measure.prod_restrict, Measure.restrict_univ]

/-- The zero extension of a slab-square-integrable force is square integrable
on every finite slab. -/
theorem forcedAssocProv_sliceForce_locallySquareIntegrable
    {T : ℝ} {f : ParabolicPoint → Vec3}
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    IsLocallySquareIntegrableForce
      ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)).indicator f) := by
  have hQ : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hglobal : MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)).indicator f) 2
      (volume : Measure ParabolicPoint) :=
    (memLp_indicator_iff_restrict hQ).2 hf
  intro S _
  exact hglobal.restrict _

/-- The momentum identity of `thm:assoc-pressure-forced` for the pressure
`p_N + p_f`, against every compactly supported test on the slab. The force
pressure `p_f` enters through its weak gradient `G`: `p_f` is locally
`L^{3/2}` on compact cylinders, `G` is square integrable, and the residual
`f - G` is weakly divergence free on almost every time slice. -/
theorem forcedAssociatedPressure_momentum_of_forcePressure
    {T : ℝ} {a : Vec3 → Vec3} {f : ParabolicPoint → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hF : CKN.IsForcedLerayHopfSolution T a f u Du)
    (hN : ∀ i j : Fin 3,
      MemLp (CKN.forcedQuadraticTensor T u i j)
        (ENNReal.ofReal (5 / 3 : ℝ)) (volume : Measure ParabolicPoint))
    (pf : ParabolicPoint → ℝ) (G : ParabolicPoint → Vec3)
    (hpfLoc : ∀ (K : Set Vec3) (I : Set ℝ), IsCompact K → IsCompact I → I ⊆ Ioo 0 T →
      MemLp pf (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K I)))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => pf (x, t)) (fun x => G (x, t)))
    (hres : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3, (f (x, t) - G (x, t)) i * ψ.partialDeriv i x = 0) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - (CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
                (CKN.forcedQuadraticTensor T u) hN z + pf z) *
              ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, f z i * φ z i = 0 := by
  intro φ hφ
  let μ : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T))
  have hT : 0 < T := hF.1
  have hf2 : MemLp f 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    hF.2.2.1
  let uP : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let DuP : Vec3 × ℝ → Fin 3 → Vec3 := fun z => Du (parabolicHomeomorph.symm z)
  let pN : Vec3 × ℝ → ℝ := CKN.Leray.rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num)
    (CKN.forcedQuadraticTensor T u) hN
  let fP : Vec3 × ℝ → Vec3 := fun z => f (parabolicHomeomorph.symm z)
  let GP : Vec3 × ℝ → Vec3 := fun z => G (parabolicHomeomorph.symm z)
  let pfP : Vec3 × ℝ → ℝ := fun z => pf (parabolicHomeomorph.symm z)
  let r : Vec3 × ℝ → Vec3 := fun z => fP z - GP z
  have hμeq : μ = (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T) := by
    change (volume : Measure Vec3).prod (volume.restrict (Ioo 0 T)) = _
    rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict, Measure.restrict_univ]
  -- integrability on the product slab
  have toμ : ∀ {E : Type} [NormedAddCommGroup E] {F : ParabolicPoint → E} {q : ℝ≥0∞},
      MemLp F q (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) →
      MemLp (fun z : Vec3 × ℝ => F (parabolicHomeomorph.symm z)) q μ := by
    intro E _ F q h
    have h' : MemLp (fun z : Vec3 × ℝ => F (parabolicHomeomorph.symm z)) q
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) : Measure (Vec3 × ℝ)) := h
    rwa [forcedAssocProv_measure_eq T] at h'
  have hU : MemLp uP 2 μ := forcedAssociatedPressure_velocity_memLp_two_productSlab hF
  have hDu : MemLp DuP 2 μ := forcedAssociatedPressure_gradient_memLp_two_productSlab hF
  have hTensor : ∀ i j, MemLp (fun z => uP z i * uP z j) (ENNReal.ofReal (5 / 3 : ℝ)) μ := by
    intro i j
    have hslab := (hN i j).restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    have hμ := toμ hslab
    refine hμ.ae_eq ?_
    have hmem : ∀ᵐ z ∂μ, z.2 ∈ Ioo 0 T := by
      rw [hμeq]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioo)] with z hz
      exact hz.2
    filter_upwards [hmem] with z hz
    simp [CKN.forcedQuadraticTensor, uP, hz]
  have hpN : MemLp pN (ENNReal.ofReal (5 / 3 : ℝ)) μ :=
    toμ (forcedAssociatedPressure_rieszPressure_memLp_slab hN)
  have hr : MemLp r 2 μ := (toμ hf2).sub (toμ hG)
  have hrdiv : ∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
        ∫ x : Vec3, ∑ i : Fin 3, r (x, t) i * ψ.partialDeriv i x = 0 := hres
  -- the test in product coordinates
  let φP : Vec3 × ℝ → Vec3 := fun z => φ ((z.1, z.2) : ParabolicPoint)
  have hφP : φP ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) := hφ
  -- the force-pressure gradient pairs as minus the force pressure times the divergence
  have hGpair : ∀ g : Vec3 × ℝ → Vec3,
      g ∈ CKN.spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z, ∑ i : Fin 3, GP z i * g z i ∂μ =
        -∫ z, pfP z * (∑ i : Fin 3, CKN.spatialPartialProd (fun q => g q i) i z) ∂μ := by
    intro g hg
    let K : Set Vec3 := Prod.fst '' tsupport g
    let I : Set ℝ := Prod.snd '' tsupport g
    have hKc : IsCompact K := hg.2.1.isCompact.image continuous_fst
    have hIc : IsCompact I := hg.2.1.isCompact.image continuous_snd
    have hIT : I ⊆ Ioo 0 T := by
      rintro t ⟨z, hz, rfl⟩
      exact (hg.2.2 hz).2
    have hsupp : tsupport g ⊆ K ×ˢ I := fun z hz => ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩
    have hloc : MemLp pfP (ENNReal.ofReal (3 / 2 : ℝ)) (μ.restrict (K ×ˢ I)) := by
      have h := hpfLoc K I hKc hIc hIT
      have h' : MemLp pfP (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I)) := h
      have hKI : MeasurableSet (K ×ˢ I) := hKc.measurableSet.prod hIc.measurableSet
      have hμKI : μ.restrict (K ×ˢ I) = (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I) := by
        rw [hμeq, Measure.restrict_restrict hKI,
          inter_eq_left.2 (Set.prod_mono (Set.subset_univ _) hIT)]
      rw [hμKI]
      exact h'
    exact forcePressureGradient_pairing hKc.measurableSet hIc.measurableSet hIT hloc
      (toμ hG) hgrad hg.1 hg.2.1 hsupp
  -- the residual identity for every Helmholtz cutoff
  let Φ : ℕ → Vec3 × ℝ → Vec3 := associatedPressureHelmholtzTestCutoff φP
  have hcutoff : ∀ n, ∫ z, forcedAssociatedPressureResidualIntegrand uP DuP pN r (Φ n) z ∂μ
      = 0 := by
    intro n
    let V : Vec3 × ℝ → Vec3 :=
      associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φP n)
    let ψ : Vec3 × ℝ → ℝ := associatedPressureHelmholtzScalarPotentialCutoff φP n
    let W : Vec3 × ℝ → Vec3 := associatedPressureTestGradient ψ
    have hV := associatedPressureHelmholtzCutoffCurl_mem_spaceTimeTestFunction hφP n
    have hW := associatedPressureHelmholtzScalarPotentialCutoffGradient_mem_spaceTimeTestFunction
      hφP n
    have hψ := associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction hφP n
    have hA := associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφP n
    obtain ⟨hVI, hVr⟩ := forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
      hr hV
    obtain ⟨hWI, hWr⟩ := forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
      hr hW
    -- the divergence of the solenoidal part vanishes
    have hVdiv : ∀ z, ∑ i : Fin 3, CKN.spatialPartialProd (fun q => V q i) i z = 0 := by
      intro z
      have h := associatedPressureTestCurl_divergence hA.1 z
      exact h
    -- the forced momentum identity on the solenoidal part
    have hVmom : ∫ z, associatedPressureMomentumProductIntegrand uP DuP pN V z ∂μ =
        ∫ z, ∑ i : Fin 3, fP z i * V z i ∂μ := by
      let w : ParabolicPoint → Vec3 := fun y => V (parabolicHomeomorph y)
      have hw : w ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) := by
        change (fun q : Vec3 × ℝ => w (parabolicHomeomorph.symm q)) ∈ _
        exact hV
      have hwdiv : ∀ z : ParabolicPoint,
          ∑ i : Fin 3, spatialPartial (fun y => w y i) i z = 0 := by
        intro z
        exact hVdiv (parabolicHomeomorph z)
      have hmom := hF.2.2.2.2.2.2.2.2.2.2.1 w hw hwdiv
      rw [forcedAssocProv_setIntegral_eq] at hmom
      have hpoint : ∀ z : Vec3 × ℝ,
          ((-(∑ i : Fin 3, u (parabolicHomeomorph.symm z) i *
              timePartial (fun y => w y i) (parabolicHomeomorph.symm z)))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u (parabolicHomeomorph.symm z) i * u (parabolicHomeomorph.symm z) j *
                  spatialPartial (fun y => w y i) j (parabolicHomeomorph.symm z)
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du (parabolicHomeomorph.symm z) i j *
                  spatialPartial (fun y => w y i) j (parabolicHomeomorph.symm z)
            - ∑ i : Fin 3, f (parabolicHomeomorph.symm z) i *
                w (parabolicHomeomorph.symm z) i) =
          associatedPressureMomentumProductIntegrand uP DuP pN V z -
            ∑ i : Fin 3, fP z i * V z i := by
        intro z
        rw [associatedPressureMomentumProductIntegrand_pressureless_curl hA.1 z]
        rfl
      simp only [hpoint] at hmom
      have hfV := (forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
        (toμ hf2) hV).2
      rw [integral_sub hVI hfV] at hmom
      linarith only [hmom]
    have hGV : Integrable (fun z => ∑ i : Fin 3, GP z i * V z i) μ :=
      (forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN (toμ hG) hV).2
    have hfV := (forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
      (toμ hf2) hV).2
    have hVres : ∫ z, ∑ i : Fin 3, r z i * V z i ∂μ = ∫ z, ∑ i : Fin 3, fP z i * V z i ∂μ := by
      have hsplit : (fun z => ∑ i : Fin 3, r z i * V z i) =
          fun z => (∑ i : Fin 3, fP z i * V z i) - ∑ i : Fin 3, GP z i * V z i := by
        funext z
        simp only [r, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      rw [hsplit, integral_sub hfV hGV, hGpair V hV]
      simp only [hVdiv, mul_zero, integral_zero, neg_zero, sub_zero]
      rfl
    -- the gradient part
    have hWmom : ∫ z, associatedPressureMomentumProductIntegrand uP DuP pN W z ∂μ = 0 := by
      have hgrad0 := forcedAssociatedPressureCompactGradient_momentum_zero hF hN
        (forcedAssociatedPressure_tensor_memLp_threeHalves hF) hψ.1 hψ.2.1 hψ.2.2
      have htrace (z : Vec3 × ℝ) :
          (∑ i : Fin 3, CKN.spatialPartialProd
            (fun q => CKN.spatialPartialProd ψ i q) i z) =
          rieszPressureJointLaplacian ψ z := by
        rw [rieszPressureJointLaplacian]
        apply Finset.sum_congr rfl
        intro i _
        change CKN.mixedSecond (fun x : Vec3 => ψ (x, z.2)) i i z.1 = _
        exact rieszPressure_sliceMixedSecond_eq_joint hψ.1 i i z
      have hEq (z : Vec3 × ℝ) :
          associatedPressureMomentumProductIntegrand uP DuP pN W z =
            (-(∑ i : Fin 3, uP z i * CKN.timePartialProd (CKN.spatialPartialProd ψ i) z))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  uP z i * uP z j * CKN.spatialSecondPartialProd ψ i j z
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  DuP z i j * CKN.spatialSecondPartialProd ψ i j z
              - pN z * rieszPressureJointLaplacian ψ z := by
        change associatedPressureMomentumProductIntegrand uP DuP pN
          (associatedPressureTestGradient ψ) z = _
        simp only [associatedPressureMomentumProductIntegrand, associatedPressureTestGradient]
        rw [htrace]
        rfl
      simp only [hEq]
      exact hgrad0
    have hWres : ∫ z, ∑ i : Fin 3, r z i * W z i ∂μ = 0 :=
      forcedField_pairing_scalarGradient_zero hr hrdiv hψ.1 hψ.2.1
    -- the cutoff is the sum of the two parts
    have hlin (z : Vec3 × ℝ) :
        forcedAssociatedPressureResidualIntegrand uP DuP pN r (Φ n) z =
          (associatedPressureMomentumProductIntegrand uP DuP pN V z -
            ∑ i : Fin 3, r z i * V z i) +
          (associatedPressureMomentumProductIntegrand uP DuP pN W z -
            ∑ i : Fin 3, r z i * W z i) := by
      change associatedPressureMomentumProductIntegrand uP DuP pN (fun q => V q + W q) z -
          ∑ i : Fin 3, r z i * (V z + W z) i = _
      rw [associatedPressureMomentumProductIntegrand_add hV.1 hW.1 z]
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
    rw [integral_congr_ae (Eventually.of_forall hlin)]
    have h1 : Integrable (fun z => associatedPressureMomentumProductIntegrand uP DuP pN V z -
        ∑ i : Fin 3, r z i * V z i) μ := hVI.sub hVr
    have h2 : Integrable (fun z => associatedPressureMomentumProductIntegrand uP DuP pN W z -
        ∑ i : Fin 3, r z i * W z i) μ := hWI.sub hWr
    rw [integral_add h1 h2, integral_sub hVI hVr, integral_sub hWI hWr, hVmom, hVres, hWmom,
      hWres]
    ring
  -- remove the cutoffs
  obtain ⟨Kd, hKd, -, Cd, -, hderiv⟩ :=
    associatedPressureHelmholtzTestCutoff_derivative_profile_bounds hφP
  obtain ⟨Kv, hKv, -, Cv, -, hvalue⟩ :=
    associatedPressureHelmholtzTestCutoff_value_profile_bound hφP
  have hresφ := forcedAssociatedPressureResidual_integral_eq_zero_of_cutoffs hU hDu hTensor hpN
    hr Φ (associatedPressureHelmholtzTestCutoff_mem_spaceTimeTestFunction hφP) Kd Kv hKd hKv
    Cd Cv hderiv hvalue
    (fun i z => associatedPressureHelmholtzTestCutoff_time_eventually_eq hφP i z)
    (fun i j z => associatedPressureHelmholtzTestCutoff_spatial_eventually_eq hφP i j z)
    (fun i z => associatedPressureHelmholtzTestCutoff_value_eventually_eq hφP i z) hcutoff
  -- split the residual back into the force and the force pressure
  obtain ⟨hIφ, hrφ⟩ := forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
    hr hφP
  have hfφ := (forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
    (toμ hf2) hφP).2
  have hGφ := (forcedAssociatedPressureResidualIntegrand_integrable hU hDu hTensor hpN
    (toμ hG) hφP).2
  let divφ : Vec3 × ℝ → ℝ := fun z => ∑ i : Fin 3, CKN.spatialPartialProd (fun q => φP q i) i z
  have hpfdiv : Integrable (fun z => pfP z * divφ z) μ := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) divφ := by
      refine ContDiff.sum fun i _ => ?_
      exact CKN.spatialPartial_contDiff (CKN.component_mem_spaceTimeTestFunction hφP i).1 i
    let K : Set Vec3 := Prod.fst '' tsupport φP
    let I : Set ℝ := Prod.snd '' tsupport φP
    have hKc : IsCompact K := hφP.2.1.isCompact.image continuous_fst
    have hIc : IsCompact I := hφP.2.1.isCompact.image continuous_snd
    have hIT : I ⊆ Ioo 0 T := by
      rintro t ⟨z, hz, rfl⟩
      exact (hφP.2.2 hz).2
    have hKI : MeasurableSet (K ×ˢ I) := hKc.measurableSet.prod hIc.measurableSet
    have hsupp : Function.support (fun z => pfP z * divφ z) ⊆ K ×ˢ I := by
      intro z hz
      have hdz : divφ z ≠ 0 := right_ne_zero_of_mul hz
      have hmem : z ∈ tsupport φP := by
        by_contra hnot
        apply hdz
        have hloc : φP =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hnot
        refine Finset.sum_eq_zero fun i _ => ?_
        have hi : (fun q => φP q i) =ᶠ[𝓝 z] 0 := hloc.mono fun q hq => by simp [hq]
        change fderiv ℝ (fun x : Vec3 => φP (x, z.2) i) z.1 (CKN.basisVec i) = 0
        have hslice : (fun x : Vec3 => φP (x, z.2) i) =ᶠ[𝓝 z.1] fun _ => 0 := by
          have hc : Continuous (fun x : Vec3 => (x, z.2)) := continuous_id.prodMk continuous_const
          exact hc.continuousAt.eventually hi
        rw [hslice.fderiv_eq]
        simp
      exact ⟨⟨z, hmem, rfl⟩, ⟨z, hmem, rfl⟩⟩
    have hloc : MemLp pfP (ENNReal.ofReal (3 / 2 : ℝ)) (μ.restrict (K ×ˢ I)) := by
      have h := hpfLoc K I hKc hIc hIT
      have h' : MemLp pfP (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I)) := h
      have hμKI : μ.restrict (K ×ˢ I) = (volume : Measure (Vec3 × ℝ)).restrict (K ×ˢ I) := by
        rw [hμeq, Measure.restrict_restrict hKI,
          inter_eq_left.2 (Set.prod_mono (Set.subset_univ _) hIT)]
      rw [hμKI]
      exact h'
    have hdiv3 : MemLp divφ 3 (μ.restrict (K ×ˢ I)) := by
      have hd : ∀ i : Fin 3, MemLp (fun z => CKN.spatialPartialProd (fun q => φP q i) i z) 3
          (volume : Measure (Vec3 × ℝ)) := fun i =>
        (CKN.spatialPartial_contDiff (CKN.component_mem_spaceTimeTestFunction hφP i).1
          i).continuous.memLp_of_hasCompactSupport
          (CKN.hasCompactSupport_spatialPartial
            (CKN.component_mem_spaceTimeTestFunction hφP i).2.1 i)
      have hglobal : MemLp divφ 3 (volume : Measure (Vec3 × ℝ)) := by
        refine (((hd 0).add (hd 1)).add (hd 2)).ae_eq (Eventually.of_forall fun z => ?_)
        simp [divφ, Fin.sum_univ_three]
      have hμle : μ.restrict (K ×ˢ I) ≤ (volume : Measure (Vec3 × ℝ)) := by
        refine (Measure.restrict_le_self).trans ?_
        rw [hμeq]
        exact Measure.restrict_le_self
      exact hglobal.mono_measure hμle
    have : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
      have h : Real.HolderTriple (3 / 2 : ℝ) 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
      simpa using h.ennrealOfReal
    have hon : IntegrableOn (fun z => pfP z * divφ z) (K ×ˢ I) μ := by
      have hprod : MemLp (pfP * divφ) 1 (μ.restrict (K ×ˢ I)) := hloc.mul hdiv3
      exact memLp_one_iff_integrable.mp hprod
    exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hon
  have hGpairφ := hGpair φP hφP
  -- conclude
  rw [forcedAssocProv_setIntegral_eq]
  change ∫ z, ((-(∑ i : Fin 3, uP z i * CKN.timePartialProd (fun q => φP q i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3, uP z i * uP z j * CKN.spatialPartialProd (fun q => φP q i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3, DuP z i j * CKN.spatialPartialProd (fun q => φP q i) j z
        - (pN z + pfP z) * divφ z
        - ∑ i : Fin 3, fP z i * φP z i) ∂μ = 0
  have hpoint (z : Vec3 × ℝ) :
      ((-(∑ i : Fin 3, uP z i * CKN.timePartialProd (fun q => φP q i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3, uP z i * uP z j * CKN.spatialPartialProd (fun q => φP q i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3, DuP z i j * CKN.spatialPartialProd (fun q => φP q i) j z
        - (pN z + pfP z) * divφ z
        - ∑ i : Fin 3, fP z i * φP z i) =
      forcedAssociatedPressureResidualIntegrand uP DuP pN r φP z -
        (pfP z * divφ z + ∑ i : Fin 3, GP z i * φP z i) := by
    simp only [forcedAssociatedPressureResidualIntegrand, associatedPressureMomentumProductIntegrand,
      r, divφ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpoint)]
  have hresInt : Integrable
      (fun z => forcedAssociatedPressureResidualIntegrand uP DuP pN r φP z) μ := hIφ.sub hrφ
  have hsumInt : Integrable (fun z => pfP z * divφ z + ∑ i : Fin 3, GP z i * φP z i) μ :=
    hpfdiv.add hGφ
  rw [integral_sub hresInt hsumInt, integral_add hpfdiv hGφ, hresφ]
  have hG' : ∫ z, ∑ i : Fin 3, GP z i * φP z i ∂μ = -∫ z, pfP z * divφ z ∂μ := hGpairφ
  rw [hG']
  ring

/-- The force pressure of `thm:assoc-pressure-forced`: the pressure of
`lem:force-pressure` for the force restricted to the slab `ℝ³ × (0,T)`. -/
def forcedAssociatedPressureForcePressure {T : ℝ} {f : ParabolicPoint → Vec3}
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    ParabolicPoint → ℝ :=
  forcePressure ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)).indicator f)
    (forcedAssocProv_sliceForce_locallySquareIntegrable hf)

/-- The properties of the force pressure used in `thm:assoc-pressure-forced`:
measurability and the `L²_t L⁶_x` bound on the slab, the weak gradient
`(I - ℙ) f(·, t)` on almost every slice, the local `L^{3/2}` bounds on
compact cylinders and on local boxes, and a square-integrable weak gradient
field `G` for which `f - G` is weakly divergence free on almost every
slice. -/
theorem forcedAssociatedPressureForcePressure_spec
    {T : ℝ} {f : ParabolicPoint → Vec3}
    (hT : 0 < T)
    (hf : MemLp f (2 : ℝ≥0∞)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    let pf := forcedAssociatedPressureForcePressure hf
    AEStronglyMeasurable pf
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => pf (x, t)) (ENNReal.ofReal (6 : ℝ))
          (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ⊤ ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        ∃ hft : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x : Vec3 => pf (x, t))
            (fun x i => CKN.Leray.forcePressureGradientFunction
              (fun y : Vec3 => f (y, t)) hft x i)) ∧
      (∀ (K : Set Vec3) (I : Set ℝ), IsCompact K → IsCompact I → I ⊆ Ioo 0 T →
        MemLp pf (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K I))) ∧
      (∀ Ω' J, localBox (Set.univ : Set Vec3) (Ioo 0 T) Ω' J →
        localLp (spaceTimeSet Ω' J) (3 / 2 : ℝ) pf) ∧
      ∃ G : ParabolicPoint → Vec3,
        MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
          HasWeakGradientOn (Set.univ : Set Vec3) (fun x => pf (x, t)) (fun x => G (x, t))) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
          ∀ ψ : CKN.WeakTestFunction (Set.univ : Set Vec3),
            ∫ x : Vec3, ∑ i : Fin 3, (f (x, t) - G (x, t)) i * ψ.partialDeriv i x = 0) := by
  intro pf
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let fT : ParabolicPoint → Vec3 := Q.indicator f
  let hfT : IsLocallySquareIntegrableForce fT :=
    forcedAssocProv_sliceForce_locallySquareIntegrable hf
  obtain ⟨hpfMeas, hpfL6, hpfGrad, hlocal⟩ := forcePressure_spec fT hfT T hT
  have hslice : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Vec3, fT (x, t) = f (x, t) := by
    intro t ht x
    have hzQ : ((x, t) : ParabolicPoint) ∈ Q := ⟨Set.mem_univ _, ht⟩
    exact Set.indicator_of_mem hzQ f
  have hcpt : ∀ (K : Set Vec3) (I : Set ℝ), IsCompact K → IsCompact I → I ⊆ Ioo 0 T →
      MemLp pf (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (spaceTimeSet K I)) := by
    intro K I hK hI hIT
    have hbound := hlocal K I hK.measurableSet hI.measurableSet hIT
    refine hbound.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hI.measure_lt_top.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hpfL6.ne
  refine ⟨hpfMeas, hpfL6, ?_, hcpt, ?_, ?_⟩
  · filter_upwards [hpfGrad, ae_restrict_mem measurableSet_Ioo] with t ⟨hftT, hweak⟩ ht
    have hftEq : (fun x : Vec3 => fT (x, t)) =ᵐ[volume] fun x : Vec3 => f (x, t) :=
      Eventually.of_forall fun x => hslice t ht x
    have hft : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume := hftT.ae_eq hftEq
    have hclass : realVectorL2OfCoordinateFunction (fun x : Vec3 => fT (x, t)) hftT =
        realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, t)) hft := by
      apply realVectorL2Representative_injective_ae
      filter_upwards [realVectorL2OfCoordinateFunction_rep _ hftT,
        realVectorL2OfCoordinateFunction_rep _ hft, hftEq] with x h1 h2 heq
      rw [h1, h2, heq]
    have hgradEq : forcePressureGradientFunction (fun x : Vec3 => fT (x, t)) hftT =ᵐ[volume]
        forcePressureGradientFunction (fun x : Vec3 => f (x, t)) hft := by
      change realVectorL2Representative
          (forcePressureGradientL2
            (realVectorL2OfCoordinateFunction (fun x : Vec3 => fT (x, t)) hftT)) =ᵐ[volume]
        realVectorL2Representative
          (forcePressureGradientL2
            (realVectorL2OfCoordinateFunction (fun x : Vec3 => f (x, t)) hft))
      rw [hclass]
    exact ⟨hft, hasWeakGradientOn_congr_ae_right hgradEq hweak⟩
  · intro Ω' J hbox
    rcases hbox with ⟨hΩopen, hΩc, -, hJord, hJc, hJsub⟩
    have hsub : spaceTimeSet Ω' J ⊆ spaceTimeSet (closure Ω') (closure J) :=
      Set.prod_mono subset_closure subset_closure
    have h := hcpt (closure Ω') (closure J) hΩc hJc hJsub
    exact h.mono_measure (Measure.restrict_mono_set volume hsub)
  · obtain ⟨-, hGspec⟩ := forcePressureGradientField_spec fT hfT
    obtain ⟨hG2, hGslices⟩ := hGspec T hT
    refine ⟨forcePressureGradientField fT hfT, hG2, ?_, ?_⟩
    · filter_upwards [hGslices] with t ht
      exact ht.2
    · filter_upwards [forcePressureResidual_isWeakDivFree_slices fT hfT hT,
        ae_restrict_mem measurableSet_Ioo] with t ht htI
      intro ψ
      have h := ht.2 ψ
      have hfun : (fun x : Vec3 => fT (x, t) - forcePressureGradientField fT hfT (x, t)) =
          fun x => f (x, t) - forcePressureGradientField fT hfT (x, t) := by
        funext x
        rw [hslice t htI x]
      rw [hfun] at h
      exact h

end CKN.Leray

end
