-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedAssemblySupport
public import CKN.Leray.LerayAssemblyMomentum
public import CKN.Leray.LerayAssemblyEnergy
public import CKN.Leray.LerayHopfLimitMomentum
public import CKN.Leray.StabilityMomentumSupport
public import CKN.Leray.StabilityBoundedPairing
public import CKN.Leray.StabilityFiniteSumIntegral
public import CKN.Leray.StabilityPressureFixedMultiplier

/-!
# The forced momentum limit

The passage to the limit in the forced regularized momentum identity
`eq:reg-momentum-forced` on one local box, as in the proof of
`thm:leray-forced`. The force term is the same for every regularized
solution and pairs with the bounded test, so it enters the limit linearly.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- An integrand vanishing off a compact set inside a local box has the same
integral over positive time and over the box. -/
theorem forcedAssembly_setIntegral_eq_localBox
    {Ω' : Set Vec3} {J : Set ℝ} {K : Set ParabolicPoint}
    (hKpos : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : K ⊆ spaceTimeSet Ω' J)
    (F : ParabolicPoint → ℝ) (hF : ∀ z ∉ K, F z = 0) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), F z) =
      ∫ z in spaceTimeSet Ω' J, F z := by
  have hglob : (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), F z) =
      ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hF z (fun hmem => hz (hKpos hmem))
  have hloc : (∫ z in spaceTimeSet Ω' J, F z) = ∫ z, F z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    exact hF z (fun hmem => hz (hKbox hmem))
  exact hglob.trans hloc.symm

/-- The forced regularized momentum identities pass to the forced momentum
identity (S3) of `def:sws` under the strong velocity, transport and pressure
limits and the weak gradient limit on a local box containing the support of
the test. -/
theorem forcedAssembly_momentum_limit
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
    (U Jv : ℕ → ParabolicPoint → Vec3)
    (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (Pseq : ℕ → ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (φ : Vec3 × ℝ → Vec3)
    (hφ : φ ∈ spaceTimeTestFunction (V := Vec3)
      (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : tsupport (show ParabolicPoint → Vec3 from φ) ⊆
      spaceTimeSet Ω' J)
    (hULocal : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (hJLocal : ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (huLocal : MemLp u 3 (volume.restrict (spaceTimeSet Ω' J)))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hJconv : Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hDseqLocal : ∀ n, MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet Ω' J)))
    (hDuLocal : MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hweak : ∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet Ω' J)) →
      Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
        Dseq n z i j * w z) atTop
        (nhds (∫ z in spaceTimeSet Ω' J, Du z i j * w z)))
    (hPseqLocal : ∀ n, MemLp (Pseq n) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)))
    (hpLocal : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)))
    (hPconv : Tendsto
      (fun n => eLpNorm (Pseq n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hfLocal : MemLp f 2 (volume.restrict (spaceTimeSet Ω' J)))
    (hreg : ∀ n,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              Jv n z j * U n z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Dseq n z i j * spatialPartial (fun y => φ y i) j z
          - Pseq n z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (-(∑ i, u z i * timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j *
            spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, Du z i j *
            spatialPartial (fun w => φ w i) j z
        - p z * ∑ i, spatialPartial (fun w => φ w i) i z
        - ∑ i, f z i * φ z i = 0 := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
  have hKpos : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    tsupport_parabolic_subset_spaceTimeSet hφ
  have hvan : ∀ z ∉ K, (∀ i : Fin 3, φ z i = 0) ∧
      (∀ i : Fin 3, timePartial (fun w => φ w i) z = 0) ∧
      (∀ i j : Fin 3, spatialPartial (fun w => φ w i) j z = 0) := by
    intro z hz
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport φ := by
      intro hmem
      apply hz
      change z ∈ tsupport (show ParabolicPoint → Vec3 from φ)
      rw [tsupport_parabolic_eq]
      exact hmem
    have hzcomp (i : Fin 3) :
        (z : Vec3 × ℝ) ∉ tsupport (fun w => φ w i) := by
      intro hmem
      exact hzprod ((tsupport_component_subset (V := ℝ) φ i
        (fun _ h => by rw [h]; rfl)) hmem)
    have hφz : (show ParabolicPoint → Vec3 from φ) z = 0 :=
      image_eq_zero_of_notMem_tsupport hz
    refine ⟨fun i => by rw [hφz]; rfl, fun i => ?_, fun i j => ?_⟩
    · exact timePartial_eq_zero_off_tsupport (hzcomp i)
    · exact spatialPartial_eq_zero_off_tsupport (hzcomp i) j
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hUconvThree : Tendsto (fun n => eLpNorm (U n - u) 3 μ)
      atTop (nhds 0) := hUconv
  have hJconvThree : Tendsto (fun n => eLpNorm (Jv n - u) 3 μ)
      atTop (nhds 0) := hJconv
  have hDLocal (n : ℕ) (i j : Fin 3) :
      MemLp (fun z => Dseq n z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp (hDseqLocal n)) i)) j
  have hDuLocal' (i j : Fin 3) :
      MemLp (fun z => Du z i j) 2 μ :=
    (memLp_pi_iff.mp ((memLp_pi_iff.mp hDuLocal) i)) j
  have hWeakLocal (i j : Fin 3) : Tendsto
      (fun n => ∫ z in spaceTimeSet Ω' J,
        Dseq n z i j * spatialPartial (fun w => φ w i) j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        Du z i j * spatialPartial (fun w => φ w i) j z)) :=
    hweak i j _ ((stability_spatialPartial_memLp_top φ hφ i j).mono_exponent
      (by simp))
  have hAconv := CKN.Leray.lerayHopfLimit_linearTerm_tendsto μ
    U u hULocal hUconvThree
    (fun i z => timePartial (fun w => φ w i) z)
    (fun i => stability_timePartial_memLp_top φ hφ i)
  have hBconv := CKN.Leray.lerayHopfLimit_advectiveTerm_tendsto μ
    U Jv u hULocal hJLocal huLocal hUconvThree hJconvThree
    (fun i j z => spatialPartial (fun w => φ w i) j z)
    (fun i j => stability_spatialPartial_memLp_top φ hφ i j)
  have hCseqInt (n : ℕ) (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => Dseq n z i j *
        spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num)
      (hDLocal n i j) (stability_spatialPartial_memLp_top φ hφ i j)
  have hClimInt (i j : Fin 3) : Integrable
      (fun z : ParabolicPoint => Du z i j *
        spatialPartial (fun w => φ w i) j z) μ :=
    stability_integrable_mul_bounded_test μ (by norm_num)
      (hDuLocal' i j) (stability_spatialPartial_memLp_top φ hφ i j)
  have hCconv : Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      ∑ i : Fin 3, ∑ j : Fin 3,
        Dseq n z i j * spatialPartial (fun w => φ w i) j z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        ∑ i : Fin 3, ∑ j : Fin 3,
          Du z i j * spatialPartial (fun w => φ w i) j z)) := by
    apply stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n i z => ∑ j : Fin 3,
        Dseq n z i j * spatialPartial (fun w => φ w i) j z)
      (fun i z => ∑ j : Fin 3,
        Du z i j * spatialPartial (fun w => φ w i) j z)
    · intro n i _
      exact integrable_finsetSum Finset.univ (fun j _ => hCseqInt n i j)
    · intro i _
      exact integrable_finsetSum Finset.univ (fun j _ => hClimInt i j)
    · intro i _
      apply stability_tendsto_integral_finsetSum μ Finset.univ
        (fun n j z => Dseq n z i j * spatialPartial (fun w => φ w i) j z)
        (fun j z => Du z i j * spatialPartial (fun w => φ w i) j z)
        (fun n j _ => hCseqInt n i j) (fun j _ => hClimInt i j)
        (fun j _ => hWeakLocal i j)
  have hPSeqLocal (n : ℕ) : MemLp (Pseq n) (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hPseqLocal n
  have hpLocal' : MemLp p (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hpLocal
  have hPconvInt : Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      Pseq n z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        p z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z)) := by
    have h := stability_tendsto_integral_mul_test_of_LthreeHalves μ
      Pseq p (fun z => ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z)
      hPSeqLocal (stability_testDivergence_memLp_top φ hφ)
      (by simpa only [CKN.ofReal_threeHalves] using hPconv)
    have heqN (n : ℕ) :
        (∫ z, (∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) * Pseq n z ∂μ) =
        ∫ z, Pseq n z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    have heqP :
        (∫ z, (∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z) * p z ∂μ) =
        ∫ z, p z * ∑ i : Fin 3,
          spatialPartial (fun w => φ w i) i z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    simpa only [heqN, heqP] using h
  have hφTop (i : Fin 3) : MemLp (fun z : ParabolicPoint => φ z i) ∞ μ :=
    stability_energyTest_memLp_top (fun w : Vec3 × ℝ => φ w i)
      (component_mem_spaceTimeTestFunction hφ i)
  have hFInt : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3, f z i * φ z i) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      stability_integrable_mul_bounded_test μ (by norm_num)
        ((memLp_pi_iff.mp hfLocal) i) (hφTop i))
  have hASeqInt (n : ℕ) : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3,
        U n z i * timePartial (fun w => φ w i) z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      stability_integrable_mul_bounded_test μ (by norm_num)
        ((memLp_pi_iff.mp (hULocal n)) i)
        (stability_timePartial_memLp_top φ hφ i))
  have hALimInt : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3,
        u z i * timePartial (fun w => φ w i) z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      stability_integrable_mul_bounded_test μ (by norm_num)
        ((memLp_pi_iff.mp huLocal) i)
        (stability_timePartial_memLp_top φ hφ i))
  let : ENNReal.HolderTriple (3 : ℝ≥0∞) 3 (3 / 2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple 3 3 (3 / 2) :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa only [CKN.ofReal_threeHalves, ENNReal.ofReal_ofNat] using
      hreal.ennrealOfReal
  have hOneThreeHalves : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
    rw [← CKN.ofReal_threeHalves]
    simpa using ENNReal.ofReal_le_ofReal
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have hBSeqInt (n : ℕ) : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
        U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z) μ := by
    refine integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => ?_))
    have hprod : MemLp (fun z : ParabolicPoint => U n z i * Jv n z j)
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp (hULocal n)) i).mul
        ((memLp_pi_iff.mp (hJLocal n)) j)
    exact stability_integrable_mul_bounded_test μ hOneThreeHalves hprod
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hBLimInt : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * spatialPartial (fun w => φ w i) j z) μ := by
    refine integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => ?_))
    have hprod : MemLp (fun z : ParabolicPoint => u z i * u z j)
        (3 / 2 : ℝ≥0∞) μ :=
      ((memLp_pi_iff.mp huLocal) i).mul ((memLp_pi_iff.mp huLocal) j)
    exact stability_integrable_mul_bounded_test μ hOneThreeHalves hprod
      (stability_spatialPartial_memLp_top φ hφ i j)
  have hCSeqInt (n : ℕ) : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
        Dseq n z i j * spatialPartial (fun w => φ w i) j z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hCseqInt n i j))
  have hCLimInt : Integrable
      (fun z : ParabolicPoint => ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * spatialPartial (fun w => φ w i) j z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hClimInt i j))
  have hPSeqInt (n : ℕ) : Integrable
      (fun z : ParabolicPoint => Pseq n z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z +
          ∑ i : Fin 3, f z i * φ z i) μ :=
    (stability_integrable_mul_bounded_test μ (by norm_num)
      (hPseqLocal n) (stability_testDivergence_memLp_top φ hφ)).add hFInt
  have hPLimInt : Integrable
      (fun z : ParabolicPoint => p z * ∑ i : Fin 3,
        spatialPartial (fun w => φ w i) i z +
          ∑ i : Fin 3, f z i * φ z i) μ :=
    (stability_integrable_mul_bounded_test μ (by norm_num)
      hpLocal (stability_testDivergence_memLp_top φ hφ)).add hFInt
  have hPFconv : Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
      Pseq n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z +
        ∑ i : Fin 3, f z i * φ z i) atTop
      (nhds (∫ z in spaceTimeSet Ω' J,
        p z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z +
          ∑ i : Fin 3, f z i * φ z i)) := by
    have hsplitN (n : ℕ) : (∫ z in spaceTimeSet Ω' J,
        Pseq n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z +
          ∑ i : Fin 3, f z i * φ z i) =
        (∫ z in spaceTimeSet Ω' J,
          Pseq n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) +
        ∫ z in spaceTimeSet Ω' J, ∑ i : Fin 3, f z i * φ z i :=
      integral_add (stability_integrable_mul_bounded_test μ (by norm_num)
        (hPseqLocal n) (stability_testDivergence_memLp_top φ hφ)) hFInt
    have hsplit : (∫ z in spaceTimeSet Ω' J,
        p z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z +
          ∑ i : Fin 3, f z i * φ z i) =
        (∫ z in spaceTimeSet Ω' J,
          p z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) +
        ∫ z in spaceTimeSet Ω' J, ∑ i : Fin 3, f z i * φ z i :=
      integral_add (stability_integrable_mul_bounded_test μ (by norm_num)
        hpLocal (stability_testDivergence_memLp_top φ hφ)) hFInt
    simp_rw [hsplitN, hsplit]
    exact hPconvInt.add tendsto_const_nhds
  have hregN (n : ℕ) :
      (∫ z in spaceTimeSet Ω' J,
        -(∑ i : Fin 3, U n z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Dseq n z i j * spatialPartial (fun w => φ w i) j z
          - (Pseq n z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z +
              ∑ i : Fin 3, f z i * φ z i)) = 0 := by
    have h := hreg n
    rw [forcedAssembly_setIntegral_eq_localBox hKpos hKbox _ (by
      intro z hz
      obtain ⟨h0, h1, h2⟩ := hvan z hz
      simp [h0, h1, h2])] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [] with z
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
        U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          Jv n z j * U n z i * spatialPartial (fun w => φ w i) j z := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    ring
  have hlocal := CKN.Leray.lerayAssembly_momentum_four_terms μ
    (fun n z => ∑ i : Fin 3,
      U n z i * timePartial (fun w => φ w i) z)
    (fun n z => ∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * Jv n z j * spatialPartial (fun w => φ w i) j z)
    (fun n z => ∑ i : Fin 3, ∑ j : Fin 3,
      Dseq n z i j * spatialPartial (fun w => φ w i) j z)
    (fun n z => Pseq n z * ∑ i : Fin 3,
      spatialPartial (fun w => φ w i) i z + ∑ i : Fin 3, f z i * φ z i)
    (fun z => ∑ i : Fin 3,
      u z i * timePartial (fun w => φ w i) z)
    (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      u z i * u z j * spatialPartial (fun w => φ w i) j z)
    (fun z => ∑ i : Fin 3, ∑ j : Fin 3,
      Du z i j * spatialPartial (fun w => φ w i) j z)
    (fun z => p z * ∑ i : Fin 3,
      spatialPartial (fun w => φ w i) i z + ∑ i : Fin 3, f z i * φ z i)
    hASeqInt hBSeqInt hCSeqInt hPSeqInt
    hALimInt hBLimInt hCLimInt hPLimInt
    hAconv hBconv hCconv hPFconv hregN
  rw [forcedAssembly_setIntegral_eq_localBox hKpos hKbox _ (by
    intro z hz
    obtain ⟨h0, h1, h2⟩ := hvan z hz
    simp [h0, h1, h2])]
  rw [← hlocal]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end CKN.Leray

end
