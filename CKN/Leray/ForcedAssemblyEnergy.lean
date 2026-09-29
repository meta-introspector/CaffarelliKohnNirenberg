-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedAssemblyMomentum

/-!
# The forced local energy limit

The passage to the limit in the forced regularized local energy inequality
`eq:reg-local-energy-forced` on one local box, as in the proof of
`thm:leray-forced`. The quadratic, transport and pressure fluxes converge as
in the unforced case, the force work `2(f·u)ψ` converges by strong `L²`
convergence of the velocities, and the gradient term is weakly lower
semicontinuous.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The forced regularized local energy inequalities pass to the local energy
inequality (S4) of `def:sws` with the force work term, under the strong
velocity, transport and pressure limits and the weak gradient limit on a local
box containing the support of the test. -/
theorem forcedAssembly_localEnergy_limit
    {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
    (U Jv : ℕ → ParabolicPoint → Vec3)
    (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3)
    (Pseq : ℕ → ParabolicPoint → ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (ψ : Vec3 × ℝ → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0))
    (hKbox : tsupport (show ParabolicPoint → ℝ from ψ) ⊆
      spaceTimeSet Ω' J)
    (hψpos : ∀ z, 0 ≤ ψ z)
    (hULocal : ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (hJLocal : ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet Ω' J)))
    (huLocal : MemLp u 3 (volume.restrict (spaceTimeSet Ω' J)))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0))
    (hUconvTwo : Tendsto (fun n => eLpNorm (U n - u) 2
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
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (U n) (Dseq n) z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          vec3EuclideanNorm (U n z) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3,
                spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Jv n z i +
                2 * Pseq n z * U n z i) * spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * U n z i) * ψ z) :
    2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        spatialGradientSq u Du z * ψ z ≤
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        vec3EuclideanNorm (u z) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
          + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψ i z
          + 2 * (∑ i, f z i * u z i) * ψ z := by
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
  have hKpos : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  have hvan : ∀ z ∉ K, ψ z = 0 ∧ timePartial ψ z = 0 ∧
      (∀ i : Fin 3, spatialPartial ψ i z = 0) ∧
      (∀ i : Fin 3, spatialSecondPartial ψ i i z = 0) := by
    intro z hz
    have hzprod : (z : Vec3 × ℝ) ∉ tsupport ψ := by
      intro hmem
      apply hz
      change z ∈ tsupport (show ParabolicPoint → ℝ from ψ)
      rw [tsupport_parabolic_eq]
      exact hmem
    exact ⟨image_eq_zero_of_notMem_tsupport hz,
      timePartial_eq_zero_off_tsupport hzprod,
      fun i => spatialPartial_eq_zero_off_tsupport hzprod i,
      fun i => spatialSecondPartial_eq_zero_off_tsupport hzprod i i⟩
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  let : IsFiniteMeasure μ := stability_localBox_finiteMeasure hbox
  have hψTop : MemLp (fun z : ParabolicPoint => ψ z) ∞ μ :=
    stability_energyTest_memLp_top ψ hψ
  have hψnonneg : ∀ᵐ z ∂μ, 0 ≤ ψ z :=
    Eventually.of_forall fun z => hψpos z
  have hgrad := lerayAssembly_weightedGradient_matrix μ
    Dseq Du hDseqLocal hDuLocal hweak
    (fun z => ψ z) hψTop hψnonneg
  have hP (n : ℕ) : MemLp (Pseq n) (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hPseqLocal n
  have hp : MemLp p (3 / 2 : ℝ≥0∞) μ := by
    simpa only [CKN.ofReal_threeHalves] using hpLocal
  have hPc : Tendsto
      (fun n => eLpNorm (Pseq n - p) (3 / 2 : ℝ≥0∞) μ)
      atTop (nhds 0) := by
    simpa only [CKN.ofReal_threeHalves] using hPconv
  let Tψ : ParabolicPoint → ℝ := fun z =>
    timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z
  have hTψ : MemLp Tψ ∞ μ := stability_energyLaplacian_memLp_top ψ hψ
  let φψ : Fin 3 → ParabolicPoint → ℝ := fun i z => spatialPartial ψ i z
  have hφψ (i : Fin 3) : MemLp (φψ i) ∞ μ :=
    stability_energySpatial_memLp_top ψ hψ i
  obtain ⟨hAn, hA, -⟩ :=
    lerayAssembly_quadraticTerm_tendsto μ U u hULocal huLocal hUconv Tψ hTψ
  obtain ⟨hBn, hB, -⟩ :=
    lerayAssembly_cubicTerm_tendsto μ U Jv u
      hULocal hJLocal huLocal hUconv hJconv φψ hφψ
  obtain ⟨hCn, hC, -⟩ :=
    lerayAssembly_pressureFlux_tendsto μ Pseq p U u hP hp
      hULocal huLocal hPc hUconv φψ hφψ
  have hRconv := lerayAssembly_energyRhs_tendsto μ
    U Jv u Pseq p hULocal hJLocal huLocal hP hp hUconv hJconv hPc
    Tψ hTψ φψ hφψ
  let r : ℕ → ParabolicPoint → ℝ := fun n z =>
    vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Tψ z +
      ∑ j : Fin 3,
        (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Jv n z j +
          2 * Pseq n z * U n z j) * φψ j z
  let rLim : ParabolicPoint → ℝ := fun z =>
    vec3EuclideanNorm (u z) ^ (2 : ℕ) * Tψ z +
      ∑ j : Fin 3,
        (vec3EuclideanNorm (u z) ^ (2 : ℕ) * u z j +
          2 * p z * u z j) * φψ j z
  have hrInt (n : ℕ) : Integrable (r n) μ := by
    refine (((hAn n).add (hBn n)).add ((hCn n).const_mul 2)).congr ?_
    refine Eventually.of_forall fun z => ?_
    simp only [r, Pi.add_apply]
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [Fin.sum_univ_three]
    ring
  have hrLimInt : Integrable rLim μ := by
    refine ((hA.add hB).add (hC.const_mul 2)).congr ?_
    refine Eventually.of_forall fun z => ?_
    simp only [rLim, Pi.add_apply]
    rw [gauss_vec3EuclideanNorm_sq]
    simp only [Fin.sum_univ_three]
    ring
  have hRconv' : Tendsto (fun n => ∫ z, r n z ∂μ) atTop
      (nhds (∫ z, rLim z ∂μ)) := hRconv
  let wt : Fin 3 → ParabolicPoint → ℝ := fun i z => 2 * f z i * ψ z
  have hwt (i : Fin 3) : MemLp (wt i) 2 μ := by
    have h : MemLp ((fun z : ParabolicPoint => ψ z) •
        (fun z : ParabolicPoint => f z i)) 2 μ :=
      hψTop.smul ((memLp_pi_iff.mp hfLocal) i)
    have heq : wt i = fun z => 2 * (((fun z : ParabolicPoint => ψ z) •
        (fun z : ParabolicPoint => f z i)) z) := by
      funext z
      change 2 * f z i * ψ z = 2 * (ψ z * f z i)
      ring
    rw [heq]
    exact h.const_mul 2
  have : ENNReal.HolderTriple 2 2 1 := by
    have h : Real.HolderTriple (2 : ℝ) 2 1 :=
      ⟨by norm_num, by norm_num, by norm_num⟩
    simpa using h.ennrealOfReal
  have hUi (n : ℕ) (i : Fin 3) : MemLp (fun z => U n z i) 2 μ :=
    ((memLp_pi_iff.mp (hULocal n)) i).mono_exponent (by norm_num)
  have hui (i : Fin 3) : MemLp (fun z => u z i) 2 μ :=
    ((memLp_pi_iff.mp huLocal) i).mono_exponent (by norm_num)
  have hUiconv (i : Fin 3) : Tendsto (fun n =>
      eLpNorm ((fun z => U n z i) - fun z => u z i) 2 μ) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hUconvTwo (Eventually.of_forall fun _ => bot_le)
      (Eventually.of_forall fun n => ?_)
    exact eLpNorm_mono ((hUi n i).aestronglyMeasurable.sub
      (hui i).aestronglyMeasurable)
      (fun z => norm_le_pi_norm ((U n - u) z) i)
  have hWInt (n : ℕ) : Integrable
      (fun z => ∑ i : Fin 3, U n z i * wt i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (hUi n i).integrable_mul (hwt i))
  have hWLimInt : Integrable
      (fun z => ∑ i : Fin 3, u z i * wt i z) μ :=
    integrable_finsetSum Finset.univ (fun i _ =>
      (hui i).integrable_mul (hwt i))
  have hWconv : Tendsto (fun n => ∫ z, ∑ i : Fin 3, U n z i * wt i z ∂μ)
      atTop (nhds (∫ z, ∑ i : Fin 3, u z i * wt i z ∂μ)) := by
    apply stability_tendsto_integral_finsetSum μ Finset.univ
      (fun n i z => U n z i * wt i z) (fun i z => u z i * wt i z)
    · intro n i _
      exact (hUi n i).integrable_mul (hwt i)
    · intro i _
      exact (hui i).integrable_mul (hwt i)
    · intro i _
      exact forcedAssembly_pairing_tendsto_of_strong_two μ
        (fun n z => U n z i) (fun z => u z i) (wt i) (fun n => hUi n i)
        (hwt i) (hUiconv i)
  have hvanInt (F : ParabolicPoint → ℝ)
      (hF : ∀ z, ψ z = 0 → timePartial ψ z = 0 →
        (∀ i : Fin 3, spatialPartial ψ i z = 0) →
        (∀ i : Fin 3, spatialSecondPartial ψ i i z = 0) → F z = 0) :
      (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0), F z) =
        ∫ z in spaceTimeSet Ω' J, F z :=
    forcedAssembly_setIntegral_eq_localBox hKpos hKbox F (fun z hz =>
      hF z (hvan z hz).1 (hvan z hz).2.1 (hvan z hz).2.2.1 (hvan z hz).2.2.2)
  let A (n : ℕ) : ℝ :=
    ∫ z in spaceTimeSet Ω' J, spatialGradientSq (U n) (Dseq n) z * ψ z
  let B : ℝ :=
    ∫ z in spaceTimeSet Ω' J, spatialGradientSq u Du z * ψ z
  let C (n : ℕ) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ z in spaceTimeSet Ω' J, Dseq n z i j * Du z i j * ψ z
  let R (n : ℕ) : ℝ := ∫ z, r n z ∂μ
  let W (n : ℕ) : ℝ := ∫ z, ∑ i : Fin 3, U n z i * wt i z ∂μ
  let S : ℝ := ∫ z, rLim z ∂μ
  let W₀ : ℝ := ∫ z, ∑ i : Fin 3, u z i * wt i z ∂μ
  have hCconv : Tendsto C atTop (nhds B) := hgrad.1
  have hpolar : ∀ n, 2 * C n ≤ A n + B := hgrad.2
  have hineq (n : ℕ) : 2 * A n ≤ R n + W n := by
    have h := hreg n
    rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox
      (U n) (Dseq n)] at h
    rw [hvanInt _ (fun z h0 h1 h2 h3 => by simp [h0, h1, h2, h3])] at h
    have heq : (∫ z in spaceTimeSet Ω' J,
        vec3EuclideanNorm (U n z) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3,
              spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            (vec3EuclideanNorm (U n z) ^ (2 : ℕ) * Jv n z i +
              2 * Pseq n z * U n z i) * spatialPartial ψ i z +
          2 * (∑ i : Fin 3, f z i * U n z i) * ψ z) =
        ∫ z, r n z + ∑ i : Fin 3, U n z i * wt i z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [r, wt, Tψ, φψ, Fin.sum_univ_three]
      ring
    rw [heq, integral_add (hrInt n) (hWInt n)] at h
    exact h
  have hpoint (n : ℕ) : 4 * C n ≤ R n + W n + 2 * B := by
    linarith only [hpolar n, hineq n]
  have hlimit : 4 * B ≤ S + W₀ + 2 * B :=
    le_of_tendsto_of_tendsto' (hCconv.const_mul 4)
      ((hRconv'.add hWconv).add_const (2 * B)) hpoint
  have hlocal : 2 * B ≤ S + W₀ := by
    linarith only [hlimit]
  rw [stability_energy_gradient_integral_eq_localBox ψ hψ hKbox u Du]
  rw [hvanInt _ (fun z h0 h1 h2 h3 => by simp [h0, h1, h2, h3])]
  have heq : (∫ z in spaceTimeSet Ω' J,
      vec3EuclideanNorm (u z) ^ 2 *
          (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
        + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψ i z
        + 2 * (∑ i, f z i * u z i) * ψ z) =
      ∫ z, rLim z + ∑ i : Fin 3, u z i * wt i z ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [rLim, wt, Tψ, φψ, Fin.sum_univ_three]
    ring
  rw [heq, integral_add hrLimInt hWLimInt]
  exact hlocal

end CKN.Leray

end
