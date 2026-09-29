-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRealNorms
public import CKN.Leray.ForcedRegularisedPressure
public import CKN.Leray.Support.CarlemanCoreMixed

/-!
# Real-radius Helmholtz cutoff limits

Compact time support and radial bounds give the three real-parameter limits
in `lem:helmholtz-test`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section
namespace CKN.Leray

private theorem hp_realVectorComponent_spatialPartial_zero_of_time_zero
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A) (k : Fin 3)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, A (x, t) = 0)
    {z : Vec3 × ℝ} (ht : z.2 ∉ K) (j : Fin 3) :
    CKN.spatialPartialProd (fun q => A q k) j z = 0 := by
  let f : Vec3 × ℝ → ℝ := fun q => A q k
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 z :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  have hlocal : f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    exact congrArg (fun v : Vec3 => v k) (hzero q.2 hq.2 q.1)
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) z :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ k).comp hA
  have hdiff : DifferentiableAt ℝ f z := (hf.differentiable (by simp)) z
  change CKN.spatialPartial f j z = 0
  rw [CKN.spatialPartial_eq_product_fderiv hdiff j, hfd.fderiv]
  simp

private theorem hp_timePartial_zero_of_time_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    {z : Vec3 × ℝ} (ht : z.2 ∉ K) :
    CKN.timePartial f z = 0 := by
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 z :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  have hlocal : f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    exact hzero q.2 hq.2 q.1
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) z :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hdiff : DifferentiableAt ℝ f z := (hf.differentiable (by simp)) z
  change CKN.timePartial f z = 0
  rw [CKN.timePartial_eq_product_fderiv hdiff, hfd.fderiv]
  simp

private theorem hp_curl_zero_of_time_zero
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, A (x, t) = 0)
    (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestCurl A (x, t) i = 0 := by
  have hpart (k j : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) j (x, t) = 0 := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
      (contDiff_apply ℝ ℝ k).comp hA
    exact hp_realVectorComponent_spatialPartial_zero_of_time_zero
      A hA k hK hzero ht j
  fin_cases i <;>
    simp [associatedPressureTestCurl_zero, associatedPressureTestCurl_one,
      associatedPressureTestCurl_two, hpart]

private theorem hp_curl_timePartial_zero_of_time_zero
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, A (x, t) = 0)
    (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestTimePartial
      (fun q => associatedPressureTestCurl A q i) (x, t) = 0 := by
  have hcurl : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestCurl A q i) :=
    (contDiff_apply ℝ ℝ i).comp (associatedPressureTestCurl_contDiff hA)
  have hzeroCurl (s : ℝ) (hs : s ∉ K) (y : Vec3) :
      associatedPressureTestCurl A (y, s) i = 0 :=
    hp_curl_zero_of_time_zero A hA hK hzero s hs y i
  exact hp_timePartial_zero_of_time_zero hcurl hK hzeroCurl ht

private theorem hp_curl_spatialPartial_zero_of_time_zero
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, A (x, t) = 0)
    (t : ℝ) (ht : t ∉ K) (x : Vec3) (i j : Fin 3) :
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl A q i) j (x, t) = 0 := by
  let f : Vec3 × ℝ → ℝ := fun q => associatedPressureTestCurl A q i
  have hcurl : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestCurl A q i) :=
    (contDiff_apply ℝ ℝ i).comp (associatedPressureTestCurl_contDiff hA)
  have hzeroCurl (s : ℝ) (hs : s ∉ K) (y : Vec3) :
      associatedPressureTestCurl A (y, s) i = 0 :=
    hp_curl_zero_of_time_zero A hA hK hzero s hs y i
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 (x, t) :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  have hlocal : f =ᶠ[𝓝 (x, t)] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    exact hzeroCurl q.2 hq.2 q.1
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) (x, t) :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hcurl
  have hdiff : DifferentiableAt ℝ f (x, t) := (hf.differentiable (by simp)) _
  change CKN.spatialPartial f j (x, t) = 0
  rw [CKN.spatialPartial_eq_product_fderiv hdiff j, hfd.fderiv]
  simp

/-- The real-radius time derivative error is integrable in the time-slice
spatial `L²` norm, with an explicit `R⁻³ᐟ²` bound. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_L1tL2x_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (i : Fin 3),
      ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))) *
        volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hslice⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_timePartial_component_eLpNorm_error_le hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro R hR i
  let b : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal
    (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))
  let A := associatedPressureHelmholtzVectorPotential φ
  let Acut := associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcut : ContDiff ℝ (⊤ : ℕ∞) Acut :=
    (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
      hφ R hR).1
  have hzeroA (t : ℝ) (ht : t ∉ K) (x : Vec3) : A (x, t) = 0 := hzero t ht x |>.2
  have hzeroAcut (t : ℝ) (ht : t ∉ K) (x : Vec3) : Acut (x, t) = 0 := by
    change rieszPressurePotentialCutoffReal R hR x •
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0
    rw [(hzero t ht x).2]
    simp
  have hpoint (t : ℝ) :
      eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl Acut q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl A q i) (x, t))
        2 (volume : Measure Vec3) ≤ K.indicator (fun _ => b) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      simpa [b, Acut, A] using hslice R hR t i
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_curl_timePartial_zero_of_time_zero
        Acut hAcut hK.isClosed hzeroAcut t ht x i
      have hbase := fun x => hp_curl_timePartial_zero_of_time_zero
        A hA hK.isClosed hzeroA t ht x i
      have hz : (fun x : Vec3 =>
          associatedPressureTestTimePartial
            (fun q => associatedPressureTestCurl Acut q i) (x, t) -
          associatedPressureTestTimePartial
            (fun q => associatedPressureTestCurl A q i) (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNorm_zero]
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b) t ∂(volume : Measure ℝ) := lintegral_mono hpoint
    _ = b * volume K := lintegral_indicator_const hK.measurableSet b

/-- The time-integrated squared spatial `L²` norm of each real-radius curl
error derivative has the `R⁻³ᐟ²` tail bound. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L2tx_sq_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R)
      (i j : Fin 3),
      ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))) ^ (2 : ℝ) *
        volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hslice⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_spatialPartial_component_eLpNorm_error_le hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro R hR i j
  let b : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal
    (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))
  let A := associatedPressureHelmholtzVectorPotential φ
  let Acut := associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcut : ContDiff ℝ (⊤ : ℕ∞) Acut :=
    (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
      hφ R hR).1
  have hzeroA (t : ℝ) (ht : t ∉ K) (x : Vec3) : A (x, t) = 0 := hzero t ht x |>.2
  have hzeroAcut (t : ℝ) (ht : t ∉ K) (x : Vec3) : Acut (x, t) = 0 := by
    change rieszPressurePotentialCutoffReal R hR x •
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0
    rw [(hzero t ht x).2]
    simp
  have hpoint (t : ℝ) :
      (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl A q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ≤
      K.indicator (fun _ => b ^ (2 : ℝ)) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have hle := hslice R hR t i j
      dsimp [b]
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_curl_spatialPartial_zero_of_time_zero
        Acut hAcut hK.isClosed hzeroAcut t ht x i j
      have hbase := fun x => hp_curl_spatialPartial_zero_of_time_zero
        A hA hK.isClosed hzeroA t ht x i j
      have hz : (fun x : Vec3 =>
          CKN.spatialPartialProd (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
          CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNorm_zero]
      simp
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b ^ (2 : ℝ)) t ∂(volume : Measure ℝ) :=
      lintegral_mono hpoint
    _ = b ^ (2 : ℝ) * volume K := lintegral_indicator_const hK.measurableSet _

/-- The time-integrated spatial essential-sup norm of each real-radius curl
gradient error has a fourth-order decay bound. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L1tLinf_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R)
      (i j : Fin 3),
      ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ) ≤
      ENNReal.ofReal (C * (1 + R / 2) ^ (-(4 : ℝ))) * volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_spatialPartial_error_profile hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro R hR i j
  let ρ := R / 2
  let b : ℝ≥0∞ := ENNReal.ofReal (C * (1 + ρ) ^ (-(4 : ℝ)))
  let A := associatedPressureHelmholtzVectorPotential φ
  let Acut := associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcut : ContDiff ℝ (⊤ : ℕ∞) Acut :=
    (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
      hφ R hR).1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hpointwise (t : ℝ) (x : Vec3) :
      |CKN.spatialPartialProd (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t)| ≤
      C * (1 + ρ) ^ (-(4 : ℝ)) := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile R hR (x, t) i j
      have hxy : 1 + ρ ≤ 1 + ‖x‖ := by linarith only [hx]
      have hdecay : (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ (1 + ρ) ^ (-(4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hxy (by norm_num)
      exact herr.trans (mul_le_mul_of_nonneg_left hdecay hC)
    · have hnormlt : ‖x‖ < ρ := lt_of_not_ge hx
      have hEupper := vec3EuclideanNorm_le_sqrt_three_mul_norm x
      have hsqrt3 : Real.sqrt 3 ≤ 2 := by
        nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      have hE : vec3EuclideanNorm x < R := by
        calc
          vec3EuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := hEupper
          _ ≤ 2 * ‖x‖ := mul_le_mul_of_nonneg_right hsqrt3 (norm_nonneg x)
          _ < 2 * ρ := by nlinarith only [hnormlt]
          _ = R := by dsimp [ρ]; ring
      have hxBall : x ∈ CKN.euclideanBall 0 R := by
        apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).2
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using hE
      have hxClosed : x ∈ CKN.euclideanClosedBall 0 R := by
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hRpos.le).2
        exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hRpos).1 hxBall |>.le
      have heq := associatedPressureHelmholtzCutoffCurlReal_spatialPartial_eq_of_inner
        A hA R hR (x, t) i j hxBall hxClosed
      have heq' : CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl Acut q i) j (x, t) =
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl A q i) j (x, t) := by
        change CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (fun w => rieszPressurePotentialCutoffReal R hR w.1 •
                associatedPressureHelmholtzVectorPotential φ w) q i) j (x, t) = _
        exact heq
      have hz : CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t) = 0 := by
        exact sub_eq_zero.mpr heq'
      rw [hz]
      simpa using mul_nonneg hC
        (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ρ) (-(4 : ℝ)))
  have hpoint (t : ℝ) :
      eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t))
        (volume : Measure Vec3) ≤ K.indicator (fun _ => b) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have hbound (x : Vec3) :
          ‖CKN.spatialPartialProd (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
            CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t)‖ ≤
          C * (1 + ρ) ^ (-(4 : ℝ)) := by
        rw [Real.norm_eq_abs]
        exact hpointwise t x
      have hsup := eLpNormEssSup_le_of_ae_bound (μ := volume)
        (Filter.Eventually.of_forall hbound)
      simpa [b, ρ] using hsup
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_curl_spatialPartial_zero_of_time_zero
        Acut hAcut hK.isClosed
        (fun s hs y => by simp [Acut, associatedPressureHelmholtzCutoffVectorPotentialReal,
          hzero s hs y]) t ht x i j
      have hbase := fun x => hp_curl_spatialPartial_zero_of_time_zero
        A hA hK.isClosed (fun s hs y => (hzero s hs y).2) t ht x i j
      have hz : (fun x : Vec3 =>
          CKN.spatialPartialProd (fun q => associatedPressureTestCurl Acut q i) j (x, t) -
          CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNormEssSup_zero]
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b) t ∂(volume : Measure ℝ) := lintegral_mono hpoint
    _ = b * volume K := lintegral_indicator_const hK.measurableSet b

private theorem hp_realHalf_tendsto_atTop :
    Tendsto (fun R : ℝ => R / 2) atTop atTop :=
  Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id

private theorem hp_realHalf_rpow_three_halves_tendsto_zero :
    Tendsto (fun R : ℝ => (R / 2) ^ (-(3 / 2 : ℝ))) atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
    hp_realHalf_tendsto_atTop

private theorem hp_realHalf_rpow_four_tendsto_zero :
    Tendsto (fun R : ℝ => (1 + R / 2) ^ (-(4 : ℝ))) atTop (nhds 0) := by
  have hbase : Tendsto (fun R : ℝ => 1 + R / 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop 1 hp_realHalf_tendsto_atTop
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hbase

private theorem hp_real_tendsto_ENNReal_zero_of_le
    {f g : ℝ → ℝ≥0∞} (hg : Tendsto g atTop (nhds 0))
    (hfg : ∀ᶠ R : ℝ in atTop, f R ≤ g R) :
    Tendsto f atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Filter.Eventually.of_forall fun _ => bot_le) hfg

/-- Each component of the real-radius time derivative cutoff error converges
to zero in the time-integrated spatial `L²` norm. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_L1tL2x_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ i : Fin 3,
      Tendsto (fun R : ℝ => ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_timePartial_L1tL2x_bound hφ
  refine ⟨K, hK, C, hC, ?_⟩
  have hreal : Tendsto (fun R : ℝ => associatedPressureHelmholtzTailL2Constant *
      (R / 2) ^ (-(3 / 2 : ℝ))) atTop (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul hp_realHalf_rpow_three_halves_tendsto_zero)
  have htail := ENNReal.tendsto_ofReal hreal
  have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hmajor : Tendsto (fun R : ℝ =>
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))) *
        volume K) atTop (nhds 0) := by
    have hscaled := ENNReal.Tendsto.const_mul htail
      (a := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
    have hscaledMeasure := ENNReal.Tendsto.mul_const hscaled
      (b := volume K) (Or.inr hfinite)
    simpa using hscaledMeasure
  intro i
  apply hp_real_tendsto_ENNReal_zero_of_le hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have htotal := associatedPressureHelmholtzCutoffVectorPotentialRealTotal_eq φ R hR
  simpa [htotal] using hbound R hR i

/-- Each spatial derivative of the real-radius cutoff error converges to zero
in space-time `L²`. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L2tx_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun R : ℝ => ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ))
        atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L2tx_sq_bound hφ
  refine ⟨K, hK, C, hC, ?_⟩
  have hreal : Tendsto (fun R : ℝ => associatedPressureHelmholtzTailL2Constant *
      (R / 2) ^ (-(3 / 2 : ℝ))) atTop (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul hp_realHalf_rpow_three_halves_tendsto_zero)
  have htail := ENNReal.tendsto_ofReal hreal
  have hscaled := ENNReal.Tendsto.const_mul htail
    (a := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
  have hscaled' : Tendsto (fun R : ℝ => ENNReal.ofReal C * ENNReal.ofReal
      (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ))))
      atTop (nhds 0) := by simpa using hscaled
  have hscaledSq := (ENNReal.continuous_pow 2).tendsto 0 |>.comp hscaled'
  have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hmajor : Tendsto (fun R : ℝ =>
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * (R / 2) ^ (-(3 / 2 : ℝ)))) ^
        (2 : ℝ) * volume K) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hscaledSq
      (b := volume K) (Or.inr hfinite)
  intro i j
  apply hp_real_tendsto_ENNReal_zero_of_le hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have htotal := associatedPressureHelmholtzCutoffVectorPotentialRealTotal_eq φ R hR
  simpa [htotal] using hbound R hR i j

/-- Each spatial derivative of the real-radius cutoff error converges to zero
in the time-integrated spatial essential-sup norm. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L1tLinf_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun R : ℝ => ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialRealTotal φ R) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_spatialPartial_L1tLinf_bound hφ
  refine ⟨K, hK, C, hC, ?_⟩
  have hreal : Tendsto (fun R : ℝ => C * (1 + R / 2) ^ (-(4 : ℝ)))
      atTop (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul hp_realHalf_rpow_four_tendsto_zero)
  have htail := ENNReal.tendsto_ofReal hreal
  have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hmajor : Tendsto (fun R : ℝ =>
      ENNReal.ofReal (C * (1 + R / 2) ^ (-(4 : ℝ))) * volume K)
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const htail
      (b := volume K) (Or.inr hfinite)
  intro i j
  apply hp_real_tendsto_ENNReal_zero_of_le hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have htotal := associatedPressureHelmholtzCutoffVectorPotentialRealTotal_eq φ R hR
  simpa [htotal] using hbound R hR i j

end CKN.Leray

end
