-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRateNorms
public import CKN.Leray.ForcedRegularisedPressure
public import CKN.Leray.Support.CarlemanCoreMixed

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section
namespace CKN.Leray

private theorem hp_spatialPartial_zero_of_time_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x, f (x, t) = 0)
    {z : Vec3 × ℝ} (ht : z.2 ∉ K) (j : Fin 3) :
    CKN.spatialPartialProd f j z = 0 := by
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
  change CKN.spatialPartial f j z = 0
  rw [CKN.spatialPartial_eq_product_fderiv hdiff j, hfd.fderiv]
  simp

private theorem hp_potential_cutoffCurl_zero_off_time
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0)
    (n : ℕ) (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestCurl
      (associatedPressureHelmholtzCutoffVectorPotential φ n) (x, t) i = 0 := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotential φ n) :=
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1
  have hzeroCut (t : ℝ) (ht : t ∉ K) (x : Vec3) :
      associatedPressureHelmholtzCutoffVectorPotential φ n (x, t) = 0 := by
    simp [associatedPressureHelmholtzCutoffVectorPotential, hzero t ht x]
  have hpart (k j : Fin 3) :
      associatedPressureTestPartial
        (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) j
        (x, t) = 0 := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) :=
      (contDiff_apply ℝ ℝ k).comp hA
    exact hp_spatialPartial_zero_of_time_zero hcomp hK
      (fun s hs y => congrArg (fun v : Vec3 => v k) (hzeroCut s hs y)) ht j
  fin_cases i <;>
    simp [associatedPressureTestCurl_zero, associatedPressureTestCurl_one,
      associatedPressureTestCurl_two, hpart]

private theorem hp_potentialCurl_zero_off_time
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0)
    (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestCurl
      (associatedPressureHelmholtzVectorPotential φ) (x, t) i = 0 := by
  have hA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzVectorPotential φ) :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hpart (k j : Fin 3) :
      associatedPressureTestPartial
        (fun q => associatedPressureHelmholtzVectorPotential φ q k) j (x, t) = 0 := by
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun q => associatedPressureHelmholtzVectorPotential φ q k) :=
      (contDiff_apply ℝ ℝ k).comp hA
    exact hp_spatialPartial_zero_of_time_zero hcomp hK
      (fun s hs y => congrArg (fun v : Vec3 => v k) (hzero s hs y)) ht j
  fin_cases i <;>
    simp [associatedPressureTestCurl_zero, associatedPressureTestCurl_one,
      associatedPressureTestCurl_two, hpart]

private theorem hp_potentialCurl_timePartial_zero_off_time
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0)
    (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestTimePartial
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) q i) (x, t) = 0 := by
  have hcurl : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) q i) :=
    (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hz := hp_potentialCurl_zero_off_time hφ hK hzero t ht
  have hzero' (s : ℝ) (hs : s ∉ K) (y : Vec3) :
      associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) (y, s) i = 0 :=
    hp_potentialCurl_zero_off_time hφ hK hzero s hs y i
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 (x, t) :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  let f : Vec3 × ℝ → ℝ := fun q => associatedPressureTestCurl
    (associatedPressureHelmholtzVectorPotential φ) q i
  have hlocal : f =ᶠ[𝓝 (x, t)] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    dsimp [f]
    exact hzero' q.2 hq.2 q.1
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) (x, t) :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hdiff : DifferentiableAt ℝ f (x, t) := by
    simpa [f] using (hcurl.differentiable (by simp)) (x, t)
  change CKN.timePartial f (x, t) = 0
  rw [CKN.timePartial_eq_product_fderiv hdiff, hfd.fderiv]
  simp

private theorem hp_cutoffCurl_timePartial_zero_off_time
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0)
    (n : ℕ) (t : ℝ) (ht : t ∉ K) (x : Vec3) (i : Fin 3) :
    associatedPressureTestTimePartial
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) = 0 := by
  have hcurl : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) :=
    (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1)
  have hzero' (s : ℝ) (hs : s ∉ K) (y : Vec3) :
      associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) (y, s) i = 0 :=
    hp_potential_cutoffCurl_zero_off_time hφ hK hzero n s hs y i
  have hO : IsOpen ((Set.univ : Set Vec3) ×ˢ Kᶜ) :=
    isOpen_univ.prod hK.isOpen_compl
  have hnear : ((Set.univ : Set Vec3) ×ˢ Kᶜ) ∈ 𝓝 (x, t) :=
    hO.mem_nhds ⟨Set.mem_univ _, ht⟩
  let f : Vec3 × ℝ → ℝ := fun q => associatedPressureTestCurl
    (associatedPressureHelmholtzCutoffVectorPotential φ n) q i
  have hlocal : f =ᶠ[𝓝 (x, t)] fun _ => (0 : ℝ) := by
    filter_upwards [hnear] with q hq
    dsimp [f]
    exact hzero' q.2 hq.2 q.1
  have hfd : HasFDerivAt f (0 : (Vec3 × ℝ) →L[ℝ] ℝ) (x, t) :=
    hasFDerivAt_zero_of_eventually_const 0 hlocal
  have hdiff : DifferentiableAt ℝ f (x, t) := by
    simpa [f] using (hcurl.differentiable (by simp)) (x, t)
  change CKN.timePartial f (x, t) = 0
  rw [CKN.timePartial_eq_product_fderiv hdiff, hfd.fderiv]
  simp

private theorem hp_cutoffCurl_spatialPartial_zero_off_time
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    {K : Set ℝ} (hK : IsClosed K)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureHelmholtzVectorPotential φ (x, t) = 0)
    (n : ℕ) (t : ℝ) (ht : t ∉ K) (x : Vec3) (i j : Fin 3) :
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) = 0 := by
  have hcurl : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) :=
    (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1)
  have hzero' (s : ℝ) (hs : s ∉ K) (y : Vec3) :
      associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) (y, s) i = 0 :=
    hp_potential_cutoffCurl_zero_off_time hφ hK hzero n s hs y i
  exact hp_spatialPartial_zero_of_time_zero hcurl hK hzero' ht j

private theorem hp_cutoffCurl_spatialPartial_eq_inner
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3)
    (hxBall : z.1 ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n))
    (hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n)) :
    CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j z =
      CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) q i) j z := by
  let A := associatedPressureHelmholtzVectorPotential φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotential φ n) :=
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1
  have hdouble (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    have hcutcomp : ContDiff ℝ (⊤ : ℕ∞)
        (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
      rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
    have hcutId := rieszPressure_sliceMixedSecond_eq_joint hcutcomp j l z
    have hEq := associatedPressurePotentialCutoff_hessian_eq_of_inner
      (hAcomp k) j l n z hxBall hxClosed
    have hAId := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    have hformula :
        CKN.spatialSecondPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l j z =
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) j l z := by
      change CKN.mixedSecond
        (fun x : Vec3 =>
          (rieszPressurePotentialCutoff n x • A (x, z.2)) k)
        j l z.1 = _
      exact hcutId
    rw [hformula]
    have hbase : CKN.spatialSecondPartialProd (fun q => A q k) l j z =
        rieszPressureJointHessian (fun q => A q k) j l z := by
      change CKN.mixedSecond (fun x : Vec3 => A (x, z.2) k) j l z.1 = _
      exact hAId
    rw [hbase]
    exact hEq
  have hdouble' (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => rieszPressurePotentialCutoff n q.1 * A q k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z = _
    exact hdouble k l
  have hcutCurl : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n)) :=
    associatedPressureTestCurl_contDiff hcutA
  have hbaseCurl : ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestCurl A) :=
    associatedPressureTestCurl_contDiff hA
  have hpCurlFormula {B : Vec3 × ℝ → Vec3}
      (hB : ContDiff ℝ (⊤ : ℕ∞) B) (a b : Fin 3) (q : Vec3 × ℝ) :
      CKN.spatialPartialProd (fun y => associatedPressureTestCurl B y a) b q =
        match a with
        | 0 => CKN.spatialSecondPartialProd (fun y => B y 2) 1 b q -
            CKN.spatialSecondPartialProd (fun y => B y 1) 2 b q
        | 1 => CKN.spatialSecondPartialProd (fun y => B y 0) 2 b q -
            CKN.spatialSecondPartialProd (fun y => B y 2) 0 b q
        | 2 => CKN.spatialSecondPartialProd (fun y => B y 1) 0 b q -
            CKN.spatialSecondPartialProd (fun y => B y 0) 1 b q := by
    have hBcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y => B y k) :=
      (contDiff_apply ℝ ℝ k).comp hB
    have hpart (k l : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => associatedPressureTestPartial (fun w => B w k) l y) := by
      have h := CKN.spatialPartial_contDiff (hBcomp k) l
      convert h using 1
      funext y
      exact associatedPressureTestPartial_eq_spatialPartial (fun w => B w k) l y
    fin_cases a
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 2) 1 y -
          associatedPressureTestPartial (fun w => B w 1) 2 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 2 1).differentiable (by simp) q)
        ((hpart 1 2).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 0) 2 y -
          associatedPressureTestPartial (fun w => B w 2) 0 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 0 2).differentiable (by simp) q)
        ((hpart 2 0).differentiable (by simp) q) b]
      rfl
    · change CKN.spatialPartial
        (fun y => associatedPressureTestPartial (fun w => B w 1) 0 y -
          associatedPressureTestPartial (fun w => B w 0) 1 y) b q = _
      rw [CKN.spatialPartial_sub_at
        ((hpart 1 0).differentiable (by simp) q)
        ((hpart 0 1).differentiable (by simp) q) b]
      rfl
  rw [hpCurlFormula hcutA i j z, hpCurlFormula hA i j z]
  fin_cases i
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 2) 1 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 1) 2 j z =
      CKN.spatialSecondPartialProd (fun q => A q 2) 1 j z -
        CKN.spatialSecondPartialProd (fun q => A q 1) 2 j z
    simp [hdouble']
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 0) 2 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 2) 0 j z =
      CKN.spatialSecondPartialProd (fun q => A q 0) 2 j z -
        CKN.spatialSecondPartialProd (fun q => A q 2) 0 j z
    simp [hdouble']
  · change CKN.spatialSecondPartialProd
        (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 1) 0 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 0) 1 j z =
      CKN.spatialSecondPartialProd (fun q => A q 1) 0 j z -
        CKN.spatialSecondPartialProd (fun q => A q 0) 1 j z
    simp [hdouble']

/-- The time derivative error is integrable in the time-slice spatial L² norm,
with an explicit R^(-3/2) bound. Both fields vanish outside the compact time
support of φ. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_L1tL2x_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (n : ℕ) (i : Fin 3),
      ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant *
          (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))) * volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hslice⟩ :=
    associatedPressureHelmholtzCutoffCurl_timePartial_component_eLpNorm_error_le hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro n i
  let b : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal
    (associatedPressureHelmholtzTailL2Constant *
      (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))
  have hpoint (t : ℝ) :
      eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ≤ K.indicator (fun _ => b) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      simpa [b] using hslice n t i
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_cutoffCurl_timePartial_zero_off_time
        hφ hK.isClosed (fun s hs y => (hzero s hs y).2) n t ht x i
      have hbase := fun x => hp_potentialCurl_timePartial_zero_off_time
        hφ hK.isClosed (fun s hs y => (hzero s hs y).2) t ht x i
      have hz : (fun x : Vec3 =>
          associatedPressureTestTimePartial
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) -
          associatedPressureTestTimePartial
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzVectorPotential φ) q i) (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNorm_zero]
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b) t ∂(volume : Measure ℝ) :=
      lintegral_mono hpoint
    _ = b * volume K := lintegral_indicator_const hK.measurableSet b

/-- The squared time-slice spatial L² norm of each gradient error is
integrable in time, with the R^(-3/2) spatial tail rate. Tonelli identifies
this integral with the space-time L² norm squared. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_L2tx_sq_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (n : ℕ) (i j : Fin 3),
      ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ) ≤
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant *
          (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))) ^ (2 : ℝ) *
        volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hslice⟩ :=
    associatedPressureHelmholtzCutoffCurl_spatialPartial_component_eLpNorm_error_le hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro n i j
  let b : ℝ≥0∞ := ENNReal.ofReal C * ENNReal.ofReal
    (associatedPressureHelmholtzTailL2Constant *
      (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))
  have hpoint (t : ℝ) :
      (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ≤
      K.indicator (fun _ => b ^ (2 : ℝ)) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have hle := hslice n t i j
      dsimp [b]
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_cutoffCurl_spatialPartial_zero_off_time
        hφ hK.isClosed (fun s hs y => (hzero s hs y).2) n t ht x i j
      have hbaseCurl : ContDiff ℝ (⊤ : ℕ∞)
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) :=
        (contDiff_apply ℝ ℝ i).comp
          (associatedPressureTestCurl_contDiff
            (associatedPressureHelmholtzVectorPotential_contDiff hφ))
      have hbase (x : Vec3) :
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t) = 0 :=
        hp_spatialPartial_zero_of_time_zero hbaseCurl hK.isClosed
          (fun s hs y => hp_potentialCurl_zero_off_time hφ hK.isClosed
            (fun r hr w => (hzero r hr w).2) s hs y i) (z := (x, t)) ht j
      have hz : (fun x : Vec3 =>
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNorm_zero]
      simp
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b ^ (2 : ℝ)) t ∂(volume : Measure ℝ) :=
      lintegral_mono hpoint
    _ = b ^ (2 : ℝ) * volume K := lintegral_indicator_const hK.measurableSet _

/-- The spatial gradient cutoff error tends to zero in the time-slice
essential-sup norm with an explicit fourth-order radius bound. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_L1tLinf_bound
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C ≥ 0, ∀ (n : ℕ) (i j : Fin 3),
      ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ) ≤
      ENNReal.ofReal (C *
        ((1 + rieszPressurePotentialCutoffScale n / 2) ^ (-(4 : ℝ)))) * volume K := by
  obtain ⟨K, hK, hzero⟩ := associatedPressureHelmholtzPotentials_compactTimeSupport hφ
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurl_spatialPartial_error_profile hφ
  refine ⟨K, hK, C, hC, ?_⟩
  intro n i j
  let s := rieszPressurePotentialCutoffScale n
  let ρ := s / 2
  let b : ℝ≥0∞ := ENNReal.ofReal (C * ((1 + ρ) ^ (-(4 : ℝ))))
  have hs1 : 1 ≤ s := by simpa [s] using rieszPressurePotentialCutoffScale_ge_one n
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hpointwise (t : ℝ) (x : Vec3) :
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t)| ≤
      C * (1 + ρ) ^ (-(4 : ℝ)) := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile n (x, t) i j
      have hxy : 1 + ρ ≤ 1 + ‖x‖ := by linarith only [hx]
      have hdecay : (1 + ‖x‖) ^ (-(4 : ℝ)) ≤ (1 + ρ) ^ (-(4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hxy (by norm_num)
      exact herr.trans (mul_le_mul_of_nonneg_left hdecay hC)
    · have hnormlt : ‖x‖ < ρ := lt_of_not_ge hx
      have hEupper := vec3EuclideanNorm_le_sqrt_three_mul_norm x
      have hsqrt3 : Real.sqrt 3 ≤ 2 := by
        nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      have hE : vec3EuclideanNorm x < s := by
        calc
          vec3EuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := hEupper
          _ ≤ 2 * ‖x‖ := mul_le_mul_of_nonneg_right hsqrt3 (norm_nonneg x)
          _ < 2 * ρ := by nlinarith only [hnormlt]
          _ = s := by dsimp [ρ, s]; ring
      have hxBall : x ∈ CKN.euclideanBall 0 s := by
        apply (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hspos).2
        simpa [vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using hE
      have hxClosed : x ∈ CKN.euclideanClosedBall 0 s := by
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hspos.le).2
        exact (CKN.mem_euclideanBall_iff_vecEuclideanNorm_lt hspos).1 hxBall |>.le
      have heq := hp_cutoffCurl_spatialPartial_eq_inner hφ n (x, t) i j
        (by simpa [s] using hxBall) (by simpa [s] using hxClosed)
      have hz : CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t) = 0 := by
        exact sub_eq_zero.mpr heq
      rw [hz]
      simpa using mul_nonneg hC
        (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ρ) (-(4 : ℝ)))
  have hpoint (t : ℝ) :
      eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ≤ K.indicator (fun _ => b) t := by
    by_cases ht : t ∈ K
    · rw [Set.indicator_of_mem ht]
      have hbound (x : Vec3) :
          ‖CKN.spatialPartialProd
              (fun q => associatedPressureTestCurl
                (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
            CKN.spatialPartialProd
              (fun q => associatedPressureTestCurl
                (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t)‖ ≤
          C * (1 + ρ) ^ (-(4 : ℝ)) := by
        rw [Real.norm_eq_abs]
        exact hpointwise t x
      have hsup := eLpNormEssSup_le_of_ae_bound (μ := volume)
        (Filter.Eventually.of_forall hbound)
      simpa [b, ρ, s] using hsup
    · rw [Set.indicator_of_notMem ht]
      have hcut := fun x => hp_cutoffCurl_spatialPartial_zero_off_time
        hφ hK.isClosed (fun r hr y => (hzero r hr y).2) n t ht x i j
      have hbaseCurl : ContDiff ℝ (⊤ : ℕ∞)
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) :=
        (contDiff_apply ℝ ℝ i).comp
          (associatedPressureTestCurl_contDiff
            (associatedPressureHelmholtzVectorPotential_contDiff hφ))
      have hbase (x : Vec3) :
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t) = 0 :=
        hp_spatialPartial_zero_of_time_zero hbaseCurl hK.isClosed
          (fun r hr y => hp_potentialCurl_zero_off_time hφ hK.isClosed
            (fun a ha w => (hzero a ha w).2) r hr y i) (z := (x, t)) ht j
      have hz : (fun x : Vec3 =>
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
          CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t)) = 0 := by
        funext x
        simp [hcut x, hbase x]
      rw [hz, eLpNormEssSup_zero]
  calc
    _ ≤ ∫⁻ t, K.indicator (fun _ => b) t ∂(volume : Measure ℝ) :=
      lintegral_mono hpoint
    _ = b * volume K := lintegral_indicator_const hK.measurableSet b

private theorem hp_cutoffScaleHalf_tendsto_atTop :
    Tendsto (fun n : ℕ => rieszPressurePotentialCutoffScale n / 2) atTop atTop := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1 hnat
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((n : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) hshift
  simpa [rieszPressurePotentialCutoffScale, div_eq_mul_inv, mul_comm] using hhalf

private theorem hp_cutoffScaleHalf_rpow_three_halves_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))
      atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
    hp_cutoffScaleHalf_tendsto_atTop

private theorem hp_cutoffScaleHalf_rpow_four_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (1 + rieszPressurePotentialCutoffScale n / 2) ^ (-(4 : ℝ)))
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : ℕ => 1 + rieszPressurePotentialCutoffScale n / 2) atTop atTop :=
    Filter.tendsto_atTop_add_const_left atTop 1 hp_cutoffScaleHalf_tendsto_atTop
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hbase

private theorem hp_tendsto_ENNReal_zero_of_le
    {f g : ℕ → ℝ≥0∞} (hg : Tendsto g atTop (nhds 0))
    (hfg : ∀ n, f n ≤ g n) : Tendsto f atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
    (fun n => bot_le) hfg

/-- Each component of the time derivative cutoff error converges to zero in
the time-integrated spatial L² norm, with the explicit R^(-3/2) rate. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_L1tL2x_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ i : Fin 3,
      Tendsto (fun n : ℕ => ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurl_timePartial_L1tL2x_bound hφ
  refine ⟨K, hK, ?_⟩
  refine ⟨C, ?_⟩
  constructor
  · exact hC
  ·
    have hreal : Tendsto (fun n : ℕ =>
        associatedPressureHelmholtzTailL2Constant *
          (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))
        atTop (nhds 0) := by
      simpa [mul_zero] using
        (tendsto_const_nhds.mul hp_cutoffScaleHalf_rpow_three_halves_tendsto_zero)
    have htail := ENNReal.tendsto_ofReal hreal
    have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
    have hmeasure (i : Fin 3) : Tendsto (fun n : ℕ =>
        (ENNReal.ofReal C * ENNReal.ofReal
          (associatedPressureHelmholtzTailL2Constant *
            (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))) * volume K)
        atTop (nhds 0) := by
      have hscaled := ENNReal.Tendsto.const_mul htail
        (a := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
      have hscaledMeasure := ENNReal.Tendsto.mul_const hscaled
        (b := volume K) (Or.inr hfinite)
      simpa using hscaledMeasure
    intro i
    exact hp_tendsto_ENNReal_zero_of_le (hmeasure i) (fun n => hbound n i)

/-- Each spatial derivative cutoff error converges to zero in space-time L²,
with the explicit R^(-3/2) rate. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_L2tx_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun n : ℕ => ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurl_spatialPartial_L2tx_sq_bound hφ
  refine ⟨K, hK, C, hC, ?_⟩
  have hreal : Tendsto (fun n : ℕ =>
      associatedPressureHelmholtzTailL2Constant *
        (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul hp_cutoffScaleHalf_rpow_three_halves_tendsto_zero)
  have htail := ENNReal.tendsto_ofReal hreal
  have hscaled := ENNReal.Tendsto.const_mul htail
    (a := ENNReal.ofReal C) (Or.inr ENNReal.ofReal_ne_top)
  have hscaled' : Tendsto (fun n : ℕ => ENNReal.ofReal C *
      ENNReal.ofReal (associatedPressureHelmholtzTailL2Constant *
        (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ))))
      atTop (nhds 0) := by simpa using hscaled
  have hscaledSq := (ENNReal.continuous_pow 2).tendsto 0 |>.comp hscaled'
  have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hupper : Tendsto (fun n : ℕ =>
      (ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant *
          (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ)))) ^ (2 : ℝ) *
        volume K) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hscaledSq (b := volume K) (Or.inr hfinite)
  intro i j
  exact hp_tendsto_ENNReal_zero_of_le hupper (fun n => hbound n i j)

/-- Each spatial derivative cutoff error converges to zero in the
time-integrated spatial essential-sup norm, with a fourth-order radius bound. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_L1tLinf_tendsto_zero
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun n : ℕ => ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0) := by
  obtain ⟨K, hK, C, hC, hbound⟩ :=
    associatedPressureHelmholtzCutoffCurl_spatialPartial_L1tLinf_bound hφ
  refine ⟨K, hK, C, hC, ?_⟩
  have hreal : Tendsto (fun n : ℕ =>
      C * (1 + rieszPressurePotentialCutoffScale n / 2) ^ (-(4 : ℝ)))
      atTop (nhds 0) := by
    simpa [mul_zero] using
      (tendsto_const_nhds.mul hp_cutoffScaleHalf_rpow_four_tendsto_zero)
  have hcoefficient : Tendsto (fun n : ℕ => ENNReal.ofReal
      (C * (1 + rieszPressurePotentialCutoffScale n / 2) ^ (-(4 : ℝ))))
      atTop (nhds 0) := by simpa using ENNReal.tendsto_ofReal hreal
  have hfinite : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hupper : Tendsto (fun n : ℕ =>
      ENNReal.ofReal
        (C * (1 + rieszPressurePotentialCutoffScale n / 2) ^ (-(4 : ℝ))) *
        volume K) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.mul_const hcoefficient
      (b := volume K) (Or.inr hfinite)
  intro i j
  exact hp_tendsto_ENNReal_zero_of_le (by simpa using hupper) (fun n => hbound n i j)

end CKN.Leray

end
