-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegEquicontinuityMain
public import CKN.Leray.RegEquicontinuityInputsData
public import CKN.Leray.RegContractBoundsTenThirds
public import CKN.Leray.ForcedRegLocalEnergyNLimit

/-!
# Source bounds for the regularized time modulus

The two estimates behind `lem:reg-equicontinuity`. The diffusion and transport
terms of the pairing equation are bounded by the slice `L²` norms of the
velocity and the transport field. By Hölder's inequality in space-time, the
pressure term over a time interval `(s, t)` is bounded by
`‖p‖_{L^{5/3}} ‖g‖_{L^{5/2}} (t - s)^{2/5}`. The estimates hold also when the
lower endpoint `s` is `0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The diffusion and transport terms in the regularized pairing equation are
bounded directly by the slice `L²` norms of the velocity and its transport
field. -/
theorem regEquiSrc_pairing_rhs_bound
    (A G : ℝ) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (U J : Fin 3 → Vec3 → ℝ)
    (hU : ∀ i, MemLp (U i) 2 volume ∧
      (eLpNorm (U i) 2 volume).toReal ≤ A)
    (hJ : ∀ j, MemLp (J j) 2 volume ∧
      (eLpNorm (J j) 2 volume).toReal ≤ A)
    (w : Fin 3 → Vec3 → ℝ)
    (hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i))
    (hwc : ∀ i, HasCompactSupport (w i))
    (hGbound : ∀ i j x, |spatialDeriv (w i) j x| ≤ G) :
    |∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
      (U i x * spatialDeriv (spatialDeriv (w i) j) j x +
        U i x * J j x * spatialDeriv (w i) j x)| ≤
      A * (∑ i : Fin 3,
        (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal) +
        9 * A ^ 2 * G := by
  have hGnonneg : 0 ≤ G := (abs_nonneg _).trans (hGbound 0 0 0)
  have hLapCont (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (spatialLaplacian (w i)) := by
    unfold spatialLaplacian
    exact ContDiff.sum (s := Finset.univ) (fun j _ =>
      contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth (hw i) j) j)
  have hLapCompact (i : Fin 3) : HasCompactSupport
      (spatialLaplacian (w i)) := by
    unfold spatialLaplacian
    exact HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun j : Fin 3 => spatialDeriv (spatialDeriv (w i) j) j)
      (fun j _ => by
        have hfirst : HasCompactSupport (spatialDeriv (w i) j) := by
          change HasCompactSupport
            (fun x => (fderiv ℝ (w i) x) (basisVec j))
          exact (hwc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
        change HasCompactSupport
          (fun x => (fderiv ℝ (spatialDeriv (w i) j) x) (basisVec j))
        exact hfirst.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hLapMem (i : Fin 3) : MemLp (spatialLaplacian (w i)) 2 volume :=
    (hLapCont i).continuous.memLp_of_hasCompactSupport (hLapCompact i)
  have hGradCont (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (w i) j) := contDiff_spatialDeriv_smooth (hw i) j
  have hGradCompact (i j : Fin 3) : HasCompactSupport
      (spatialDeriv (w i) j) := by
    change HasCompactSupport
      (fun x => (fderiv ℝ (w i) x) (basisVec j))
    exact (hwc i).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hGradMem (i j : Fin 3) : MemLp (spatialDeriv (w i) j) 2 volume :=
    (hGradCont i j).continuous.memLp_of_hasCompactSupport (hGradCompact i j)
  have hConvMem (i j : Fin 3) : MemLp
      (fun x => J j x * spatialDeriv (w i) j x) 2 volume := by
    have hmaj : MemLp (fun x => G * |J j x|) 2 volume :=
      ((hJ j).1.norm).const_mul G
    refine hmaj.mono' ((hJ j).1.aestronglyMeasurable.mul
      (hGradMem i j).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    change |J j x * spatialDeriv (w i) j x| ≤ G * |J j x|
    rw [abs_mul]
    calc
      |J j x| * |spatialDeriv (w i) j x| ≤ |J j x| * G :=
        mul_le_mul_of_nonneg_left (hGbound i j x) (abs_nonneg _)
      _ = G * |J j x| := by ring
  have hDiffInt (i : Fin 3) : Integrable
      (fun x => U i x * spatialLaplacian (w i) x) volume :=
    memLp_one_iff_integrable.mp ((hU i).1.mul (hLapMem i))
  have hConvInt (i j : Fin 3) : Integrable
      (fun x => U i x * (J j x * spatialDeriv (w i) j x)) volume :=
    memLp_one_iff_integrable.mp ((hU i).1.mul (hConvMem i j))
  have hDiffBound (i : Fin 3) :
      |∫ x, U i x * spatialLaplacian (w i) x| ≤
        A * (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal := by
    calc
      |∫ x, U i x * spatialLaplacian (w i) x| ≤
          (eLpNorm (U i) 2 volume).toReal *
            (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal :=
        abs_integral_mul_le_eLpNorm_two (hU i).1 (hLapMem i)
      _ ≤ A * (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal :=
        mul_le_mul_of_nonneg_right (hU i).2 (ENNReal.toReal_nonneg)
  have hConvBound (i j : Fin 3) :
      |∫ x, U i x * (J j x * spatialDeriv (w i) j x)| ≤ A ^ 2 * G := by
    have hmul := toReal_eLpNorm_mul_le (hJ j).1
      (hGradMem i j).aestronglyMeasurable (hGbound i j)
    have hcs := abs_integral_mul_le_eLpNorm_two (hU i).1 (hConvMem i j)
    calc
      |∫ x, U i x * (J j x * spatialDeriv (w i) j x)| ≤
          (eLpNorm (U i) 2 volume).toReal *
            (eLpNorm (fun x => J j x * spatialDeriv (w i) j x)
              2 volume).toReal := hcs
      _ ≤ A * (G * (eLpNorm (J j) 2 volume).toReal) := by
        exact mul_le_mul (hU i).2 hmul (by positivity) (by positivity)
      _ ≤ A ^ 2 * G := by
        calc
          A * (G * (eLpNorm (J j) 2 volume).toReal) =
              (A * G) * (eLpNorm (J j) 2 volume).toReal := by ring
          _ ≤ (A * G) * A :=
            mul_le_mul_of_nonneg_left (hJ j).2 (mul_nonneg hA hG)
          _ = A ^ 2 * G := by ring
  have hDiffSum : Integrable (fun x =>
      ∑ i : Fin 3, U i x * spatialLaplacian (w i) x) volume :=
    integrable_finsetSum (s := Finset.univ) (fun i hi => hDiffInt i)
  have hConvInnerIntegrable (i : Fin 3) : Integrable (fun x =>
      ∑ j : Fin 3, U i x * (J j x * spatialDeriv (w i) j x)) volume :=
    integrable_finsetSum (s := Finset.univ) (fun j hj => hConvInt i j)
  have hConvSum : Integrable (fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        U i x * (J j x * spatialDeriv (w i) j x)) volume :=
    integrable_finsetSum (s := Finset.univ)
      (fun i hi => hConvInnerIntegrable i)
  have hRewrite : (fun x =>
      ∑ i : Fin 3, ∑ j : Fin 3,
        (U i x * spatialDeriv (spatialDeriv (w i) j) j x +
          U i x * J j x * spatialDeriv (w i) j x)) = fun x =>
      (∑ i : Fin 3, U i x * spatialLaplacian (w i) x) +
        ∑ i : Fin 3, ∑ j : Fin 3,
          U i x * (J j x * spatialDeriv (w i) j x) := by
    funext x
    simp [spatialLaplacian, Finset.mul_sum, Finset.sum_add_distrib,
      mul_assoc]
  have hDiffIntegral :
      (∫ x, ∑ i : Fin 3, U i x * spatialLaplacian (w i) x) =
        ∑ i : Fin 3, ∫ x, U i x * spatialLaplacian (w i) x :=
    integral_finsetSum (s := Finset.univ) (fun i hi => hDiffInt i)
  have hConvIntegral :
      (∫ x, ∑ i : Fin 3, ∑ j : Fin 3,
          U i x * (J j x * spatialDeriv (w i) j x)) =
        ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, U i x * (J j x * spatialDeriv (w i) j x) := by
    rw [integral_finsetSum (s := Finset.univ)
      (fun i hi => hConvInnerIntegrable i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum (s := Finset.univ) (fun j hj => hConvInt i j)
  rw [hRewrite, integral_add hDiffSum hConvSum, hDiffIntegral, hConvIntegral]
  have hDiffAbs :
      |∑ i : Fin 3, ∫ x, U i x * spatialLaplacian (w i) x| ≤
        A * ∑ i : Fin 3,
          (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal := by
    calc
      _ ≤ ∑ i : Fin 3,
          |∫ x, U i x * spatialLaplacian (w i) x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3,
          A * (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal :=
        Finset.sum_le_sum (fun i hi => hDiffBound i)
      _ = _ := by rw [Finset.mul_sum]
  have hConvAbs :
      |∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, U i x * (J j x * spatialDeriv (w i) j x)| ≤ 9 * A ^ 2 * G := by
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
          |∫ x, U i x * (J j x * spatialDeriv (w i) j x)| := by
            exact (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun i hi => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, A ^ 2 * G := by
        exact Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => hConvBound i j
      _ = 9 * A ^ 2 * G := by
        norm_num [Finset.sum_const, Finset.card_univ]
        ring
  calc
    |(∑ i : Fin 3, ∫ x, U i x * spatialLaplacian (w i) x) +
       ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x, U i x * (J j x * spatialDeriv (w i) j x)| ≤
      |∑ i : Fin 3, ∫ x, U i x * spatialLaplacian (w i) x| +
        |∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x, U i x * (J j x * spatialDeriv (w i) j x)| := abs_add_le _ _
    _ ≤ A * (∑ i : Fin 3,
          (eLpNorm (spatialLaplacian (w i)) 2 volume).toReal) +
        9 * A ^ 2 * G := add_le_add hDiffAbs hConvAbs

theorem regEquiSrc_interval_pressure_bound
    {p : ParabolicPoint → ℝ}
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure)
    (P : ℝ) (hP0 : 0 ≤ P)
    (hP : eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
      regUniformPositiveTimeMeasure ≤ ENNReal.ofReal P)
    {g : Vec3 → ℝ}
    (hg : MemLp g (ENNReal.ofReal (5 / 2 : ℝ)) volume)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    |∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume| ≤
      P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := by
  let ν : Measure ℝ := volume.restrict (Ioc s t)
  let μ : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod ν
  let Q : Set ParabolicPoint := Set.univ ×ˢ Ioc s t
  have hIocPos : Ioc s t ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact (lt_of_le_of_lt hs hr.1)
  have hMeasure : regUniformPositiveTimeMeasure.restrict Q = μ := by
    change (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ))).restrict (Set.univ ×ˢ Ioc s t) =
      (volume : Measure Vec3).prod (volume.restrict (Ioc s t))
    rw [Measure.restrict_restrict_of_subset
      (Set.prod_mono (Set.Subset.refl Set.univ) hIocPos)]
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioc s t)]
    simp [Measure.restrict_univ]
  have hνfinite : ν Set.univ < ⊤ := by
    simp [ν]
  let : IsFiniteMeasure ν := ⟨hνfinite⟩
  have hgLift : MemLp (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ := by
    change MemLp (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) ((volume : Measure Vec3).prod ν)
    exact hg.comp_fst (volume.restrict (Ioc s t))
  have hgQ : MemLp (fun z : ParabolicPoint => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) (regUniformPositiveTimeMeasure.restrict Q) := by
    rw [hMeasure]
    exact hgLift
  have hProduct := regEquicontinuity_pressure_mul_memLp_one p
    (fun z : ParabolicPoint => g z.1) Q hp hgQ
  let fP : ParabolicPoint → ℝ := fun z => p z * g z.1
  let f : Vec3 × ℝ → ℝ := fun z => p (z.1, z.2) * g z.1
  have hProductIntegrable : Integrable f μ := by
    rw [← hMeasure]
    change Integrable fP
      (regUniformPositiveTimeMeasure.restrict Q)
    exact memLp_one_iff_integrable.mp hProduct.1
  have hProductBound : eLpNorm f 1 μ ≤
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
        eLpNorm (fun z : Vec3 × ℝ => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) μ := by
    rw [← hMeasure]
    change eLpNorm fP 1 (regUniformPositiveTimeMeasure.restrict Q) ≤
      eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
        eLpNorm (fun z : ParabolicPoint => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) (regUniformPositiveTimeMeasure.restrict Q)
    exact hProduct.2
  have hMass : ν Set.univ = ENNReal.ofReal (t - s) := by
    simp [ν]
  have hMassNe : ν Set.univ ≠ 0 := by
    rw [hMass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hst))
  have hExponent : (ENNReal.ofReal (5 / 2 : ℝ)).toReal⁻¹ = 2 / 5 := by
    norm_num
  have hLiftNorm : eLpNorm (fun z : Vec3 × ℝ => g z.1)
      (ENNReal.ofReal (5 / 2 : ℝ)) μ =
      ENNReal.ofReal ((t - s) ^ (2 / 5 : ℝ)) *
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
    calc
      eLpNorm (fun z : Vec3 × ℝ => g z.1)
          (ENNReal.ofReal (5 / 2 : ℝ)) μ =
        eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) (Measure.map Prod.fst μ) := by
          symm
          have hmap : AEStronglyMeasurable g (Measure.map Prod.fst μ) := by
            rw [Measure.map_fst_prod]
            exact hg.aestronglyMeasurable.smul_measure _
          exact eLpNorm_map_measure hmap measurable_fst.aemeasurable
      _ = eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
          ((ν Set.univ) • (volume : Measure Vec3)) := by
            change eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ))
              (Measure.map Prod.fst ((volume : Measure Vec3).prod ν)) = _
            rw [Measure.map_fst_prod]
      _ = (ν Set.univ) ^ (2 / 5 : ℝ) *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
            rw [eLpNorm_smul_measure_of_ne_zero hMassNe]
            simp [hExponent]
      _ = ENNReal.ofReal ((t - s) ^ (2 / 5 : ℝ)) *
          eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume := by
            rw [hMass, ENNReal.ofReal_rpow_of_nonneg (sub_nonneg.mpr hst.le)
              (by norm_num)]
  have hProductRealBound : (eLpNorm f 1 μ).toReal ≤
      P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := by
    have hPfinite : eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
        regUniformPositiveTimeMeasure < ⊤ :=
      lt_of_le_of_lt hP ENNReal.ofReal_lt_top
    have hgfinite : eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume < ⊤ :=
      hg.eLpNorm_lt_top
    have hprodFinite : eLpNorm f 1 μ < ⊤ := by
      calc
        eLpNorm f 1 μ ≤
            eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
              eLpNorm (fun z : Vec3 × ℝ => g z.1)
                (ENNReal.ofReal (5 / 2 : ℝ)) μ := hProductBound
        _ < ⊤ := ENNReal.mul_lt_top hPfinite (by
          rw [hLiftNorm]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfinite)
    have hRhsFinite :
        eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
          eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ < ⊤ := by
      exact ENNReal.mul_lt_top hPfinite (by
        rw [hLiftNorm]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfinite)
    have hreal : (eLpNorm f 1 μ).toReal ≤
        (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure).toReal *
          (eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := by
      calc
        (eLpNorm f 1 μ).toReal ≤
            (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure *
              eLpNorm (fun z : Vec3 × ℝ => g z.1)
                (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal :=
          ENNReal.toReal_mono hRhsFinite.ne hProductBound
        _ = _ := by
          rw [ENNReal.toReal_mul]
    calc
      (eLpNorm f 1 μ).toReal ≤
          (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ)) regUniformPositiveTimeMeasure).toReal *
            (eLpNorm (fun z : Vec3 × ℝ => g z.1)
              (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := hreal
      _ ≤ P * (eLpNorm (fun z : Vec3 × ℝ => g z.1)
            (ENNReal.ofReal (5 / 2 : ℝ)) μ).toReal := by
          gcongr
          calc
            (eLpNorm p (ENNReal.ofReal (5 / 3 : ℝ))
                regUniformPositiveTimeMeasure).toReal ≤
              (ENNReal.ofReal P).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
            _ = P := ENNReal.toReal_ofReal hP0
      _ = P * ((t - s) ^ (2 / 5 : ℝ) *
            (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal) := by
          rw [hLiftNorm, ENNReal.toReal_mul]
          simp [ENNReal.toReal_ofReal (Real.rpow_nonneg
            (sub_nonneg.mpr hst.le) _)]
      _ = P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
            (t - s) ^ (2 / 5 : ℝ) := by ring
  have hAbsIntegral : |∫ z, f z ∂μ| ≤ (eLpNorm f 1 μ).toReal := by
    calc
      |∫ z, f z ∂μ| ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
      _ = ∫ z, ‖f z‖ ∂μ := by simp [Real.norm_eq_abs]
      _ = (eLpNorm f 1 μ).toReal := by
        rw [integral_norm_eq_lintegral_enorm hProductIntegrable.aestronglyMeasurable,
          eLpNorm_one_eq_lintegral_enorm hProductIntegrable.aestronglyMeasurable]
  have hFubini := integral_prod_symm f hProductIntegrable
  have hInterval : (∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume) =
      ∫ z, f z ∂μ := by
    rw [intervalIntegral.integral_of_le hst.le]
    change (∫ r, ∫ x : Vec3, p (x, r) * g x ∂volume ∂ν) = _
    calc
      (∫ r, ∫ x : Vec3, p (x, r) * g x ∂volume ∂ν) =
          ∫ z : Vec3 × ℝ, f z ∂μ := by
            simpa [f] using hFubini.symm
      _ = ∫ z, f z ∂μ := rfl
  calc
    |∫ r in s..t, ∫ x : Vec3, p (x, r) * g x ∂volume| =
        |∫ z, f z ∂μ| := by rw [hInterval]
    _ ≤ (eLpNorm f 1 μ).toReal := hAbsIntegral
    _ ≤ P * (eLpNorm g (ENNReal.ofReal (5 / 2 : ℝ)) volume).toReal *
        (t - s) ^ (2 / 5 : ℝ) := hProductRealBound

end CKN.Leray

end
