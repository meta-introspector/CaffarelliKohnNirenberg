-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Parabolic.Vec3Norm
public import CKN.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory Set
open Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

private instance forcedLerayLimitFluxHolderTriple :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := by
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have h := hreal.ennrealOfReal
  norm_num at h ⊢
  exact h

theorem forcedLerayLimit_flux_integral_bound
    (T : ℝ)
    (U J : ParabolicPoint → Vec3) (P : ParabolicPoint → ℝ)
    (M3 MJ MP : ℝ≥0∞)
    (hM3 : M3 < ⊤) (hMJ : MJ < ⊤) (hMP : MP < ⊤)
    (hU : AEStronglyMeasurable U
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hJ : AEStronglyMeasurable J
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hP : AEStronglyMeasurable P
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hUbound : eLpNorm (fun z => vec3EuclideanNorm (U z)) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ M3)
    (hJbound : ∀ i : Fin 3, eLpNorm (fun z => J z i) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MJ)
    (hPbound : eLpNorm P (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ≤ MP) :
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      vec3EuclideanNorm (U z) ^ (2 : ℕ) *
          ∑ i : Fin 3, |J z i| +
        2 * |P z| * ∑ i : Fin 3, |U z i|
      ≤ (M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3)).toReal := by
  classical
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let μ : Measure ParabolicPoint := volume.restrict S
  let V : ParabolicPoint → ℝ := fun z => vec3EuclideanNorm (U z)
  let Q : ParabolicPoint → ℝ := fun z => V z ^ (2 : ℕ)
  let A : ParabolicPoint → ℝ := fun z =>
    Q z * ∑ i : Fin 3, |J z i|
  let B : ParabolicPoint → ℝ := fun z =>
    2 * |P z| * ∑ i : Fin 3, |U z i|
  let H : ParabolicPoint → ℝ := fun z => A z + B z
  have hV : AEStronglyMeasurable V μ := by
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable hU
  have hQ : AEStronglyMeasurable Q μ := hV.pow 2
  have hJcoord : ∀ i : Fin 3, AEStronglyMeasurable (fun z => |J z i|) μ := by
    intro i
    exact _root_.continuous_abs.comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hJ)
  have hUcoord : ∀ i : Fin 3, AEStronglyMeasurable (fun z => |U z i|) μ := by
    intro i
    exact _root_.continuous_abs.comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hU)
  have hPabs : AEStronglyMeasurable (fun z => |P z|) μ :=
    _root_.continuous_abs.comp_aestronglyMeasurable hP
  have hJsum : AEStronglyMeasurable (fun z => ∑ i : Fin 3, |J z i|) μ :=
    Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hJcoord i)
  have hUsum : AEStronglyMeasurable (fun z => ∑ i : Fin 3, |U z i|) μ :=
    Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hUcoord i)
  have hA : AEStronglyMeasurable A μ := by
    dsimp [A]
    exact hQ.mul hJsum
  have hB : AEStronglyMeasurable B μ := by
    dsimp [B]
    convert (hPabs.mul hUsum).const_mul 2 using 1
    ext z
    simp only [Pi.mul_apply]
    ring
  have hH : AEStronglyMeasurable H μ := hA.add hB
  have hQbound : eLpNorm Q (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ M3 ^ (2 : ℕ) := by
    have hraw := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := (3 : ℝ≥0∞)) (q := (3 : ℝ≥0∞))
      (r := ENNReal.ofReal (3 / 2 : ℝ))
      (fun x y : ℝ => x * y) 1 continuous_mul hV hV
      (Eventually.of_forall fun z => by
        dsimp [Q, V]
        norm_num [Real.norm_eq_abs])
      (hpqr := by
        have hr : Real.HolderTriple 3 3 (3 / 2) :=
          ⟨by norm_num, by norm_num, by norm_num⟩
        simpa only [ENNReal.ofReal_ofNat] using hr.ennrealOfReal)
    have hprod : eLpNorm (fun z => V z * V z) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
        M3 * M3 := by
      calc
        _ ≤ eLpNorm V 3 μ * eLpNorm V 3 μ := by simpa using hraw
        _ ≤ M3 * M3 := mul_le_mul hUbound hUbound (by positivity) (by positivity)
    simpa [Q, pow_two] using hprod
  have hJbound' : ∀ i : Fin 3, eLpNorm (fun z => |J z i|) 3 μ ≤ MJ := by
    intro i
    calc
      eLpNorm (fun z => |J z i|) 3 μ = eLpNorm (fun z => J z i) 3 μ :=
        eLpNorm_norm _ ((continuous_apply i).comp_aestronglyMeasurable hJ)
      _ ≤ MJ := hJbound i
  have hAbound : eLpNorm A 1 μ ≤ M3 ^ (2 : ℕ) * (3 * MJ) := by
    let F : Fin 3 → ParabolicPoint → ℝ := fun i z => Q z * |J z i|
    have hFmeas : ∀ i : Fin 3, AEStronglyMeasurable (F i) μ := by
      intro i
      exact hQ.mul (hJcoord i)
    have hFbound : ∀ i : Fin 3, eLpNorm (F i) 1 μ ≤ M3 ^ (2 : ℕ) * MJ := by
      intro i
      have hh := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (3 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (fun x y : ℝ => x * y) 1 continuous_mul hQ (hJcoord i)
        (Eventually.of_forall fun z => by simp [Real.norm_eq_abs])
      calc
        eLpNorm (F i) 1 μ ≤ eLpNorm Q (ENNReal.ofReal (3 / 2 : ℝ)) μ *
            eLpNorm (fun z => |J z i|) 3 μ := by simpa [F] using hh
        _ ≤ M3 ^ (2 : ℕ) * MJ :=
          mul_le_mul hQbound (hJbound' i) (by positivity) (by positivity)
    have hsum : eLpNorm (fun z => ∑ i : Fin 3, F i z) 1 μ ≤
        ∑ i : Fin 3, eLpNorm (F i) 1 μ :=
      eLpNorm_sum_le (p := (1 : ℝ≥0∞)) (s := (Finset.univ : Finset (Fin 3)))
        (f := F) (by norm_num)
    have hsumBound : ∑ i : Fin 3, eLpNorm (F i) 1 μ ≤
        M3 ^ (2 : ℕ) * (3 * MJ) := by
      calc
        _ ≤ ∑ _i : Fin 3, M3 ^ (2 : ℕ) * MJ :=
          Finset.sum_le_sum fun i _ => hFbound i
        _ = M3 ^ (2 : ℕ) * (3 * MJ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    have hAeq : A = fun z => ∑ i : Fin 3, F i z := by
      funext z
      dsimp [A, F, Q, V]
      rw [Finset.mul_sum]
    rw [hAeq]
    exact hsum.trans hsumBound
  have hUcoordBound : ∀ i : Fin 3, eLpNorm (fun z => |U z i|) 3 μ ≤ M3 := by
    intro i
    have hmono : eLpNorm (fun z => |U z i|) 3 μ ≤ eLpNorm V 3 μ := by
      apply eLpNorm_mono_ae_real (hUcoord i)
      filter_upwards [] with z
      calc
        ‖|U z i|‖ = |U z i| := by simp
        _ = ‖U z i‖ := Real.norm_eq_abs _
        _ ≤ vec3EuclideanNorm (U z) :=
          (norm_le_pi_norm (U z) i).trans (norm_le_vec3EuclideanNorm (U z))
        _ = V z := rfl
    exact hmono.trans hUbound
  have hPabsBound : eLpNorm (fun z => |P z|) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ MP := by
    calc
      eLpNorm (fun z => |P z|) (ENNReal.ofReal (3 / 2 : ℝ)) μ =
          eLpNorm P (ENNReal.ofReal (3 / 2 : ℝ)) μ := eLpNorm_norm _ hP
      _ ≤ MP := hPbound
  have hBbound : eLpNorm B 1 μ ≤ 2 * MP * (3 * M3) := by
    let G : Fin 3 → ParabolicPoint → ℝ := fun i z => |P z| * |U z i|
    have hGbound : ∀ i : Fin 3, eLpNorm (G i) 1 μ ≤ MP * M3 := by
      intro i
      have hh := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (3 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
        (fun x y : ℝ => x * y) 1 continuous_mul hPabs (hUcoord i)
        (Eventually.of_forall fun z => by simp [Real.norm_eq_abs])
      calc
        eLpNorm (G i) 1 μ ≤ eLpNorm (fun z => |P z|)
            (ENNReal.ofReal (3 / 2 : ℝ)) μ * eLpNorm (fun z => |U z i|) 3 μ := by
              simpa [G] using hh
        _ ≤ MP * M3 := mul_le_mul hPabsBound (hUcoordBound i)
            (by positivity) (by positivity)
    have hsum : eLpNorm (fun z => 2 * ∑ i : Fin 3, G i z) 1 μ ≤
        2 * ∑ i : Fin 3, eLpNorm (G i) 1 μ := by
      have hsum' : eLpNorm (fun z => ∑ i : Fin 3, G i z) 1 μ ≤
          ∑ i : Fin 3, eLpNorm (G i) 1 μ :=
        eLpNorm_sum_le (p := (1 : ℝ≥0∞)) (s := (Finset.univ : Finset (Fin 3)))
          (f := G) (by norm_num)
      calc
        _ = 2 * eLpNorm (fun z => ∑ i : Fin 3, G i z) 1 μ := by
          have hfun : (2 : ℕ) • (fun z => ∑ i : Fin 3, G i z) =
              (fun z => 2 * ∑ i : Fin 3, G i z) := by
            funext z
            norm_num [Pi.smul_apply, nsmul_eq_mul]
          calc
            eLpNorm (fun z => 2 * ∑ i : Fin 3, G i z) 1 μ =
                eLpNorm ((2 : ℕ) • (fun z => ∑ i : Fin 3, G i z)) 1 μ := by
              rw [hfun]
            _ = (↑(2 : ℕ) : ℝ≥0∞) *
                eLpNorm (fun z => ∑ i : Fin 3, G i z) 1 μ :=
              eLpNorm_nsmul 2 (fun z => ∑ i : Fin 3, G i z)
            _ = 2 * eLpNorm (fun z => ∑ i : Fin 3, G i z) 1 μ := by norm_num
        _ ≤ 2 * ∑ i : Fin 3, eLpNorm (G i) 1 μ := mul_le_mul_of_nonneg_left hsum' (by norm_num)
    have hsumBound : 2 * ∑ i : Fin 3, eLpNorm (G i) 1 μ ≤ 2 * MP * (3 * M3) := by
      calc
        _ ≤ 2 * ∑ _i : Fin 3, MP * M3 := by
          gcongr with i hi
          exact hGbound i
        _ = 2 * MP * (3 * M3) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    have hBeq : B = fun z => 2 * ∑ i : Fin 3, G i z := by
      funext z
      dsimp [B, G]
      calc
        2 * |P z| * ∑ i : Fin 3, |U z i| =
            ∑ i : Fin 3, (2 * |P z|) * |U z i| := by
          rw [Finset.mul_sum]
        _ = 2 * ∑ i : Fin 3, |P z| * |U z i| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    rw [hBeq]
    exact hsum.trans hsumBound
  have hHbound : eLpNorm H 1 μ ≤
      M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3) := by
    calc
      eLpNorm H 1 μ ≤ eLpNorm A 1 μ + eLpNorm B 1 μ := by
        change eLpNorm (fun z => A z + B z) 1 μ ≤ _
        exact eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      _ ≤ M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3) := add_le_add hAbound hBbound
  have hboundTop : M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3) < ⊤ := by
    have hM3sq : M3 ^ (2 : ℕ) < ⊤ := by
      simpa [pow_two] using ENNReal.mul_lt_top hM3 hM3
    exact ENNReal.add_lt_top.mpr ⟨
      ENNReal.mul_lt_top hM3sq (ENNReal.mul_lt_top (by norm_num) hMJ),
      ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hMP)
        (ENNReal.mul_lt_top (by norm_num) hM3)⟩
  have hMemH : MemLp H 1 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hHbound hboundTop
  have hHnonneg : ∀ z, 0 ≤ H z := by
    intro z
    dsimp [H, A, B, Q, V]
    exact add_nonneg
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _))
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _))
  have hIntegral : ENNReal.ofReal (∫ z, H z ∂μ) = eLpNorm H 1 μ := by
    rw [hMemH.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hHnonneg z)]
  have hrealNonneg : 0 ≤ ∫ z, H z ∂μ := integral_nonneg hHnonneg
  have hrealBound : ∫ z, H z ∂μ ≤
      (M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3)).toReal := by
    have htoReal : ENNReal.toReal (eLpNorm H 1 μ) ≤
        ENNReal.toReal (M3 ^ (2 : ℕ) * (3 * MJ) + 2 * MP * (3 * M3)) :=
      ENNReal.toReal_mono hboundTop.ne hHbound
    rw [← hIntegral] at htoReal
    simpa only [ENNReal.toReal_ofReal hrealNonneg] using htoReal
  change ∫ z, H z ∂μ ≤ _
  simpa [H, A, B, μ, S] using hrealBound

end CKN.Leray
