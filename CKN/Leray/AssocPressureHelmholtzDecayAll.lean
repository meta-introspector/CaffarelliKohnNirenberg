-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRateSpacetime
public import CKN.Leray.AssocPressureVectorPotentialDecay
public import CKN.Foundation.Harmonic.KernelAllOrders
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# All-order decay in the test-field Helmholtz decomposition

The spatial derivatives are controlled by the all-order Newtonian kernel
estimate and the compact support of the test data.
-/

@[expose] public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal Convolution Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The ordered spatial coordinate derivative used to express `D_x^n` in
`lem:helmholtz-test`. -/
def associatedPressureSpatialMultiPartial :
    (n : ℕ) → (Fin n → Fin 3) → (Vec3 × ℝ → ℝ) → Vec3 × ℝ → ℝ
  | 0, _, f, z => f z
  | n + 1, w, f, z =>
      associatedPressureSpatialMultiPartial n (Fin.tail w)
        (CKN.spatialPartialProd f (w 0)) z

private theorem associatedPressureSpatialMultiPartial_contDiff
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (w : Fin n → Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (associatedPressureSpatialMultiPartial n w f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
      exact ih (CKN.spatialPartial_contDiff hf (w 0)) (Fin.tail w)

private theorem associatedPressureSpatialMultiPartial_slice_bound
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (w : Fin n → Fin 3) (z : Vec3 × ℝ) :
    |associatedPressureSpatialMultiPartial n w f z| ≤
      ‖iteratedFDeriv ℝ n (fun x : Vec3 => f (x, z.2)) z.1‖ := by
  induction n generalizing f z with
  | zero =>
      simp [associatedPressureSpatialMultiPartial, norm_iteratedFDeriv_zero]
  | succ n ih =>
      let i : Fin 3 := w 0
      let fSlice : Vec3 → ℝ := fun x => f (x, z.2)
      let L : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ :=
        ContinuousLinearMap.apply ℝ ℝ (CKN.basisVec i)
      have hL : ‖L‖ ≤ 1 := by
        apply L.opNorm_le_bound
        · norm_num
        · intro u
          have h := ContinuousLinearMap.le_opNorm u (CKN.basisVec i)
          simpa [L, CKN.basisVec, Pi.norm_single] using h
      have hfs : ContDiff ℝ (⊤ : ℕ∞) fSlice := by
        exact hf.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) z.2)
      have hdf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ fSlice) :=
        hfs.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
      have hsource : (fun x : Vec3 => CKN.spatialPartialProd f i (x, z.2)) =
          L ∘ fderiv ℝ fSlice := by
        funext x
        change CKN.spatialDeriv fSlice i x = _
        rfl
      have hiter := L.iteratedFDeriv_comp_left
        (f := fderiv ℝ fSlice) hdf.contDiffAt (i := n) (by exact_mod_cast le_top)
          (x := z.1)
      have hnorm := L.norm_compContinuousMultilinearMap_le
        (iteratedFDeriv ℝ n (fderiv ℝ fSlice) z.1)
      have hderiv : ‖iteratedFDeriv ℝ n (fderiv ℝ fSlice) z.1‖ =
          ‖iteratedFDeriv ℝ (n + 1) fSlice z.1‖ :=
        norm_iteratedFDeriv_fderiv
      have hstep :
          ‖iteratedFDeriv ℝ n
              (fun x : Vec3 => CKN.spatialPartialProd f i (x, z.2)) z.1‖ ≤
            ‖iteratedFDeriv ℝ (n + 1) fSlice z.1‖ := by
        rw [hsource, hiter]
        calc
          _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ fSlice) z.1‖ := hnorm
          _ ≤ ‖iteratedFDeriv ℝ (n + 1) fSlice z.1‖ := by
            rw [hderiv]
            calc
              ‖L‖ * ‖iteratedFDeriv ℝ (n + 1) fSlice z.1‖ ≤
                  1 * ‖iteratedFDeriv ℝ (n + 1) fSlice z.1‖ :=
                mul_le_mul_of_nonneg_right hL (norm_nonneg _)
              _ = _ := one_mul _
      have hmain := ih (CKN.spatialPartial_contDiff hf i) (Fin.tail w) z
      change |associatedPressureSpatialMultiPartial n (Fin.tail w)
          (CKN.spatialPartialProd f (w 0)) z| ≤ _
      exact hmain.trans (by simpa [i, CKN.spatialPartialProd, fSlice] using hstep)

private theorem associatedPressureNewtonianPotential_iteratedFDeriv_far_bound
    {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (k : ℕ) :
    ∃ R ≥ 1, ∃ M ≥ 0, ∃ c ≥ 0, ∀ t x,
      4 * R < vec3EuclideanNorm x →
        ∀ w : Fin k → Fin 3,
        |associatedPressureSpatialMultiPartial k w
          (associatedPressureNewtonianPotential g) (x, t)| ≤
          c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := by
  let K : Set Vec3 := (tsupport g).image Prod.fst
  have hproj : Continuous (fun z : Vec3 × ℝ => z.1) := continuous_fst
  have hK : IsCompact K := hgc.isCompact.image hproj
  have hNormImage : BddAbove (vec3EuclideanNorm '' K) :=
    hK.bddAbove_image CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.continuousOn
  obtain ⟨B, hB⟩ := hNormImage
  let R : ℝ := max 1 B
  have hR : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  obtain ⟨M, hM, hmass⟩ := associatedPressurePotentialSource_slice_integral_bound hg hgc
  obtain ⟨c, hc, hfar⟩ :=
    CKN.Foundation.Heat.exists_norm_iteratedFDeriv_pressureNewtonianPotential_le k
  refine ⟨R, hR, M, hM, c, hc, ?_⟩
  intro t x hx
  let U : Set Vec3 := Metric.ball x (vec3EuclideanNorm x / 16)
  have hU : IsOpen U := Metric.isOpen_ball
  have hxnorm : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
  have hxU : x ∈ U := by
    change dist x x < vec3EuclideanNorm x / 16
    simpa only [dist_self] using div_pos hxnorm (by norm_num)
  have hsourceZero : ∀ y ∉ K, g (y, t) = 0 := by
    intro y hy
    have hnot : (y, t) ∉ tsupport g := by
      intro hmem
      exact hy ⟨(y, t), hmem, rfl⟩
    exact image_eq_zero_of_notMem_tsupport hnot
  have hsourceCompact : HasCompactSupport (fun y : Vec3 => g (y, t)) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    exact ⟨(y, t), subset_tsupport (f := g)
      (Function.mem_support.mpr (by simpa using hy)), rfl⟩
  have hsourceInt : Integrable (fun y : Vec3 => g (y, t)) volume :=
    (hg.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      hsourceCompact
  have hsep : ∀ y ∈ U, ∀ z ∈ K,
      vec3EuclideanNorm x / 2 ≤ vec3EuclideanNorm (y - z) := by
    intro y hy z hz
    have hdist : ‖y - x‖ < vec3EuclideanNorm x / 16 := by
      simpa [U, dist_eq_norm] using hy
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hnear : vec3EuclideanNorm (y - x) < vec3EuclideanNorm x / 8 := by
      have hnorm :=
        CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm (y - x)
      have hmul : Real.sqrt 3 * ‖y - x‖ ≤ 2 * ‖y - x‖ :=
        mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
      linarith only [hdist, hnorm, hmul]
    have hlarge : 3 * vec3EuclideanNorm x / 4 ≤ vec3EuclideanNorm y := by
      have htriangle : vec3EuclideanNorm x ≤
          vec3EuclideanNorm y + vec3EuclideanNorm (x - y) := by
        calc
        vec3EuclideanNorm x = vec3EuclideanNorm (y + (x - y)) := by
            congr 1
            abel
          _ ≤ vec3EuclideanNorm y + vec3EuclideanNorm (x - y) :=
            CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le _ _
      rw [show vec3EuclideanNorm (x - y) = vec3EuclideanNorm (y - x) by
        rw [show x - y = -(y - x) by abel,
          CKN.Foundation.Parabolic.vec3EuclideanNorm_neg]] at htriangle
      linarith only [htriangle, hnear, hxnorm]
    have hsmall : vec3EuclideanNorm z ≤ R :=
      (hB ⟨z, hz, rfl⟩).trans (le_max_right _ _)
    have htriangle : vec3EuclideanNorm y ≤
        vec3EuclideanNorm (y - z) + vec3EuclideanNorm z := by
      calc
        vec3EuclideanNorm y = vec3EuclideanNorm ((y - z) + z) := by
          congr 1
          abel
        _ ≤ vec3EuclideanNorm (y - z) + vec3EuclideanNorm z :=
          CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le _ _
    have hRsmall : R ≤ vec3EuclideanNorm x / 4 := by linarith only [hx]
    nlinarith only [hlarge, hsmall, htriangle, hRsmall]
  have hdelta : 0 < vec3EuclideanNorm x / 2 := by
    have hxlarge : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
    exact half_pos hxlarge
  have hbound := hfar (fun y : Vec3 => g (y, t)) hsourceInt K U hU
    hsourceZero (vec3EuclideanNorm x / 2) hdelta hsep x hxU
  have hmass' : (∫ y : Vec3, |g (y, t)|) ≤ M := hmass t
  have hle : c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ *
      (∫ y : Vec3, |g (y, t)|) ≤
      c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := by
    have hfactor : 0 ≤ c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ := by
      positivity
    exact mul_le_mul_of_nonneg_left hmass' hfactor
  intro w
  have hpoint := hbound.trans hle
  have hkernel :
      ‖iteratedFDeriv ℝ k
        (fun y : Vec3 => associatedPressureNewtonianPotential g (y, t)) x‖ ≤
        c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := by
    simpa [associatedPressureNewtonianPotential] using hpoint
  exact (associatedPressureSpatialMultiPartial_slice_bound
    (associatedPressureNewtonianPotential_contDiff hg hgc) k w (x, t)).trans hkernel

private theorem associatedPressureNewtonianPotential_iteratedFDeriv_far_decay
    {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (k : ℕ) :
    ∃ R ≥ 1, ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (t : ℝ) (x : Vec3),
      4 * R < vec3EuclideanNorm x →
        |associatedPressureSpatialMultiPartial k w
          (associatedPressureNewtonianPotential g) (x, t)| ≤
          C * (1 + vec3EuclideanNorm x) ^ (-(1 + k : ℝ)) := by
  obtain ⟨R, hR, M, hM, c, hc, hfar⟩ :=
    associatedPressureNewtonianPotential_iteratedFDeriv_far_bound hg hgc k
  let n : ℕ := 1 + k
  let C : ℝ := c * M * 4 ^ n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg hc hM) (by positivity)
  refine ⟨R, hR, C, hC, ?_⟩
  intro w t x hx
  have hxnorm : 0 < vec3EuclideanNorm x := lt_trans (by positivity) hx
  have hr : 1 < vec3EuclideanNorm x := by
    nlinarith only [hR, hx]
  have hbase : 0 < 1 + vec3EuclideanNorm x := by positivity
  have htwor : 0 < 2 * vec3EuclideanNorm x := by positivity
  have hleBase : 1 + vec3EuclideanNorm x ≤ 2 * vec3EuclideanNorm x := by
    linarith only [hr]
  have hpow : (1 + vec3EuclideanNorm x) ^ n ≤
      (2 * vec3EuclideanNorm x) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hleBase n
  have hinv : ((2 * vec3EuclideanNorm x) ^ n)⁻¹ ≤
      ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  have hscale : ((vec3EuclideanNorm x / 2) ^ n)⁻¹ =
      2 ^ n * (vec3EuclideanNorm x ^ n)⁻¹ := by
    rw [div_pow]
    field_simp [ne_of_gt hxnorm]
  have hratio : (vec3EuclideanNorm x ^ n)⁻¹ =
      2 ^ n * ((2 * vec3EuclideanNorm x) ^ n)⁻¹ := by
    rw [mul_pow]
    field_simp [ne_of_gt hxnorm]
  have hinvBracket : ((1 + vec3EuclideanNorm x) ^ n)⁻¹ =
      (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) :=
    (CKN.Foundation.Heat.inv_pow_eq_rpow_neg hbase n)
  have hpower : ((vec3EuclideanNorm x / 2) ^ n)⁻¹ ≤
      4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
    rw [hscale, hratio]
    calc
      2 ^ n * (2 ^ n * ((2 * vec3EuclideanNorm x) ^ n)⁻¹) ≤
          2 ^ n * (2 ^ n * ((1 + vec3EuclideanNorm x) ^ n)⁻¹) := by
            gcongr
      _ = 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
            calc
              _ = (2 ^ n * 2 ^ n) * ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by ring
              _ = 4 ^ n * ((1 + vec3EuclideanNorm x) ^ n)⁻¹ := by
                congr 1
                rw [← mul_pow]
                norm_num
              _ = 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
                rw [hinvBracket]
  have hraw := hfar t x hx w
  calc
    _ ≤ c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M := hraw
    _ ≤ c * M * 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by
      dsimp [C, n]
      have hfactor : 0 ≤ c * M := mul_nonneg hc hM
      calc
        c * ((vec3EuclideanNorm x / 2) ^ (1 + k))⁻¹ * M =
            (c * M) * ((vec3EuclideanNorm x / 2) ^ n)⁻¹ := by ring
        _ ≤ (c * M) *
            (4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ))) :=
              mul_le_mul_of_nonneg_left hpower hfactor
        _ = c * M * 4 ^ n * (1 + vec3EuclideanNorm x) ^ (-(n : ℝ)) := by ring
    _ = C * (1 + vec3EuclideanNorm x) ^ (-(1 + k : ℝ)) := by
      simp [C, n, Nat.cast_add]

private theorem associatedPressureSpatialMultiPartial_spatialDecay_of_far
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set ℝ}
    (hK : IsCompact K) (n : ℕ) (w : Fin n → Fin 3)
    (hzero : ∀ t ∉ K, ∀ x,
      associatedPressureSpatialMultiPartial n w f (x, t) = 0)
    (m : ℕ) (R : ℝ) (hR : 1 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hfar : ∀ t x, 4 * R < vec3EuclideanNorm x →
      |associatedPressureSpatialMultiPartial n w f (x, t)| ≤
        C * (1 + vec3EuclideanNorm x) ^ (-(m : ℝ))) :
    ∃ C' ≥ 0, ∀ z,
      |associatedPressureSpatialMultiPartial n w f z| ≤ C' *
        (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) := by
  let F : Vec3 × ℝ → ℝ := fun z =>
    associatedPressureSpatialMultiPartial n w f z
  have hF : Continuous F :=
    (associatedPressureSpatialMultiPartial_contDiff hf n w).continuous
  let B : Set Vec3 := CKN.euclideanClosedBall 0 (4 * R)
  let S : Set (Vec3 × ℝ) := B ×ˢ K
  let absf : Vec3 × ℝ → ℝ := fun z => |F z|
  have hRpos : 0 < 4 * R := by linarith only [hR]
  have hB : IsCompact B := by
    exact CKN.isCompact_euclideanClosedBall 0 hRpos.le
  have hS : IsCompact S := hB.prod hK
  have hImage : BddAbove (absf '' S) := by
    exact hS.bddAbove_image hF.abs.continuousOn
  obtain ⟨M₀, hM₀⟩ := hImage
  let M : ℝ := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  let C' : ℝ := C + M * (1 + 4 * R) ^ m
  have hC' : 0 ≤ C' := by
    dsimp [C']
    exact add_nonneg hC (mul_nonneg hM (by positivity))
  refine ⟨C', hC', ?_⟩
  intro z
  by_cases ht : z.2 ∉ K
  · have hprofile : 0 ≤
        (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num)
          (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1))
        (-(m : ℝ))
    simpa [F, hzero z.2 ht z.1] using mul_nonneg hC' hprofile
  · by_cases hx : 4 * R < vec3EuclideanNorm z.1
    · change |F z| ≤ C' *
        (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ))
      have hCbound : C ≤ C' := by
        dsimp [C']
        exact le_add_of_nonneg_right (mul_nonneg hM (by positivity))
      have hprofile : 0 ≤
          (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) :=
        Real.rpow_nonneg
          (add_nonneg (by norm_num)
            (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1))
          (-(m : ℝ))
      exact (hfar z.2 z.1 hx).trans
        (mul_le_mul_of_nonneg_right hCbound hprofile)
    · have hnorm : vec3EuclideanNorm z.1 ≤ 4 * R := le_of_not_gt hx
      have hball : z.1 ∈ B := by
        apply (CKN.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hRpos.le).2
        simpa [B, vec3EuclideanNorm, CKN.vecEuclideanNorm, CKN.vecNormSq,
          CKN.vecDot, pow_two] using hnorm
      have hzS : z ∈ S := ⟨hball, by simpa using ht⟩
      have hlocal : |F z| ≤ M := by
        have hpoint := hM₀ ⟨z, hzS, rfl⟩
        change |F z| ≤ M₀ at hpoint
        dsimp [M]
        exact hpoint.trans (le_max_left _ _)
      have hA : 0 < 1 + vec3EuclideanNorm z.1 :=
        add_pos_of_pos_of_nonneg (by norm_num)
          (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)
      have hAupper : 1 + vec3EuclideanNorm z.1 ≤ 1 + 4 * R := by
        linarith only [hnorm]
      have hpow : (1 + vec3EuclideanNorm z.1) ^ m ≤ (1 + 4 * R) ^ m :=
        pow_le_pow_left₀ (by positivity) hAupper m
      have hfactor : 1 ≤ (1 + 4 * R) ^ m *
          ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
        have hpos : 0 < (1 + vec3EuclideanNorm z.1) ^ m := pow_pos hA m
        have hdiv : 1 ≤ (1 + 4 * R) ^ m /
            ((1 + vec3EuclideanNorm z.1) ^ m) := by
          apply (le_div_iff₀ hpos).2
          simpa only [one_mul] using hpow
        simpa [div_eq_mul_inv] using hdiv
      have hrpow : (1 + vec3EuclideanNorm z.1) ^ (-(m : ℝ)) =
          ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
        rw [Real.rpow_neg hA.le]
        exact congrArg Inv.inv (by norm_num)
      rw [hrpow]
      dsimp [C']
      calc
        |F z| ≤ M := hlocal
        _ ≤ M * ((1 + 4 * R) ^ m *
            ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) := by
          calc
            M = M * 1 := by ring
            _ ≤ M * ((1 + 4 * R) ^ m *
                ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) :=
              mul_le_mul_of_nonneg_left hfactor hM
        _ ≤ (C + M * (1 + 4 * R) ^ m) *
            ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by
          calc
            M * ((1 + 4 * R) ^ m *
                ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹) =
                (M * (1 + 4 * R) ^ m) *
                  ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ := by ring
            _ ≤ (C + M * (1 + 4 * R) ^ m) *
                  ((1 + vec3EuclideanNorm z.1) ^ m)⁻¹ :=
              mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC)
                (by positivity)

private theorem associatedPressureSpatialMultiPartial_zero_of_slice_zero
    {f : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (w : Fin n → Fin 3) (t : ℝ)
    (hzero : ∀ x, f (x, t) = 0) (x : Vec3) :
    associatedPressureSpatialMultiPartial n w f (x, t) = 0 := by
  induction n generalizing f with
  | zero => simpa [associatedPressureSpatialMultiPartial] using hzero x
  | succ n ih =>
      have hpartial : ∀ y,
          CKN.spatialPartialProd f (w 0) (y, t) = 0 := by
        intro y
        change (fderiv ℝ (fun q : Vec3 => f (q, t)) y) (CKN.basisVec (w 0)) = 0
        rw [show (fun q : Vec3 => f (q, t)) = fun _ => 0 from funext hzero]
        simp
      have htail := ih (CKN.spatialPartial_contDiff hf (w 0))
        (Fin.tail w) hpartial
      change associatedPressureSpatialMultiPartial n (Fin.tail w)
        (fun q => CKN.spatialPartial f (w 0) q) (x, t) = 0
      exact htail

private theorem associatedPressureNewtonianPotential_spatialDerivative_decay
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (n : ℕ) (w : Fin n → Fin 3) :
    ∃ C ≥ 0, ∀ z,
      |associatedPressureSpatialMultiPartial n w
        (associatedPressureNewtonianPotential g) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(1 + n : ℝ)) := by
  obtain ⟨R, hR, C, hC, hfar⟩ :=
    associatedPressureNewtonianPotential_iteratedFDeriv_far_decay hg hgc n
  have hP : ContDiff ℝ (⊤ : ℕ∞) (associatedPressureNewtonianPotential g) :=
    associatedPressureNewtonianPotential_contDiff hg hgc
  let K : Set ℝ := (tsupport g).image Prod.snd
  have hK : IsCompact K := hgc.isCompact.image continuous_snd
  have hzero (t : ℝ) (ht : t ∉ K) (x : Vec3) :
      associatedPressureNewtonianPotential g (x, t) = 0 := by
    have hnot : ∀ y : Vec3, (y, t) ∉ tsupport g := by
      intro y hy
      exact ht ⟨(y, t), hy, rfl⟩
    have hslice : (fun y : Vec3 => g (y, t)) = fun _ => (0 : ℝ) := by
      funext y
      exact image_eq_zero_of_notMem_tsupport (hnot y)
    rw [associatedPressureNewtonianPotential, hslice]
    simp [CKN.pressureNewtonianPotential]
  have hpartialZero (t : ℝ) (ht : t ∉ K) (x : Vec3) :
      associatedPressureSpatialMultiPartial n w
        (associatedPressureNewtonianPotential g) (x, t) = 0 :=
    associatedPressureSpatialMultiPartial_zero_of_slice_zero hP n w t
      (hzero t ht) x
  let F : Vec3 × ℝ → ℝ := fun z =>
    associatedPressureSpatialMultiPartial n w
      (associatedPressureNewtonianPotential g) z
  have hfarF (t : ℝ) (x : Vec3) (hx : 4 * R < vec3EuclideanNorm x) :
      |F (x, t)| ≤ C * (1 + vec3EuclideanNorm x) ^ (-(1 + n : ℝ)) := by
    simpa [F] using hfar w t x hx
  have hglobal := associatedPressureSpatialMultiPartial_spatialDecay_of_far
    hP hK n w (fun t ht x => hpartialZero t ht x) (1 + n) R hR C hC
    (by intro t x hx; simpa [F] using hfarF t x hx)
  obtain ⟨C', hC', hdecay⟩ := hglobal
  exact ⟨C', hC', by intro z; simpa [F, Nat.cast_add] using hdecay z⟩

private theorem associatedPressureNewtonianPotential_spatialDerivative_decay_all
    {g : Vec3 × ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (n : ℕ) :
    ∃ C ≥ 0, ∀ w : Fin n → Fin 3, ∀ z,
      |associatedPressureSpatialMultiPartial n w
        (associatedPressureNewtonianPotential g) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(1 + n : ℝ)) := by
  choose C hC hbound using fun w : Fin n → Fin 3 =>
    associatedPressureNewtonianPotential_spatialDerivative_decay hg hgc n w
  let Csum : ℝ := ∑ w : Fin n → Fin 3, C w
  have hCsum : 0 ≤ Csum := by
    dsimp [Csum]
    exact Finset.sum_nonneg fun w _ => hC w
  refine ⟨Csum, hCsum, ?_⟩
  intro w z
  have hle : C w ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ w)
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(1 + n : ℝ)) :=
    Real.rpow_nonneg
      (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
  exact (hbound w z).trans (mul_le_mul_of_nonneg_right hle hprofile)

private theorem associatedPressureSpatialMultiPartial_sum
    (f : Fin 3 → Vec3 × ℝ → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (n : ℕ) (w : Fin n → Fin 3) (z : Vec3 × ℝ) :
    associatedPressureSpatialMultiPartial n w (fun q => ∑ i : Fin 3, f i q) z =
      ∑ i : Fin 3, associatedPressureSpatialMultiPartial n w (f i) z := by
  induction n generalizing f with
  | zero => simp [associatedPressureSpatialMultiPartial]
  | succ n ih =>
      let g (i : Fin 3) : Vec3 × ℝ → ℝ :=
        CKN.spatialPartialProd (f i) (w 0)
      have hg (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) :=
        CKN.spatialPartial_contDiff (hf i) (w 0)
      have hsum : (fun q => CKN.spatialPartialProd
          (fun y => ∑ i : Fin 3, f i y) (w 0) q) =
          fun q => ∑ i : Fin 3, g i q := by
        funext q
        exact associatedPressureSpatialPartial_finset_sum f hf (w 0) q
      change associatedPressureSpatialMultiPartial n (Fin.tail w)
          (fun q => CKN.spatialPartialProd
            (fun y => ∑ i : Fin 3, f i y) (w 0) q) z = _
      rw [hsum]
      have hresult := ih g hg (Fin.tail w)
      simpa [g, associatedPressureSpatialMultiPartial] using hresult

private theorem associatedPressureSpatialMultiPartial_shift
    (n : ℕ) (w : Fin n → Fin 3) (f : Vec3 × ℝ → ℝ) (i : Fin 3) :
    associatedPressureSpatialMultiPartial n w
        (fun z => CKN.spatialPartialProd f i z) =
      associatedPressureSpatialMultiPartial (n + 1) (Fin.cons i w) f := by
  funext z
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rfl

private theorem associatedPressureHelmholtzScalarPotential_spatialDerivative_decay_all
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∃ C ≥ 0, ∀ w : Fin n → Fin 3, ∀ z,
      |associatedPressureSpatialMultiPartial n w
        (associatedPressureHelmholtzScalarPotential φ) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
  let g : Fin 3 → Vec3 × ℝ → ℝ := fun i z => φ z i
  have hg (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) :=
    (CKN.component_mem_spaceTimeTestFunction hφ i).1
  have hgc (i : Fin 3) : HasCompactSupport (g i) :=
    (CKN.component_mem_spaceTimeTestFunction hφ i).2.1
  choose C hC hbound using fun i : Fin 3 =>
    associatedPressureNewtonianPotential_spatialDerivative_decay_all
      (hg i) (hgc i) (n + 1)
  let Csum : ℝ := ∑ i : Fin 3, C i
  have hCsum : 0 ≤ Csum := by
    dsimp [Csum]
    exact Finset.sum_nonneg fun i _ => hC i
  have hcomponent (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureNewtonianPotential (g i)) :=
    associatedPressureNewtonianPotential_contDiff (hg i) (hgc i)
  let q (i : Fin 3) : Vec3 × ℝ → ℝ := fun z =>
    CKN.spatialPartialProd (associatedPressureNewtonianPotential (g i)) i z
  have hq (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (q i) :=
    CKN.spatialPartial_contDiff (hcomponent i) i
  have hpotential : associatedPressureHelmholtzScalarPotential φ =
      fun z => ∑ i : Fin 3, q i z := by
    funext z
    simpa [q, g] using associatedPressureHelmholtzScalarPotential_eq_sum_spatialPartial hφ z
  refine ⟨Csum, hCsum, ?_⟩
  intro w z
  have hDidentity : associatedPressureSpatialMultiPartial n w
      (associatedPressureHelmholtzScalarPotential φ) z =
      ∑ i : Fin 3, associatedPressureSpatialMultiPartial n w (q i) z := by
    calc
      _ = associatedPressureSpatialMultiPartial n w
          (fun y => ∑ i : Fin 3, q i y) z := by rw [hpotential]
      _ = _ := associatedPressureSpatialMultiPartial_sum q hq n w z
  have hterm (i : Fin 3) :
      |associatedPressureSpatialMultiPartial n w (q i) z| ≤
        C i * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
    rw [associatedPressureSpatialMultiPartial_shift n w
      (associatedPressureNewtonianPotential (g i)) i]
    have h := hbound i (Fin.cons i w) z
    have hexp : -(1 + ((n + 1 : ℕ) : ℝ)) = -(2 + (n : ℝ)) := by
      push_cast
      ring
    rw [hexp] at h
    exact h
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) :=
    Real.rpow_nonneg
      (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
  calc
    |associatedPressureSpatialMultiPartial n w
        (associatedPressureHelmholtzScalarPotential φ) z| =
        |∑ i : Fin 3, associatedPressureSpatialMultiPartial n w (q i) z| :=
      congrArg abs hDidentity
    _ ≤ ∑ i : Fin 3,
        |associatedPressureSpatialMultiPartial n w (q i) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3,
        C i * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = Csum * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
      dsimp [Csum]
      rw [← Finset.sum_mul]

def associatedPressureHelmholtzRotatedTest
    (φ : Vec3 × ℝ → Vec3) (j : Fin 3) : Vec3 × ℝ → Vec3 :=
  fun z i =>
    if j = 0 then
      if i = 1 then -φ z 2 else if i = 2 then φ z 1 else 0
    else if j = 1 then
      if i = 0 then φ z 2 else if i = 2 then -φ z 0 else 0
    else
      if i = 0 then -φ z 1 else if i = 1 then φ z 0 else 0

private theorem associatedPressureHelmholtzRotatedTest_mem_spaceTimeTestFunction
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) :
    associatedPressureHelmholtzRotatedTest φ j ∈
      CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) := by
  have hcomponent (i : Fin 3) := CKN.component_mem_spaceTimeTestFunction hφ i
  have hcont : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzRotatedTest φ j) := by
    apply contDiff_pi.2
    intro i
    fin_cases j <;> fin_cases i <;>
      simp [associatedPressureHelmholtzRotatedTest] <;>
      first
      | exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : Vec3 × ℝ => (0 : ℝ)))
      | exact (hcomponent 0).1
      | exact (hcomponent 0).1.neg
      | exact (hcomponent 1).1
      | exact (hcomponent 1).1.neg
      | exact (hcomponent 2).1
      | exact (hcomponent 2).1.neg
  have hcompact : HasCompactSupport (associatedPressureHelmholtzRotatedTest φ j) :=
    HasCompactSupport.of_support_subset_isCompact hφ.2.1.isCompact (by
      intro z hz
      by_contra hnot
      apply hz
      have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
      funext i
      simp [associatedPressureHelmholtzRotatedTest, hzero])
  have hsupport : Function.support (associatedPressureHelmholtzRotatedTest φ j) ⊆
      tsupport φ := by
    intro z hz
    by_contra hnot
    apply hz
    have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hnot
    funext i
    simp [associatedPressureHelmholtzRotatedTest, hzero]
  have htsupport :
      tsupport (associatedPressureHelmholtzRotatedTest φ j) ⊆ tsupport φ :=
    closure_minimal hsupport (isClosed_tsupport φ)
  exact ⟨hcont, hcompact, htsupport.trans hφ.2.2⟩

private theorem associatedPressureHelmholtzVectorPotential_component_eq_scalarPotential
    {φ : Vec3 × ℝ → Vec3} (j : Fin 3) (z : Vec3 × ℝ) :
    associatedPressureHelmholtzVectorPotential φ z j =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureHelmholtzRotatedTest φ j) z := by
  have hdiv : associatedPressureTestDivergence
      (associatedPressureHelmholtzRotatedTest φ j) =
        fun q => -associatedPressureTestCurlComponent φ j q := by
    funext q
    fin_cases j <;>
      simp [associatedPressureTestDivergence,
        associatedPressureTestCurlComponent,
        associatedPressureHelmholtzRotatedTest, Fin.sum_univ_three,
        CKN.spatialPartialProd, CKN.spatialPartial] <;> ring
  rw [associatedPressureHelmholtzScalarPotential, hdiv,
    associatedPressureNewtonianPotential_neg]
  rfl

private theorem associatedPressureHelmholtzScalarPotential_timePartial_decay_all
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∃ C ≥ 0, ∀ w : Fin n → Fin 3, ∀ z,
      |associatedPressureSpatialMultiPartial n w
        (fun q => CKN.timePartial
          (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φ) q) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
  let φt := associatedPressureVectorTimePartial φ
  have hφt : φt ∈ CKN.spaceTimeTestFunction
      (V := Vec3) Set.univ (Ioo 0 T) :=
    associatedPressureVectorTimePartial_mem_spaceTimeTestFunction hφ
  obtain ⟨C, hC, hdecay⟩ :=
    associatedPressureHelmholtzScalarPotential_spatialDerivative_decay_all hφt n
  refine ⟨C, hC, ?_⟩
  intro w z
  have htime :
      (show ParabolicPoint → ℝ from fun q : Vec3 × ℝ => CKN.timePartial
        (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φ) q) =
      (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φt) := by
    funext q
    exact associatedPressureHelmholtzScalarPotential_timePartial hφ q
  have hDtime := congrArg
    (fun f : Vec3 × ℝ → ℝ => associatedPressureSpatialMultiPartial n w f z) htime
  rw [hDtime]
  exact hdecay w z

private theorem associatedPressureHelmholtzVectorPotential_component_timePartial_eq_scalarPotential
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (j : Fin 3) (z : Vec3 × ℝ) :
    CKN.timePartial
        (show ParabolicPoint → ℝ from
          fun q : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ q j) z =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureVectorTimePartial
          (associatedPressureHelmholtzRotatedTest φ j)) z := by
  have hη := associatedPressureHelmholtzRotatedTest_mem_spaceTimeTestFunction hφ j
  have hpotential :
      (show ParabolicPoint → ℝ from
        fun q : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ q j) =
      (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential
        (associatedPressureHelmholtzRotatedTest φ j)) := by
    funext q
    exact associatedPressureHelmholtzVectorPotential_component_eq_scalarPotential j q
  calc
    _ = CKN.timePartial
        (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential
          (associatedPressureHelmholtzRotatedTest φ j)) z :=
      congrArg (fun f : ParabolicPoint → ℝ => CKN.timePartial f z) hpotential
    _ = associatedPressureHelmholtzScalarPotential
        (associatedPressureVectorTimePartial
          (associatedPressureHelmholtzRotatedTest φ j)) z :=
      associatedPressureHelmholtzScalarPotential_timePartial hη z

private theorem associatedPressureHelmholtzVectorPotential_spatialDerivative_decay_all
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∃ C ≥ 0, ∀ (j : Fin 3) (w : Fin n → Fin 3) (z : Vec3 × ℝ),
      |associatedPressureSpatialMultiPartial n w
        (fun q => associatedPressureHelmholtzVectorPotential φ q j) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
  choose C hC hdecay using fun j : Fin 3 =>
    associatedPressureHelmholtzScalarPotential_spatialDerivative_decay_all
      (associatedPressureHelmholtzRotatedTest_mem_spaceTimeTestFunction hφ j) n
  let Csum : ℝ := ∑ j : Fin 3, C j
  have hCsum : 0 ≤ Csum := by
    dsimp [Csum]
    exact Finset.sum_nonneg fun j _ => hC j
  refine ⟨Csum, hCsum, ?_⟩
  intro j w z
  have hpotential : (fun q => associatedPressureHelmholtzVectorPotential φ q j) =
      associatedPressureHelmholtzScalarPotential
        (associatedPressureHelmholtzRotatedTest φ j) := by
    funext q
    exact associatedPressureHelmholtzVectorPotential_component_eq_scalarPotential j q
  have hle : C j ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) :=
    Real.rpow_nonneg
      (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
  rw [hpotential]
  exact (hdecay j w z).trans (mul_le_mul_of_nonneg_right hle hprofile)

private theorem associatedPressureHelmholtzVectorPotential_timePartial_spatialDerivative_decay_all
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) :
    ∃ C ≥ 0, ∀ (j : Fin 3) (w : Fin n → Fin 3) (z : Vec3 × ℝ),
      |associatedPressureSpatialMultiPartial n w
        (fun q => CKN.timePartial (show ParabolicPoint → ℝ from
          fun y : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ y j) q) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) := by
  choose C hC hdecay using fun j : Fin 3 =>
    associatedPressureHelmholtzScalarPotential_spatialDerivative_decay_all
      (associatedPressureVectorTimePartial_mem_spaceTimeTestFunction
        (associatedPressureHelmholtzRotatedTest_mem_spaceTimeTestFunction hφ j)) n
  let Csum : ℝ := ∑ j : Fin 3, C j
  have hCsum : 0 ≤ Csum := by
    dsimp [Csum]
    exact Finset.sum_nonneg fun j _ => hC j
  refine ⟨Csum, hCsum, ?_⟩
  intro j w z
  have htime :
      (show ParabolicPoint → ℝ from fun q : Vec3 × ℝ => CKN.timePartial
        (show ParabolicPoint → ℝ from
          fun y : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ y j) q) =
      (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential
        (associatedPressureVectorTimePartial
          (associatedPressureHelmholtzRotatedTest φ j))) := by
    funext q
    exact associatedPressureHelmholtzVectorPotential_component_timePartial_eq_scalarPotential
      hφ j q
  have hDtime := congrArg
    (fun f : Vec3 × ℝ → ℝ => associatedPressureSpatialMultiPartial n w f z) htime
  have hle : C j ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(2 + n : ℝ)) :=
    Real.rpow_nonneg
      (add_nonneg (by norm_num)
        (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
  rw [hDtime]
  exact (hdecay j w z).trans (mul_le_mul_of_nonneg_right hle hprofile)

/-- The complete test-field decomposition, derivative decay, and cutoff limits
in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzTestField_full
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    (∀ z, associatedPressureHelmholtzScalarPotential φ z =
        associatedPressureNewtonianPotential (associatedPressureTestDivergence φ) z ∧
      ∀ j, associatedPressureHelmholtzVectorPotential φ z j =
        -associatedPressureNewtonianPotential
          (associatedPressureTestCurlComponent φ j) z) ∧
    (ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzScalarPotential φ) ∧
      ContDiff ℝ (⊤ : ℕ∞) (associatedPressureHelmholtzVectorPotential φ)) ∧
    (∀ z, CKN.spatialLaplacian
        (fun x : Vec3 => associatedPressureHelmholtzScalarPotential φ (x, z.2)) z.1 =
      associatedPressureTestDivergence φ z) ∧
    (∀ z,
      associatedPressureTestDivergence
          (fun q => φ q - associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) q) z = 0 ∧
        (fun q => φ q - associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotential φ) q) z =
            associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) z) ∧
    (∀ k, ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
      |associatedPressureSpatialMultiPartial k w
          (associatedPressureHelmholtzScalarPotential φ) z| +
        |associatedPressureSpatialMultiPartial k w
          (fun q => CKN.timePartial
            (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φ) q) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) ∧
    (∀ k, ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
      ∑ j : Fin 3,
        (|associatedPressureSpatialMultiPartial k w
            (fun q => associatedPressureHelmholtzVectorPotential φ q j) z| +
          |associatedPressureSpatialMultiPartial k w
            (fun q => CKN.timePartial (show ParabolicPoint → ℝ from
              fun y : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ y j) q) z|) ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) ∧
    (∀ n : ℕ,
      associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n) ∈
        CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T) ∧
        (∀ z, associatedPressureTestDivergence
          (associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n)) z = 0)) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ i : Fin 3,
      Tendsto (fun n : ℕ => ∫⁻ t, eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) (x, t) -
        associatedPressureTestTimePartial
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) (x, t))
        2 (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0)) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun n : ℕ => ∫⁻ t, (eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3)) ^ (2 : ℝ) ∂(volume : Measure ℝ)) atTop (nhds 0)) ∧
    (∃ K : Set ℝ, IsCompact K ∧ ∃ C : ℝ, C ≥ 0 ∧ ∀ (i j : Fin 3),
      Tendsto (fun n : ℕ => ∫⁻ t, eLpNormEssSup (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        (volume : Measure Vec3) ∂(volume : Measure ℝ)) atTop (nhds 0)) := by
  have hdivSmooth := associatedPressureTestDivergence_contDiff hφ
  have hdivCompact := associatedPressureTestDivergence_hasCompactSupport hφ
  have hψSmooth := associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hASmooth := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hsigma (z : Vec3 × ℝ) :
      (fun q => φ q - associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotential φ) q) z =
        associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) z := by
    have hidentity := associatedPressureHelmholtz_identity hφ z
    calc
      _ = (associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) z +
          associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) z) -
          associatedPressureTestGradient
            (associatedPressureHelmholtzScalarPotential φ) z := by
        change φ z - associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotential φ) z = _
        rw [hidentity]
      _ = _ := by abel
  have hscalarDecay (k : ℕ) :
      ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
        |associatedPressureSpatialMultiPartial k w
            (associatedPressureHelmholtzScalarPotential φ) z| +
          |associatedPressureSpatialMultiPartial k w
            (fun q => CKN.timePartial
              (show ParabolicPoint → ℝ from associatedPressureHelmholtzScalarPotential φ) q) z| ≤
          C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) := by
    obtain ⟨Cψ, hCψ, hψ⟩ :=
      associatedPressureHelmholtzScalarPotential_spatialDerivative_decay_all hφ k
    obtain ⟨Cψt, hCψt, hψt⟩ :=
      associatedPressureHelmholtzScalarPotential_timePartial_decay_all hφ k
    refine ⟨Cψ + Cψt, add_nonneg hCψ hCψt, ?_⟩
    intro w z
    have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num)
          (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    calc
      _ ≤ Cψ * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) +
          Cψt * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) :=
        add_le_add (hψ w z) (hψt w z)
      _ = (Cψ + Cψt) * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) := by ring
  have hvectorDecay (k : ℕ) :
      ∃ C ≥ 0, ∀ (w : Fin k → Fin 3) (z : Vec3 × ℝ),
        ∑ j : Fin 3,
          (|associatedPressureSpatialMultiPartial k w
              (fun q => associatedPressureHelmholtzVectorPotential φ q j) z| +
            |associatedPressureSpatialMultiPartial k w
              (fun q => CKN.timePartial (show ParabolicPoint → ℝ from
                fun y : Vec3 × ℝ => associatedPressureHelmholtzVectorPotential φ y j) q) z|) ≤
          C * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) := by
    obtain ⟨CA, hCA, hA⟩ :=
      associatedPressureHelmholtzVectorPotential_spatialDerivative_decay_all hφ k
    obtain ⟨CAt, hCAt, hAt⟩ :=
      associatedPressureHelmholtzVectorPotential_timePartial_spatialDerivative_decay_all hφ k
    let Csum : ℝ := ∑ j : Fin 3, (CA + CAt)
    have hCsum : 0 ≤ Csum := by
      dsimp [Csum]
      exact Finset.sum_nonneg fun j _ => add_nonneg hCA hCAt
    refine ⟨Csum, hCsum, ?_⟩
    intro w z
    have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) :=
      Real.rpow_nonneg
        (add_nonneg (by norm_num)
          (CKN.Foundation.Parabolic.vec3EuclideanNorm_nonneg z.1)) _
    calc
      _ ≤ ∑ j : Fin 3,
          (CA * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) +
            CAt * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) :=
        Finset.sum_le_sum fun j _ => add_le_add (hA j w z) (hAt j w z)
      _ = Csum * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) := by
        dsimp [Csum]
        calc
          ∑ j : Fin 3,
              (CA * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) +
                CAt * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ))) =
              ∑ j : Fin 3,
                (CA + CAt) * (1 + vec3EuclideanNorm z.1) ^ (-(2 + k : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [Finset.sum_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    constructor
    · rfl
    · intro j
      rfl
  · exact ⟨hψSmooth, hASmooth⟩
  · intro z
    rw [associatedPressureHelmholtzScalarPotential]
    exact associatedPressureNewtonianPotential_laplacian hdivSmooth hdivCompact z
  · intro z
    constructor
    · have hSigmaFun : (fun q => φ q - associatedPressureTestGradient
          (associatedPressureHelmholtzScalarPotential φ) q) =
        associatedPressureTestCurl (associatedPressureHelmholtzVectorPotential φ) :=
          funext hsigma
      rw [hSigmaFun]
      simpa [associatedPressureTestDivergence, associatedPressureTestPartial,
        CKN.spatialPartialProd] using
          associatedPressureTestCurl_divergence hASmooth z
    · exact hsigma z
  · exact hscalarDecay
  · exact hvectorDecay
  · intro n
    constructor
    · exact associatedPressureHelmholtzCutoffCurl_mem_spaceTimeTestFunction hφ n
    · intro z
      simpa [associatedPressureTestDivergence, associatedPressureTestPartial,
        CKN.spatialPartialProd] using associatedPressureTestCurl_divergence
          (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1 z
  · exact associatedPressureHelmholtzCutoffCurl_timePartial_L1tL2x_tendsto_zero hφ
  · exact associatedPressureHelmholtzCutoffCurl_spatialPartial_L2tx_tendsto_zero hφ
  · exact associatedPressureHelmholtzCutoffCurl_spatialPartial_L1tLinf_tendsto_zero hφ


end CKN.Leray

end
