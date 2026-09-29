-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.MaximalDisjointBallCovering
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Preorder.Finite

@[expose] public section

open MeasureTheory
open Set
open CKN.Foundation.Parabolic
open scoped ENNReal

set_option autoImplicit false

namespace CKN.Foundation

private theorem finite_disjoint_equal_radius_ball_volume_bound
    {N : ℕ} (x₀ : Vec3) {R r : ℝ} (c : Fin N → Vec3)
    (hcenters : ∀ i, c i ∈ vec3Ball x₀ R)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2))) :
    (N : ℝ≥0∞) *
        ((ENNReal.ofReal (r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) ≤
      (ENNReal.ofReal (R + r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have hsmallSub : ∀ i, vec3Ball (c i) (r / 2) ⊆ vec3Ball x₀ (R + r / 2) := by
    intro i x hx
    change vec3EuclideanNorm (x - c i) < r / 2 at hx
    have hci : vec3EuclideanNorm (c i - x₀) < R := hcenters i
    rw [mem_vec3Ball]
    calc
      vec3EuclideanNorm (x - x₀) =
          vec3EuclideanNorm ((x - c i) + (c i - x₀)) := by congr 1; abel
      _ ≤ vec3EuclideanNorm (x - c i) + vec3EuclideanNorm (c i - x₀) :=
        vec3EuclideanNorm_add_le _ _
      _ < r / 2 + R := add_lt_add hx hci
      _ = R + r / 2 := by ring
  let U : Set Vec3 := ⋃ i : Fin N, vec3Ball (c i) (r / 2)
  have hUsubset : U ⊆ vec3Ball x₀ (R + r / 2) := by
    intro x hx
    rcases Set.mem_iUnion.mp
      (show x ∈ ⋃ i : Fin N, vec3Ball (c i) (r / 2) from hx) with ⟨i, hx⟩
    exact hsmallSub i hx
  have hballsMeas : ∀ i : Fin N, MeasurableSet (vec3Ball (c i) (r / 2)) := by
    intro i
    exact (isOpen_vec3Ball (c i) (r / 2)).measurableSet
  have hballsDisj : Pairwise fun i j : Fin N =>
      Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2)) := by
    intro i j hij
    exact hdisjoint i j hij
  have hUmeasure : volume U = ∑' i : Fin N, volume (vec3Ball (c i) (r / 2)) := by
    exact measure_iUnion hballsDisj hballsMeas
  have hsumMeasure :
      (∑ i : Fin N, volume (vec3Ball (c i) (r / 2))) ≤
        volume (vec3Ball x₀ (R + r / 2)) := by
    calc
      (∑ i : Fin N, volume (vec3Ball (c i) (r / 2))) =
          ∑' i : Fin N, volume (vec3Ball (c i) (r / 2)) := by simp
      _ = volume U := hUmeasure.symm
      _ ≤ volume (vec3Ball x₀ (R + r / 2)) := measure_mono hUsubset
  simpa only [volume_vec3Ball_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, tsum_fintype] using hsumMeasure

private theorem cardinal_bound_of_volume_comparison
    {N : ℕ} {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hvolume :
      (N : ℝ≥0∞) *
          ((ENNReal.ofReal (r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) ≤
        (ENNReal.ofReal (R + r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) :
    (N : ℝ) ≤ (R + r / 2) ^ 3 / (r / 2) ^ 3 := by
  let A : ℝ := Real.pi * 4 / 3
  have hA : 0 < A := by dsimp [A]; positivity
  have hrhalf : 0 < r / 2 := by positivity
  have hRhalf : 0 < R + r / 2 := by positivity
  have hleft :
      ENNReal.ofReal ((N : ℝ) * ((r / 2) ^ 3 * A)) =
        (N : ℝ≥0∞) * ((ENNReal.ofReal (r / 2)) ^ 3 * ENNReal.ofReal A) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hrhalf.le]
  have hright :
      ENNReal.ofReal ((R + r / 2) ^ 3 * A) =
        (ENNReal.ofReal (R + r / 2)) ^ 3 * ENNReal.ofReal A := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hRhalf.le]
  have hreal :
      (N : ℝ) * ((r / 2) ^ 3 * A) ≤ (R + r / 2) ^ 3 * A := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [hleft, hright]
    exact hvolume
  have hreal' : ((N : ℝ) * (r / 2) ^ 3) * A ≤ ((R + r / 2) ^ 3) * A := by
    simpa only [mul_assoc] using hreal
  have hcancel : (N : ℝ) * (r / 2) ^ 3 ≤ (R + r / 2) ^ 3 :=
    (mul_le_mul_iff_of_pos_right hA).mp hreal'
  exact (le_div_iff₀ (pow_pos hrhalf 3)).2 hcancel

private theorem finite_disjoint_equal_radius_ball_card_bound
    {N : ℕ} (x₀ : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (c : Fin N → Vec3) (hcenters : ∀ i, c i ∈ vec3Ball x₀ R)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2))) :
    (N : ℝ) ≤ (R + r / 2) ^ 3 / (r / 2) ^ 3 := by
  exact cardinal_bound_of_volume_comparison hR hr
    (finite_disjoint_equal_radius_ball_volume_bound x₀ c hcenters hdisjoint)

private theorem vec3Ball_disjoint_of_distance_ge
    {x y : Vec3} {r : ℝ}
    (hxy : r ≤ vec3EuclideanNorm (x - y)) :
    Disjoint (vec3Ball x (r / 2)) (vec3Ball y (r / 2)) := by
  rw [Set.disjoint_left]
  intro z hxz hyz
  change vec3EuclideanNorm (z - x) < r / 2 at hxz
  change vec3EuclideanNorm (z - y) < r / 2 at hyz
  have hxz' : vec3EuclideanNorm (x - z) < r / 2 := by
    rw [show x - z = -(z - x) by abel, vec3EuclideanNorm_neg]
    exact hxz
  have hxy' : vec3EuclideanNorm (x - y) < r := by
    calc
      vec3EuclideanNorm (x - y) =
          vec3EuclideanNorm ((x - z) + (z - y)) := by congr 1; abel
      _ ≤ vec3EuclideanNorm (x - z) + vec3EuclideanNorm (z - y) :=
        vec3EuclideanNorm_add_le _ _
      _ < r / 2 + r / 2 := add_lt_add hxz' hyz
      _ = r := by ring
  exact (not_lt_of_ge hxy hxy').elim

/-- A finite maximal family of equal-radius disjoint balls exists inside any
open Vec3 ball. Its maximality is with respect to adding another center from
the same region. -/
theorem exists_finite_maximal_equal_radius_ball_family
    (x₀ : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    ∃ N : ℕ, ∃ c : Fin N → Vec3,
      (∀ i, c i ∈ vec3Ball x₀ R) ∧
      (∀ i j, i ≠ j →
        Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2))) ∧
      (∀ x, x ∈ vec3Ball x₀ R →
        ¬ ∀ i, r ≤ vec3EuclideanNorm (x - c i)) := by
  classical
  let packingCard : Set ℕ := {N | ∃ c : Fin N → Vec3,
    (∀ i, c i ∈ vec3Ball x₀ R) ∧
    (∀ i j, i ≠ j →
      Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2)))}
  have hzero : 0 ∈ packingCard := by
    change ∃ c : Fin 0 → Vec3, _ ∧ _
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro i
      exact Fin.elim0 i
  let M : ℝ := (R + r / 2) ^ 3 / (r / 2) ^ 3
  obtain ⟨K, hMK⟩ := exists_nat_gt M
  have hpackingBound : ∀ N ∈ packingCard, N ≤ K := by
    intro N hN
    change ∃ c : Fin N → Vec3, _ ∧ _ at hN
    obtain ⟨c, hcenters, hdisjoint⟩ := hN
    have hNreal : (N : ℝ) ≤ M := by
      simpa only [M] using
        finite_disjoint_equal_radius_ball_card_bound x₀ hR hr c hcenters hdisjoint
    have hNK : (N : ℝ) < (K : ℝ) := lt_of_le_of_lt hNreal hMK
    exact Nat.le_of_lt (Nat.cast_lt.mp hNK)
  have hpackingSubset : packingCard ⊆ Set.Icc 0 K := by
    intro N hN
    exact ⟨Nat.zero_le N, hpackingBound N hN⟩
  have hpackingFinite : packingCard.Finite :=
    (Set.finite_Icc 0 K).subset hpackingSubset
  obtain ⟨N, hzeroN, hmax⟩ := hpackingFinite.exists_le_maximal hzero
  obtain ⟨c, hcenters, hdisjoint⟩ := hmax.1
  have hmaximal : ∀ x, x ∈ vec3Ball x₀ R →
      ¬ ∀ i, r ≤ vec3EuclideanNorm (x - c i) := by
    intro x hx
    by_contra hfar
    let c' : Fin (N + 1) → Vec3 := Fin.snoc c x
    have hcenters' : ∀ i, c' i ∈ vec3Ball x₀ R := by
      intro i
      induction i using Fin.lastCases with
      | last => simpa only [c', Fin.snoc_last] using hx
      | cast i => simpa only [c', Fin.snoc_castSucc] using hcenters i
    have hdisjoint' : ∀ i j, i ≠ j →
        Disjoint (vec3Ball (c' i) (r / 2)) (vec3Ball (c' j) (r / 2)) := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.lastCases with
          | last => exact (hij rfl).elim
          | cast j =>
              simpa only [c', Fin.snoc_last, Fin.snoc_castSucc] using
                vec3Ball_disjoint_of_distance_ge (hfar j)
      | cast i =>
          induction j using Fin.lastCases with
          | last =>
              simpa only [c', Fin.snoc_last, Fin.snoc_castSucc] using
                (vec3Ball_disjoint_of_distance_ge (hfar i)).symm
          | cast j =>
              have hij' : i ≠ j := by
                intro heq
                apply hij
                simpa only [Fin.castSucc_inj] using heq
              simpa only [c', Fin.snoc_castSucc] using hdisjoint i j hij'
    have hnext : N + 1 ∈ packingCard := by
      change ∃ d : Fin (N + 1) → Vec3, _ ∧ _
      exact ⟨c', hcenters', hdisjoint'⟩
    have hle : N + 1 ≤ N := hmax.2 hnext (Nat.le_succ N)
    exact (lt_irrefl N) (lt_of_lt_of_le (Nat.lt_succ_self N) hle)
  exact ⟨N, c, hcenters, hdisjoint, hmaximal⟩

/-- A maximal family at a scale no larger than half the center-region radius
covers the region after doubling, with the cardinality estimate used in
`thm:uc` of the Escauriaza–Seregin–Šverák manuscript. -/
theorem exists_finite_maximal_equal_radius_ball_cover_with_bound
    (x₀ : Vec3) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hscale : 2 * r ≤ R) :
    ∃ N : ℕ, ∃ c : Fin N → Vec3,
      (∀ i, c i ∈ vec3Ball x₀ R) ∧
      (∀ i j, i ≠ j →
        Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2))) ∧
      (∀ x, x ∈ vec3Ball x₀ R →
        ¬ ∀ i, r ≤ vec3EuclideanNorm (x - c i)) ∧
      (∀ x, x ∈ vec3Ball x₀ R → ∃ i, x ∈ vec3Ball (c i) r) ∧
      (N : ℝ) ≤ 27 * (R / r) ^ 3 := by
  obtain ⟨N, c, hcenters, hdisjoint, hmax⟩ :=
    exists_finite_maximal_equal_radius_ball_family x₀ hR hr
  have hcoverVolume :=
    finite_maximal_equal_radius_ball_cover x₀ c hcenters hdisjoint hmax
  have hcount := cardinal_bound_of_volume_comparison hR hr hcoverVolume.2
  have hratio : (R + r / 2) ^ 3 / (r / 2) ^ 3 = (1 + 2 * R / r) ^ 3 := by
    field_simp [ne_of_gt hr]
    ring
  have hcount' : (N : ℝ) ≤ (1 + 2 * R / r) ^ 3 := by
    calc
      (N : ℝ) ≤ (R + r / 2) ^ 3 / (r / 2) ^ 3 := hcount
      _ = (1 + 2 * R / r) ^ 3 := hratio
  have hbase : 1 + 2 * R / r ≤ 3 * R / r := by
    have hrR : r ≤ R := by linarith only [hscale, hr]
    have hRdiv : 1 ≤ R / r := (one_le_div₀ hr).2 hrR
    calc
      1 + 2 * R / r ≤ R / r + 2 * R / r := add_le_add hRdiv le_rfl
      _ = 3 * R / r := by ring
  have hcount'' : (1 + 2 * R / r) ^ 3 ≤ (3 * R / r) ^ 3 := by
    gcongr
  have hcount''' : (3 * R / r) ^ 3 = 27 * (R / r) ^ 3 := by ring
  have hcountFinal : (N : ℝ) ≤ 27 * (R / r) ^ 3 := by
    calc
      (N : ℝ) ≤ (1 + 2 * R / r) ^ 3 := hcount'
      _ ≤ (3 * R / r) ^ 3 := hcount''
      _ = 27 * (R / r) ^ 3 := hcount'''
  exact ⟨N, c, hcenters, hdisjoint, hmax, hcoverVolume.1, hcountFinal⟩

end CKN.Foundation
