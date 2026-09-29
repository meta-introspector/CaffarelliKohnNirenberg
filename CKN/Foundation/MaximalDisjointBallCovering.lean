-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.Parabolic.BallDisplays
public import CKN.Foundation.Parabolic.Topology
public import CKN.Foundation.Parabolic.Vec3Norm
public import Mathlib.MeasureTheory.Measure.NullMeasurable

@[expose] public section

open MeasureTheory
open Set
open CKN.Foundation.Parabolic
open scoped ENNReal

set_option autoImplicit false

namespace CKN.Foundation

/-- A finite maximal family of equal-radius disjoint balls covers its center
region after doubling the radius, and its cardinality times the ball volume is
bounded by the volume of the enclosing ball. This is the packing estimate used
in `thm:uc` of the Escauriaza–Seregin–Šverák manuscript. -/
theorem finite_maximal_equal_radius_ball_cover
    {N : ℕ} (x₀ : Vec3) {R r : ℝ} (c : Fin N → Vec3)
    (hcenters : ∀ i, c i ∈ vec3Ball x₀ R)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (vec3Ball (c i) (r / 2)) (vec3Ball (c j) (r / 2)))
    (hmax : ∀ x, x ∈ vec3Ball x₀ R →
      ¬ ∀ i, r ≤ vec3EuclideanNorm (x - c i)) :
    (∀ x, x ∈ vec3Ball x₀ R →
      ∃ i, x ∈ vec3Ball (c i) r) ∧
    (N : ℝ≥0∞) *
        ((ENNReal.ofReal (r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) ≤
      (ENNReal.ofReal (R + r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  have hcover : ∀ x, x ∈ vec3Ball x₀ R → ∃ i, x ∈ vec3Ball (c i) r := by
    intro x hx
    by_contra hnone
    apply hmax x hx
    intro i
    have hnot : ¬ vec3EuclideanNorm (x - c i) < r := by
      intro hlt
      exact hnone ⟨i, hlt⟩
    exact le_of_not_gt hnot
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
    rcases Set.mem_iUnion.mp (show x ∈ ⋃ i : Fin N, vec3Ball (c i) (r / 2) from hx)
      with ⟨i, hx⟩
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
  have hsumMeasure' :
      (N : ℝ≥0∞) *
          ((ENNReal.ofReal (r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3)) ≤
        (ENNReal.ofReal (R + r / 2)) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
    simpa only [volume_vec3Ball_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, tsum_fintype] using hsumMeasure
  exact ⟨hcover, hsumMeasure'⟩

end CKN.Foundation
