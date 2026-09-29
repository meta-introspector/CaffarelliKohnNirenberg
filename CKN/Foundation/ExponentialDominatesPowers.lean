-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter
open scoped Topology

set_option autoImplicit false

namespace CKN.Foundation

/-- Near zero, a decaying exponential is bounded by any prescribed positive
power. The estimate is used in `lem:uc-gaussian` of the Escauriaza–Seregin–Šverák manuscript and `thm:uc` of the Escauriaza–Seregin–Šverák manuscript. -/
theorem exp_neg_div_le_rpow_of_small {c q : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      Real.exp (-c / τ) ≤ τ ^ q := by
  let g : ℝ → ℝ := fun x => x ^ q * Real.exp (-c * x)
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q c hc
  have hEventually : ∀ᶠ x : ℝ in atTop, g x < 1 := by
    exact hg.eventually (isOpen_Iio.mem_nhds (by norm_num))
  obtain ⟨X, hX⟩ := (eventually_atTop.1 hEventually)
  let T : ℝ := max X 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  refine ⟨T⁻¹, inv_pos.mpr hT, ?_⟩
  intro τ hτ hτT
  have hτinv : T ≤ τ⁻¹ := by
    rw [← inv_inv T]
    exact (inv_le_inv₀ (inv_pos.mpr hT) hτ).2 hτT
  have hXT : X ≤ T := le_max_left _ _
  have hsmall : g (τ⁻¹) < 1 := hX (τ⁻¹) (hXT.trans hτinv)
  have hpowpos : 0 < τ ^ q := Real.rpow_pos_of_pos hτ q
  have hpowinv : (τ⁻¹) ^ q = (τ ^ q)⁻¹ := by
    calc
      (τ⁻¹) ^ q = τ ^ (-q) := (Real.rpow_neg_eq_inv_rpow τ q).symm
      _ = (τ ^ q)⁻¹ := Real.rpow_neg hτ.le q
  have hmul : (τ ^ q)⁻¹ * Real.exp (-c / τ) < 1 := by
    simpa [g, hpowinv, div_eq_mul_inv, mul_comm] using hsmall
  have hfinal := mul_lt_mul_of_pos_left hmul hpowpos
  have hlt : Real.exp (-c / τ) < τ ^ q := by
    simpa [mul_assoc, hpowpos.ne'] using hfinal
  exact hlt.le

/-- The dyadic exponential tail used in the initial-time error estimate is
smaller than every positive power of the starting scale, as required in
`lem:uc-gaussian` (ESS) and `thm:uc` (ESS). -/
theorem dyadic_exp_tail_le_rpow {p q c : ℝ} (hq : 0 < q) (hc : 0 < c) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Summable (fun j : ℕ =>
        (ε * (2 : ℝ) ^ (-(j : ℝ))) ^ (-p) *
          Real.exp (-c / (ε * (2 : ℝ) ^ (-(j : ℝ))))) ∧
      ∑' j : ℕ,
        (ε * (2 : ℝ) ^ (-(j : ℝ))) ^ (-p) *
          Real.exp (-c / (ε * (2 : ℝ) ^ (-(j : ℝ)))) ≤ C * ε ^ q := by
  obtain ⟨δ, hδ, hbound⟩ := exp_neg_div_le_rpow_of_small hc
  let ε₀ := min δ 1
  let C := (1 - (2 : ℝ) ^ (-q))⁻¹
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    have hpow : (2 : ℝ) ^ (-q) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hq])
    exact inv_pos.mpr (sub_pos.mpr hpow)
  refine ⟨ε₀, C, hε₀, hC, ?_⟩
  intro ε hε hεle
  have hεδ : ε ≤ δ := hεle.trans (min_le_left _ _)
  let a : ℕ → ℝ := fun j => ε * (2 : ℝ) ^ (-(j : ℝ))
  let ratio : ℝ := (2 : ℝ) ^ (-q)
  let t : ℕ → ℝ := fun j => ratio ^ j
  have haPos (j : ℕ) : 0 < a j := by
    dsimp [a]
    positivity
  have haLe (j : ℕ) : a j ≤ ε := by
    dsimp [a]
    have hpow : (2 : ℝ) ^ (-(j : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (neg_nonpos.mpr (by positivity))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hε.le
  have hfactor (j : ℕ) : a j ^ q = ε ^ q * t j := by
    have hpow2 : ((2 : ℝ) ^ (-(j : ℝ))) ^ q =
        ((2 : ℝ) ^ (-q)) ^ j := by
      rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
      congr 1
      ring
    dsimp [a, t, ratio]
    rw [Real.mul_rpow hε.le (Real.rpow_nonneg (by norm_num) _), hpow2]
  have hterm (j : ℕ) :
      a j ^ (-p) * Real.exp (-c / a j) ≤ ε ^ q * t j := by
    have hexp := hbound (a j) (haPos j) (haLe j |>.trans hεδ)
    have hpow := Real.rpow_nonneg (haPos j).le (-p)
    calc
      a j ^ (-p) * Real.exp (-c / a j) ≤ a j ^ (-p) * a j ^ (p + q) :=
        mul_le_mul_of_nonneg_left hexp hpow
      _ = a j ^ q := by
        rw [← Real.rpow_add (haPos j)]
        ring_nf
      _ = ε ^ q * t j := hfactor j
  have hratio : ratio < 1 := by
    dsimp [ratio]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hq])
  have ht : Summable t := by
    dsimp [t]
    exact summable_geometric_of_lt_one (by positivity) hratio
  have htsum : ∑' j : ℕ, t j = C := by
    dsimp [t, C, ratio]
    exact tsum_geometric_of_lt_one (by positivity) hratio
  have hmajor : Summable (fun j : ℕ => ε ^ q * t j) := ht.mul_left (ε ^ q)
  have hsum : Summable (fun j : ℕ => a j ^ (-p) * Real.exp (-c / a j)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (haPos j).le _)
      (Real.exp_nonneg _)) (fun j => hterm j) hmajor
  constructor
  · simpa only [a] using hsum
  · change ∑' j : ℕ, a j ^ (-p) * Real.exp (-c / a j) ≤ C * ε ^ q
    calc
      ∑' j : ℕ, a j ^ (-p) * Real.exp (-c / a j) ≤ ∑' j : ℕ, ε ^ q * t j :=
        hsum.tsum_le_tsum (fun j => hterm j) hmajor
      _ = ε ^ q * ∑' j : ℕ, t j := tsum_mul_left
      _ = ε ^ q * C := by rw [htsum]
      _ = C * ε ^ q := by ring

end CKN.Foundation
