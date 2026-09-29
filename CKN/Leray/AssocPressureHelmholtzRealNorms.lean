-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRealRates
public import CKN.Foundation.HomogeneousSobolev
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Real-radius Helmholtz norm estimates

Radial tail bounds convert pointwise real-radius cutoff profiles to spatial
`L²` estimates.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Pointwise ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section
namespace CKN.Leray

def hpRealTail (x : Vec3) : ℝ := (1 + ‖x‖) ^ (-(6 : ℝ))
def hpRealExterior (R : ℝ) : Set Vec3 := {x | R ≤ ‖x‖}
def hpRealTailProfile (R : ℝ) : Vec3 → ℝ :=
  fun x => if R ≤ ‖x‖ then (1 + ‖x‖) ^ (-(3 : ℝ)) else 0

private theorem hpRealTailProfile_sq (R : ℝ) (x : Vec3) :
    hpRealTailProfile R x ^ 2 = (hpRealExterior R).indicator hpRealTail x := by
  unfold hpRealTailProfile
  split_ifs with hx
  · rw [Set.indicator_of_mem (show x ∈ hpRealExterior R from hx) hpRealTail]
    let a : ℝ := 1 + ‖x‖
    have ha : 0 < a := by dsimp [a]; positivity
    have hneg3 : a ^ (-(3 : ℝ)) = (a ^ (3 : ℕ))⁻¹ := by
      calc
        a ^ (-(3 : ℝ)) = (a ^ (3 : ℝ))⁻¹ := by rw [Real.rpow_neg ha.le]
        _ = (a ^ (3 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast a 3)
    have hneg6 : a ^ (-(6 : ℝ)) = (a ^ (6 : ℕ))⁻¹ := by
      calc
        a ^ (-(6 : ℝ)) = (a ^ (6 : ℝ))⁻¹ := by rw [Real.rpow_neg ha.le]
        _ = (a ^ (6 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast a 6)
    rw [hpRealTail]
    change ((1 + ‖x‖) ^ (-(3 : ℝ))) ^ (2 : ℕ) =
      (1 + ‖x‖) ^ (-(6 : ℝ))
    rw [show 1 + ‖x‖ = a by rfl, hneg3, hneg6]
    have hpow : ((a ^ (3 : ℕ))⁻¹) ^ (2 : ℕ) = (a ^ (6 : ℕ))⁻¹ := by
      field_simp [ne_of_gt ha]
    exact hpow
  · rw [Set.indicator_of_notMem (show x ∉ hpRealExterior R from hx) hpRealTail]
    norm_num

private theorem hpRealTail_integrable : Integrable hpRealTail (volume : Measure Vec3) := by
  change Integrable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ)))
    (volume : Measure Vec3)
  apply integrable_one_add_norm
  norm_num [Vec3]

private theorem hpRealTail_unitExterior_le (x : Vec3) (hx : x ∈ hpRealExterior 1) :
    ‖x‖ ^ (-(6 : ℝ)) ≤ 64 * hpRealTail x := by
  have hx1 : 1 ≤ ‖x‖ := hx
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
  have hsum : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith only [hx1]
  have hpow : (1 + ‖x‖) ^ (6 : ℕ) ≤ 64 * ‖x‖ ^ (6 : ℕ) := by
    calc
      (1 + ‖x‖) ^ 6 ≤ (2 * ‖x‖) ^ 6 := by gcongr
      _ = 64 * ‖x‖ ^ 6 := by norm_num [mul_pow]
  have hpow' : (1 + ‖x‖) ^ (6 : ℝ) ≤ 64 * ‖x‖ ^ (6 : ℝ) := by
    exact_mod_cast hpow
  have hrec : 1 / ‖x‖ ^ (6 : ℝ) ≤ 64 / (1 + ‖x‖) ^ (6 : ℝ) := by
    have hn1 : (‖x‖ ^ (6 : ℝ)) ≠ 0 := ne_of_gt (by positivity)
    have hn2 : ((1 + ‖x‖) ^ (6 : ℝ)) ≠ 0 := ne_of_gt (by positivity)
    field_simp [hn1, hn2]
    simpa [mul_comm] using hpow'
  have hneg (y : ℝ) (hy : 0 < y) : y ^ (-(6 : ℝ)) = 1 / y ^ (6 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hy), inv_eq_one_div]
  calc
    ‖x‖ ^ (-(6 : ℝ)) = 1 / ‖x‖ ^ (6 : ℝ) := hneg ‖x‖ hxpos
    _ ≤ 64 / (1 + ‖x‖) ^ (6 : ℝ) := hrec
    _ = 64 * hpRealTail x := by
      rw [hpRealTail, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), div_eq_mul_inv]

private theorem hpRealTail_scaled_unitExterior_le (R : ℝ) (hR : 1 ≤ R)
    (x : Vec3) (hx : x ∈ hpRealExterior 1) :
    hpRealTail (R • x) ≤ 64 * R ^ (-(6 : ℝ)) * hpRealTail x := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hnorm : ‖R • x‖ = R * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
  have hbase : R * ‖x‖ ≤ 1 + R * ‖x‖ := by
    have hOne : 0 ≤ (1 : ℝ) := by norm_num
    linarith only [hOne]
  have hpow : (1 + R * ‖x‖) ^ (-(6 : ℝ)) ≤ (R * ‖x‖) ^ (-(6 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by norm_num)
  have hmul : (R * ‖x‖) ^ (-(6 : ℝ)) =
      R ^ (-(6 : ℝ)) * ‖x‖ ^ (-(6 : ℝ)) := by
    rw [Real.mul_rpow hRpos.le hxpos.le]
  rw [hpRealTail, hnorm]
  calc
    (1 + R * ‖x‖) ^ (-(6 : ℝ)) ≤
        R ^ (-(6 : ℝ)) * ‖x‖ ^ (-(6 : ℝ)) := by rw [← hmul]; exact hpow
    _ ≤ R ^ (-(6 : ℝ)) * (64 * hpRealTail x) := by
      gcongr
      exact hpRealTail_unitExterior_le x hx
    _ = 64 * R ^ (-(6 : ℝ)) * hpRealTail x := by ring

private theorem hpRealExterior_scale (R : ℝ) (hR : 0 < R) :
    R • hpRealExterior 1 = hpRealExterior R := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hn : ‖R • y‖ = R * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    change R ≤ ‖R • y‖
    rw [hn]
    have hy' : 1 ≤ ‖y‖ := hy
    nlinarith only [hy', hR.le]
  · intro hx
    refine ⟨R⁻¹ • x, ?_, ?_⟩
    · have hn : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      change 1 ≤ ‖R⁻¹ • x‖
      rw [hn]
      change R ≤ ‖x‖ at hx
      have hx' : 1 ≤ ‖x‖ / R := by
        rw [le_div_iff₀ hR]
        simpa using hx
      simpa [div_eq_mul_inv, mul_comm] using hx'
    · change R • (R⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

private theorem hpRealTail_integral_exterior_bound_ge_one (R : ℝ) (hR : 1 ≤ R) :
    ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x, hpRealTail x ∂(volume : Measure Vec3) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hunitMeas : MeasurableSet (hpRealExterior 1) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hRMeas : MeasurableSet (hpRealExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hunitInt : IntegrableOn hpRealTail (hpRealExterior 1) (volume : Measure Vec3) :=
    hpRealTail_integrable.integrableOn
  have hscaledMeas : AEStronglyMeasurable
      (fun x : Vec3 => hpRealTail (R • x)) ((volume : Measure Vec3).restrict (hpRealExterior 1)) := by
    have hmeas : Measurable hpRealTail := by
      change Measurable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ)))
      fun_prop
    exact (hmeas.comp (measurable_const_smul R)).aestronglyMeasurable.restrict
  let c : ℝ := 64 * R ^ (-(6 : ℝ))
  have hc : 0 ≤ c := by positivity
  have hmajorInt : IntegrableOn (fun x : Vec3 => c * hpRealTail x)
      (hpRealExterior 1) (volume : Measure Vec3) :=
    (hpRealTail_integrable.const_mul c).integrableOn
  have hscaledInt : IntegrableOn (fun x : Vec3 => hpRealTail (R • x))
      (hpRealExterior 1) (volume : Measure Vec3) := by
    apply Integrable.mono' hmajorInt
    · exact hscaledMeas
    · filter_upwards [ae_restrict_mem hunitMeas] with x hx
      have hbound := hpRealTail_scaled_unitExterior_le R hR x hx
      have hnormA : ‖hpRealTail (R • x)‖ = hpRealTail (R • x) := by
        rw [Real.norm_eq_abs]
        change |(1 + ‖R • x‖) ^ (-(6 : ℝ))| = _
        rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        rfl
      have hnormB : ‖c * hpRealTail x‖ = c * hpRealTail x := by
        rw [Real.norm_eq_abs]
        change |c * ((1 + ‖x‖) ^ (-(6 : ℝ)))| = _
        rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg (by positivity) _))]
        rfl
      simpa [hnormA, hnormB, c] using hbound
  have hmono : ∫ x in hpRealExterior 1, hpRealTail (R • x) ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(6 : ℝ)) * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) := by
    calc
      _ ≤ ∫ x in hpRealExterior 1, c * hpRealTail x ∂(volume : Measure Vec3) :=
        setIntegral_mono_on hscaledInt hmajorInt hunitMeas (fun x hx => by
          have hbound := hpRealTail_scaled_unitExterior_le R hR x hx
          simpa [c] using hbound)
      _ = c * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) :=
        integral_const_mul _ _
      _ = _ := rfl
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure Vec3)) hpRealTail (hpRealExterior 1) hRpos
  rw [hpRealExterior_scale R hRpos] at hscale
  have hscale' : ∫ x in hpRealExterior 1, hpRealTail (R • x) ∂(volume : Measure Vec3) =
      R ^ (-(3 : ℝ)) * ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) := by
    simpa [Module.finrank_fin_fun, Vec3, Real.rpow_neg, abs_of_pos hRpos] using hscale
  have hmul : R ^ (-(3 : ℝ)) *
      ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(6 : ℝ)) * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) := by
    rw [← hscale']
    exact hmono
  have hpos : 0 < R ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hRpos _
  have htailUnit : ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) := by
    apply le_of_mul_le_mul_left ?_ hpos
    calc
      R ^ (-(3 : ℝ)) * ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
          64 * R ^ (-(6 : ℝ)) * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) := hmul
      _ = R ^ (-(3 : ℝ)) *
          (64 * R ^ (-(3 : ℝ)) * ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3)) := by
              have hpow : R ^ (-(6 : ℝ)) = R ^ (-(3 : ℝ)) * R ^ (-(3 : ℝ)) := by
                rw [← Real.rpow_add hRpos]
                norm_num
              rw [hpow]
              ring
  have hunitLe : ∫ x in hpRealExterior 1, hpRealTail x ∂(volume : Measure Vec3) ≤
      ∫ x, hpRealTail x ∂(volume : Measure Vec3) :=
    setIntegral_le_integral hpRealTail_integrable
      (Filter.Eventually.of_forall fun x => by
        change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
        exact Real.rpow_nonneg (by positivity) _)
  exact htailUnit.trans (mul_le_mul_of_nonneg_left hunitLe (by positivity))

private theorem hpRealTail_integral_exterior_bound (R : ℝ) (hR : 0 < R) :
    ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x, hpRealTail x ∂(volume : Measure Vec3) := by
  by_cases hRone : 1 ≤ R
  · exact hpRealTail_integral_exterior_bound_ge_one R hRone
  · have hRle : R ≤ 1 := le_of_not_ge hRone
    have htailLe : ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) ≤
        ∫ x, hpRealTail x ∂(volume : Measure Vec3) :=
      setIntegral_le_integral hpRealTail_integrable
        (Filter.Eventually.of_forall fun x => by
          change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
          exact Real.rpow_nonneg (by positivity) _)
    have honeLe : 1 ≤ R ^ (-(3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R)
        hRle (by norm_num : (-(3 : ℝ)) ≤ 0)
      simpa using h
    have htotal : 0 ≤ ∫ x, hpRealTail x ∂(volume : Measure Vec3) :=
      integral_nonneg fun x => by
        change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
        exact Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ ∫ x, hpRealTail x ∂(volume : Measure Vec3) := htailLe
      _ ≤ 64 * R ^ (-(3 : ℝ)) * ∫ x, hpRealTail x ∂(volume : Measure Vec3) := by
        have hfac : 1 ≤ 64 * R ^ (-(3 : ℝ)) := by nlinarith only [honeLe]
        simpa using mul_le_mul_of_nonneg_right hfac htotal

private theorem hpReal_eLpNorm_eq_ofReal_integral_rpow
    {f : Vec3 → ℝ} {r : ℝ} (hr : 0 < r)
    (hm : AEStronglyMeasurable f (volume : Measure Vec3))
    (h0 : ∀ x, 0 ≤ f x)
    (hint : Integrable (fun x => f x ^ r) (volume : Measure Vec3)) :
    eLpNorm f (ENNReal.ofReal r) (volume : Measure Vec3) =
      ENNReal.ofReal ((∫ x, f x ^ r ∂(volume : Measure Vec3)) ^ (1 / r)) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hmem : MemLp f (ENNReal.ofReal r) (volume : Measure Vec3) := by
    rw [← integrable_norm_rpow_iff hm hr0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr.le]
    refine hint.congr (Filter.Eventually.of_forall fun a => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (h0 a)]
  rw [hmem.eLpNorm_eq_integral_rpow_norm hr0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le, one_div]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with a
  simp only [Real.norm_eq_abs, abs_of_nonneg (h0 a)]

private theorem hpRealTailProfile_memLp (R : ℝ) :
    MemLp (hpRealTailProfile R) (2 : ℝ≥0∞) (volume : Measure Vec3) := by
  have hset : MeasurableSet (hpRealExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hfmeas : AEStronglyMeasurable (hpRealTailProfile R) (volume : Measure Vec3) := by
    have hm : Measurable (hpRealTailProfile R) := by
      unfold hpRealTailProfile
      apply Measurable.ite
        (measurableSet_le continuous_const.measurable continuous_norm.measurable)
      · fun_prop
      · exact measurable_const
    exact hm.aestronglyMeasurable
  have hprofNonneg (x : Vec3) : 0 ≤ hpRealTailProfile R x := by
    unfold hpRealTailProfile
    split_ifs <;> positivity
  have hsq : Integrable (fun x : Vec3 => (hpRealTailProfile R x) ^ 2)
      (volume : Measure Vec3) := by
    have hmajor : Integrable ((hpRealExterior R).indicator hpRealTail) (volume : Measure Vec3) :=
      hpRealTail_integrable.indicator hset
    apply hmajor.congr
    filter_upwards [] with x
    exact (hpRealTailProfile_sq R x).symm
  have hnormSq : Integrable (fun x : Vec3 => ‖hpRealTailProfile R x‖ ^ 2)
      (volume : Measure Vec3) := by
    apply hsq.congr
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hprofNonneg x)]
  exact (memLp_two_iff_integrable_sq_norm hfmeas).2 hnormSq

private theorem hpRealTailProfile_eLpNorm_le (R : ℝ) (hR : 0 < R) :
    eLpNorm (hpRealTailProfile R) 2 (volume : Measure Vec3) ≤
      ENNReal.ofReal
        (8 * Real.sqrt (∫ x, hpRealTail x ∂(volume : Measure Vec3)) *
          R ^ (-(3 / 2 : ℝ))) := by
  have hset : MeasurableSet (hpRealExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hmem := hpRealTailProfile_memLp R
  have hprofileNonneg (x : Vec3) : 0 ≤ hpRealTailProfile R x := by
    unfold hpRealTailProfile
    split_ifs <;> positivity
  have hIntEq : ∫ x : Vec3, (hpRealTailProfile R x) ^ 2 ∂(volume : Measure Vec3) =
      ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) := by
    calc
      _ = ∫ x : Vec3, (hpRealExterior R).indicator hpRealTail x ∂(volume : Measure Vec3) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpRealTailProfile_sq R x
      _ = ∫ x in hpRealExterior R, hpRealTail x ∂(volume : Measure Vec3) := integral_indicator hset
  have htail := hpRealTail_integral_exterior_bound R hR
  have htotal : 0 ≤ ∫ x, hpRealTail x ∂(volume : Measure Vec3) := by
    apply integral_nonneg
    intro x
    change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
    exact Real.rpow_nonneg (by positivity) _
  have hsqNorm : Integrable (fun x : Vec3 => ‖hpRealTailProfile R x‖ ^ (2 : ℝ))
      (volume : Measure Vec3) :=
    hmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hsq : Integrable (fun x : Vec3 => hpRealTailProfile R x ^ (2 : ℝ))
      (volume : Measure Vec3) := by
    apply hsqNorm.congr
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hprofileNonneg x)]
  have hnorm := hpReal_eLpNorm_eq_ofReal_integral_rpow
    (f := hpRealTailProfile R) (r := 2) (by norm_num) hmem.aestronglyMeasurable
    (fun x => hprofileNonneg x)
    (by exact hsq)
  have hnorm' : eLpNorm (hpRealTailProfile R) 2 (volume : Measure Vec3) =
      ENNReal.ofReal ((∫ x, (hpRealTailProfile R x) ^ 2 ∂(volume : Measure Vec3)) ^
        (1 / (2 : ℝ))) := by
    simpa using hnorm
  rw [hnorm']
  apply ENNReal.ofReal_le_ofReal
  rw [hIntEq]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt := Real.sqrt_le_sqrt htail
  have hroot : Real.sqrt (64 * R ^ (-(3 : ℝ)) *
      ∫ x, hpRealTail x ∂(volume : Measure Vec3)) =
      8 * Real.sqrt (∫ x, hpRealTail x ∂(volume : Measure Vec3)) *
        R ^ (-(3 / 2 : ℝ)) := by
    let I := ∫ x, hpRealTail x ∂(volume : Measure Vec3)
    have h64 : Real.sqrt (64 * I) = 8 * Real.sqrt I := by
      rw [Real.sqrt_mul (by norm_num)]
      have hs64 : Real.sqrt (64 : ℝ) = 8 :=
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
      rw [hs64]
    have hRroot : Real.sqrt (R ^ (-(3 : ℝ))) = R ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
      congr 1
      norm_num
    calc
      Real.sqrt (64 * R ^ (-(3 : ℝ)) * I) =
          Real.sqrt ((64 * I) * R ^ (-(3 : ℝ))) := by ring_nf
      _ = Real.sqrt (64 * I) * Real.sqrt (R ^ (-(3 : ℝ))) :=
        Real.sqrt_mul (by positivity) _
      _ = 8 * Real.sqrt I * R ^ (-(3 / 2 : ℝ)) := by rw [h64, hRroot]
  exact hsqrt.trans_eq hroot

private theorem hp_eLpNorm_le_of_tail_profile
    {f : Vec3 → ℝ} (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f (volume : Measure Vec3))
    (hpoint : ∀ x, |f x| ≤ C * hpRealTailProfile R x) :
    eLpNorm f 2 (volume : Measure Vec3) ≤
      ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * R ^ (-(3 / 2 : ℝ))) := by
  have hmajorEq : (fun x : Vec3 => C * hpRealTailProfile R x) =
      C • hpRealTailProfile R := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  calc
    eLpNorm f 2 (volume : Measure Vec3) ≤
        eLpNorm (fun x : Vec3 => C * hpRealTailProfile R x) 2
          (volume : Measure Vec3) :=
      eLpNorm_mono_ae_real hf (Filter.Eventually.of_forall hpoint)
    _ = ENNReal.ofReal C * eLpNorm (hpRealTailProfile R) 2
        (volume : Measure Vec3) := by
      rw [hmajorEq, eLpNorm_const_smul, Real.enorm_of_nonneg hC]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * R ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hpRealTailProfile_eLpNorm_le R hR) (by positivity)

/- Real-radius component bounds -/

/-- Each fixed-time component of the real-radius cutoff curl time derivative
has the `R⁻³ᐟ²` spatial `L²` error rate in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurlReal_timePartial_component_eLpNorm_error_le
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (t : ℝ) (i : Fin 3),
      eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) (x, t) -
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) w i) (x, t))
        2 (volume : Measure Vec3) ≤
        ENNReal.ofReal C * ENNReal.ofReal
          (associatedPressureHelmholtzTailL2Constant *
            (R / 2) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_timePartial_error_profile hφ
  refine ⟨C, hC, ?_⟩
  intro R hR t i
  let ρ := R / 2
  let f : Vec3 → ℝ := fun x =>
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) (x, t) -
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) w i) (x, t)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hcut : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) z i) :=
    (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
          hφ R hR).1)
  have hbase : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z i) :=
    (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hcutT : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) z) :=
    CKN.contDiff_timePartial hcut
  have hbaseT : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i) z) :=
    CKN.contDiff_timePartial hbase
  have hspaceCont : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hdiff := hcutT.sub hbaseT
    dsimp [f]
    exact hdiff.comp
      (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
  have hfae : AEStronglyMeasurable f (volume : Measure Vec3) :=
    hspaceCont.continuous.measurable.aestronglyMeasurable
  have hpoint (x : Vec3) : |f x| ≤ C * hpRealTailProfile ρ x := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile R hR (x, t) i
      have hnorm := norm_le_vec3EuclideanNorm x
      have hdecay : (1 + vec3EuclideanNorm x) ^ (-(3 : ℝ)) ≤
          (1 + ‖x‖) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith only [hnorm]) (by norm_num)
      have hprofileEq : hpRealTailProfile ρ x = (1 + ‖x‖) ^ (-(3 : ℝ)) := by
        unfold hpRealTailProfile
        split_ifs; simp_all
      rw [hprofileEq]
      dsimp [f] at herr ⊢
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
      have heq := associatedPressureHelmholtzCutoffCurlReal_timePartial_eq_of_inner
        hφ R hR i (x, t) hxBall
      have hz : f x = 0 := by dsimp [f]; exact sub_eq_zero.mpr heq
      have hprofileZero : hpRealTailProfile ρ x = 0 := by
        unfold hpRealTailProfile
        split_ifs; simp_all
      rw [hz, hprofileZero]
      simp
  simpa [f, ρ] using hp_eLpNorm_le_of_tail_profile ρ hρpos C hC hfae hpoint

/-- Each fixed-time component of the spatial derivative of the real-radius
cutoff curl has the spatial `L²` tail rate in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurlReal_spatialPartial_component_eLpNorm_error_le
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (R : ℝ) (hR : 1 ≤ R) (t : ℝ) (i j : Fin 3),
      eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3) ≤
        ENNReal.ofReal C * ENNReal.ofReal
          (associatedPressureHelmholtzTailL2Constant *
            (R / 2) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurlReal_spatialPartial_error_profile hφ
  refine ⟨C, hC, ?_⟩
  intro R hR t i j
  let ρ := R / 2
  let A := associatedPressureHelmholtzVectorPotential φ
  let f : Vec3 → ℝ := fun x =>
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) q i) j (x, t) -
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl A q i) j (x, t)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) :=
    (associatedPressureHelmholtzCutoffVectorPotentialReal_mem_spaceTimeTestFunction
      hφ R hR).1
  have hbaseA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hcutCurl : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR)) :=
    associatedPressureTestCurl_contDiff hcutA
  have hbaseCurl : ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestCurl A) :=
    associatedPressureTestCurl_contDiff hbaseA
  have hcutPart : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => CKN.spatialPartialProd
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotentialReal φ R hR) w i) j q) :=
    CKN.spatialPartial_contDiff ((contDiff_apply ℝ ℝ i).comp hcutCurl) j
  have hbasePart : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => CKN.spatialPartialProd
        (fun w => associatedPressureTestCurl A w i) j q) :=
    CKN.spatialPartial_contDiff ((contDiff_apply ℝ ℝ i).comp hbaseCurl) j
  have hspaceCont : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hdiff := hcutPart.sub hbasePart
    dsimp [f]
    exact hdiff.comp
      (contDiff_prodMk_left (𝕜 := ℝ) (n := (⊤ : ℕ∞)) t)
  have hfae : AEStronglyMeasurable f (volume : Measure Vec3) :=
    hspaceCont.continuous.measurable.aestronglyMeasurable
  have hpoint (x : Vec3) : |f x| ≤ C * hpRealTailProfile ρ x := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile R hR (x, t) i j
      have hx0 : 1 ≤ 1 + ‖x‖ := by
        have hn := norm_nonneg x
        linarith only [hn]
      have hdecay : (1 + ‖x‖) ^ (-(4 : ℝ)) ≤
          (1 + ‖x‖) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx0 (by norm_num)
      have hprofileEq : hpRealTailProfile ρ x = (1 + ‖x‖) ^ (-(3 : ℝ)) := by
        unfold hpRealTailProfile
        split_ifs; simp_all
      rw [hprofileEq]
      dsimp [f, A] at herr ⊢
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
        A hbaseA R hR (x, t) i j hxBall hxClosed
      have hz : f x = 0 := by
        dsimp [f, A]
        exact sub_eq_zero.mpr heq
      have hprofileZero : hpRealTailProfile ρ x = 0 := by
        unfold hpRealTailProfile
        split_ifs; simp_all
      rw [hz, hprofileZero]
      simp
  simpa [f, ρ] using hp_eLpNorm_le_of_tail_profile ρ hρpos C hC hfae hpoint

end CKN.Leray

end
