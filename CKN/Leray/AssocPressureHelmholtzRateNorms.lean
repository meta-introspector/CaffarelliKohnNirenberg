-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureHelmholtzRates
public import CKN.Leray.AssocPressureSolenoidalTimeLimit
public import CKN.Foundation.HomogeneousSobolev
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Helmholtz cutoff norm rates

Three-dimensional radial tail estimates convert the pointwise cutoff bounds
in `lem:helmholtz-test` to spatial `L²` estimates.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section
namespace CKN.Leray

def hpTail (x : Vec3) : ℝ := (1 + ‖x‖) ^ (-(6 : ℝ))
def hpExterior (R : ℝ) : Set Vec3 := {x | R ≤ ‖x‖}
def hpTailProfile (R : ℝ) : Vec3 → ℝ :=
  fun x => if R ≤ ‖x‖ then (1 + ‖x‖) ^ (-(3 : ℝ)) else 0

/-- The universal radial tail factor for three-dimensional cubic decay. -/
def associatedPressureHelmholtzTailL2Constant : ℝ :=
  8 * Real.sqrt (∫ x, hpTail x ∂(volume : Measure Vec3))

private theorem hpTailProfile_sq (R : ℝ) (x : Vec3) :
    hpTailProfile R x ^ 2 = (hpExterior R).indicator hpTail x := by
  unfold hpTailProfile
  split_ifs with hx
  · rw [Set.indicator_of_mem (show x ∈ hpExterior R from hx) hpTail]
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
    rw [hpTail]
    change ((1 + ‖x‖) ^ (-(3 : ℝ))) ^ (2 : ℕ) =
      (1 + ‖x‖) ^ (-(6 : ℝ))
    rw [show 1 + ‖x‖ = a by rfl, hneg3, hneg6]
    have hpow : ((a ^ (3 : ℕ))⁻¹) ^ (2 : ℕ) = (a ^ (6 : ℕ))⁻¹ := by
      field_simp [ne_of_gt ha]
    exact hpow
  · rw [Set.indicator_of_notMem (show x ∉ hpExterior R from hx) hpTail]
    norm_num

private theorem hpTail_integrable : Integrable hpTail (volume : Measure Vec3) := by
  change Integrable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ)))
    (volume : Measure Vec3)
  apply integrable_one_add_norm
  norm_num [Vec3]

private theorem hpTail_unitExterior_le (x : Vec3) (hx : x ∈ hpExterior 1) :
    ‖x‖ ^ (-(6 : ℝ)) ≤ 64 * hpTail x := by
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
    _ = 64 * hpTail x := by
      rw [hpTail, Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), div_eq_mul_inv]

private theorem hpTail_scaled_unitExterior_le (R : ℝ) (hR : 1 ≤ R)
    (x : Vec3) (hx : x ∈ hpExterior 1) :
    hpTail (R • x) ≤ 64 * R ^ (-(6 : ℝ)) * hpTail x := by
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
  rw [hpTail, hnorm]
  calc
    (1 + R * ‖x‖) ^ (-(6 : ℝ)) ≤
        R ^ (-(6 : ℝ)) * ‖x‖ ^ (-(6 : ℝ)) := by rw [← hmul]; exact hpow
    _ ≤ R ^ (-(6 : ℝ)) * (64 * hpTail x) := by
      gcongr
      exact hpTail_unitExterior_le x hx
    _ = 64 * R ^ (-(6 : ℝ)) * hpTail x := by ring

private theorem hpExterior_scale (R : ℝ) (hR : 0 < R) :
    R • hpExterior 1 = hpExterior R := by
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

private theorem hpTail_integral_exterior_bound_ge_one (R : ℝ) (hR : 1 ≤ R) :
    ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x, hpTail x ∂(volume : Measure Vec3) := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hunitMeas : MeasurableSet (hpExterior 1) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hRMeas : MeasurableSet (hpExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hunitInt : IntegrableOn hpTail (hpExterior 1) (volume : Measure Vec3) :=
    hpTail_integrable.integrableOn
  have hscaledMeas : AEStronglyMeasurable
      (fun x : Vec3 => hpTail (R • x)) ((volume : Measure Vec3).restrict (hpExterior 1)) := by
    have hmeas : Measurable hpTail := by
      change Measurable (fun x : Vec3 => (1 + ‖x‖) ^ (-(6 : ℝ)))
      fun_prop
    exact (hmeas.comp (measurable_const_smul R)).aestronglyMeasurable.restrict
  let c : ℝ := 64 * R ^ (-(6 : ℝ))
  have hc : 0 ≤ c := by positivity
  have hmajorInt : IntegrableOn (fun x : Vec3 => c * hpTail x)
      (hpExterior 1) (volume : Measure Vec3) :=
    (hpTail_integrable.const_mul c).integrableOn
  have hscaledInt : IntegrableOn (fun x : Vec3 => hpTail (R • x))
      (hpExterior 1) (volume : Measure Vec3) := by
    apply Integrable.mono' hmajorInt
    · exact hscaledMeas
    · filter_upwards [ae_restrict_mem hunitMeas] with x hx
      have hbound := hpTail_scaled_unitExterior_le R hR x hx
      have hnormA : ‖hpTail (R • x)‖ = hpTail (R • x) := by
        rw [Real.norm_eq_abs]
        change |(1 + ‖R • x‖) ^ (-(6 : ℝ))| = _
        rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        rfl
      have hnormB : ‖c * hpTail x‖ = c * hpTail x := by
        rw [Real.norm_eq_abs]
        change |c * ((1 + ‖x‖) ^ (-(6 : ℝ)))| = _
        rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg (by positivity) _))]
        rfl
      simpa [hnormA, hnormB, c] using hbound
  have hmono : ∫ x in hpExterior 1, hpTail (R • x) ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(6 : ℝ)) * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) := by
    calc
      _ ≤ ∫ x in hpExterior 1, c * hpTail x ∂(volume : Measure Vec3) :=
        setIntegral_mono_on hscaledInt hmajorInt hunitMeas (fun x hx => by
          have hbound := hpTail_scaled_unitExterior_le R hR x hx
          simpa [c] using hbound)
      _ = c * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) :=
        integral_const_mul _ _
      _ = _ := rfl
  have hscale := Measure.setIntegral_comp_smul_of_pos
    (μ := (volume : Measure Vec3)) hpTail (hpExterior 1) hRpos
  rw [hpExterior_scale R hRpos] at hscale
  have hscale' : ∫ x in hpExterior 1, hpTail (R • x) ∂(volume : Measure Vec3) =
      R ^ (-(3 : ℝ)) * ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) := by
    simpa [Module.finrank_fin_fun, Vec3, Real.rpow_neg, abs_of_pos hRpos] using hscale
  have hmul : R ^ (-(3 : ℝ)) *
      ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(6 : ℝ)) * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) := by
    rw [← hscale']
    exact hmono
  have hpos : 0 < R ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hRpos _
  have htailUnit : ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) := by
    apply le_of_mul_le_mul_left ?_ hpos
    calc
      R ^ (-(3 : ℝ)) * ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
          64 * R ^ (-(6 : ℝ)) * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) := hmul
      _ = R ^ (-(3 : ℝ)) *
          (64 * R ^ (-(3 : ℝ)) * ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3)) := by
              have hpow : R ^ (-(6 : ℝ)) = R ^ (-(3 : ℝ)) * R ^ (-(3 : ℝ)) := by
                rw [← Real.rpow_add hRpos]
                norm_num
              rw [hpow]
              ring
  have hunitLe : ∫ x in hpExterior 1, hpTail x ∂(volume : Measure Vec3) ≤
      ∫ x, hpTail x ∂(volume : Measure Vec3) :=
    setIntegral_le_integral hpTail_integrable
      (Filter.Eventually.of_forall fun x => by
        change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
        exact Real.rpow_nonneg (by positivity) _)
  exact htailUnit.trans (mul_le_mul_of_nonneg_left hunitLe (by positivity))

private theorem hpTail_integral_exterior_bound (R : ℝ) (hR : 0 < R) :
    ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
      64 * R ^ (-(3 : ℝ)) * ∫ x, hpTail x ∂(volume : Measure Vec3) := by
  by_cases hRone : 1 ≤ R
  · exact hpTail_integral_exterior_bound_ge_one R hRone
  · have hRle : R ≤ 1 := le_of_not_ge hRone
    have htailLe : ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) ≤
        ∫ x, hpTail x ∂(volume : Measure Vec3) :=
      setIntegral_le_integral hpTail_integrable
        (Filter.Eventually.of_forall fun x => by
          change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
          exact Real.rpow_nonneg (by positivity) _)
    have honeLe : 1 ≤ R ^ (-(3 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R)
        hRle (by norm_num : (-(3 : ℝ)) ≤ 0)
      simpa using h
    have htotal : 0 ≤ ∫ x, hpTail x ∂(volume : Measure Vec3) :=
      integral_nonneg fun x => by
        change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
        exact Real.rpow_nonneg (by positivity) _
    calc
      _ ≤ ∫ x, hpTail x ∂(volume : Measure Vec3) := htailLe
      _ ≤ 64 * R ^ (-(3 : ℝ)) * ∫ x, hpTail x ∂(volume : Measure Vec3) := by
        have hfac : 1 ≤ 64 * R ^ (-(3 : ℝ)) := by nlinarith only [honeLe]
        simpa using mul_le_mul_of_nonneg_right hfac htotal

private theorem hp_eLpNorm_eq_ofReal_integral_rpow {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {r : ℝ} (hr : 0 < r)
    (hm : AEStronglyMeasurable f μ) (h0 : ∀ a, 0 ≤ f a)
    (hint : Integrable (fun a => f a ^ r) μ) :
    eLpNorm f (ENNReal.ofReal r) μ = ENNReal.ofReal ((∫ a, f a ^ r ∂μ) ^ (1 / r)) := by
  have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  have hmem : MemLp f (ENNReal.ofReal r) μ := by
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

private theorem hpTailProfile_memLp (R : ℝ) :
    MemLp (hpTailProfile R) (2 : ℝ≥0∞) (volume : Measure Vec3) := by
  have hset : MeasurableSet (hpExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hfmeas : AEStronglyMeasurable (hpTailProfile R) (volume : Measure Vec3) := by
    have hm : Measurable (hpTailProfile R) := by
      unfold hpTailProfile
      apply Measurable.ite
        (measurableSet_le continuous_const.measurable continuous_norm.measurable)
      · fun_prop
      · exact measurable_const
    exact hm.aestronglyMeasurable
  have hprofNonneg (x : Vec3) : 0 ≤ hpTailProfile R x := by
    unfold hpTailProfile
    split_ifs <;> positivity
  have hsq : Integrable (fun x : Vec3 => (hpTailProfile R x) ^ 2)
      (volume : Measure Vec3) := by
    have hmajor : Integrable ((hpExterior R).indicator hpTail) (volume : Measure Vec3) :=
      hpTail_integrable.indicator hset
    apply hmajor.congr
    filter_upwards [] with x
    exact (hpTailProfile_sq R x).symm
  have hnormSq : Integrable (fun x : Vec3 => ‖hpTailProfile R x‖ ^ 2)
      (volume : Measure Vec3) := by
    apply hsq.congr
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hprofNonneg x)]
  exact (memLp_two_iff_integrable_sq_norm hfmeas).2 hnormSq

private theorem hpTailProfile_eLpNorm_le (R : ℝ) (hR : 0 < R) :
    eLpNorm (hpTailProfile R) 2 (volume : Measure Vec3) ≤
      ENNReal.ofReal
        (8 * Real.sqrt (∫ x, hpTail x ∂(volume : Measure Vec3)) *
          R ^ (-(3 / 2 : ℝ))) := by
  have hset : MeasurableSet (hpExterior R) :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have hmem := hpTailProfile_memLp R
  have hprofileNonneg (x : Vec3) : 0 ≤ hpTailProfile R x := by
    unfold hpTailProfile
    split_ifs <;> positivity
  have hIntEq : ∫ x : Vec3, (hpTailProfile R x) ^ 2 ∂(volume : Measure Vec3) =
      ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) := by
    calc
      _ = ∫ x : Vec3, (hpExterior R).indicator hpTail x ∂(volume : Measure Vec3) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hpTailProfile_sq R x
      _ = ∫ x in hpExterior R, hpTail x ∂(volume : Measure Vec3) := integral_indicator hset
  have htail := hpTail_integral_exterior_bound R hR
  have htotal : 0 ≤ ∫ x, hpTail x ∂(volume : Measure Vec3) := by
    apply integral_nonneg
    intro x
    change 0 ≤ (1 + ‖x‖) ^ (-(6 : ℝ))
    exact Real.rpow_nonneg (by positivity) _
  have hsqNorm : Integrable (fun x : Vec3 => ‖hpTailProfile R x‖ ^ (2 : ℝ))
      (volume : Measure Vec3) :=
    hmem.integrable_norm_rpow (by norm_num) (by norm_num)
  have hsq : Integrable (fun x : Vec3 => hpTailProfile R x ^ (2 : ℝ))
      (volume : Measure Vec3) := by
    apply hsqNorm.congr
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hprofileNonneg x)]
  have hnorm := hp_eLpNorm_eq_ofReal_integral_rpow (μ := (volume : Measure Vec3))
    (f := hpTailProfile R) (r := 2) (by norm_num) hmem.aestronglyMeasurable
    (fun x => hprofileNonneg x)
    (by exact hsq)
  have hnorm' : eLpNorm (hpTailProfile R) 2 (volume : Measure Vec3) =
      ENNReal.ofReal ((∫ x, (hpTailProfile R x) ^ 2 ∂(volume : Measure Vec3)) ^
        (1 / (2 : ℝ))) := by
    simpa using hnorm
  rw [hnorm']
  apply ENNReal.ofReal_le_ofReal
  rw [hIntEq]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt := Real.sqrt_le_sqrt htail
  have hroot : Real.sqrt (64 * R ^ (-(3 : ℝ)) *
      ∫ x, hpTail x ∂(volume : Measure Vec3)) =
      8 * Real.sqrt (∫ x, hpTail x ∂(volume : Measure Vec3)) *
        R ^ (-(3 / 2 : ℝ)) := by
    let I := ∫ x, hpTail x ∂(volume : Measure Vec3)
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
    (hpoint : ∀ x, |f x| ≤ C * hpTailProfile R x) :
    eLpNorm f 2 (volume : Measure Vec3) ≤
      ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * R ^ (-(3 / 2 : ℝ))) := by
  have hmajorEq : (fun x : Vec3 => C * hpTailProfile R x) =
      C • hpTailProfile R := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
  calc
    eLpNorm f 2 (volume : Measure Vec3) ≤
        eLpNorm (fun x : Vec3 => C * hpTailProfile R x) 2
          (volume : Measure Vec3) :=
      eLpNorm_mono_ae_real hf (Filter.Eventually.of_forall hpoint)
    _ = ENNReal.ofReal C * eLpNorm (hpTailProfile R) 2
        (volume : Measure Vec3) := by
      rw [hmajorEq, eLpNorm_const_smul, Real.enorm_of_nonneg hC]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal
        (associatedPressureHelmholtzTailL2Constant * R ^ (-(3 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hpTailProfile_eLpNorm_le R hR) (by positivity)

private theorem hp_cutoffCurl_error_profile
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (D : Fin 3 → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hdirErr : ∀ (k l : Fin 3) (n : ℕ) (z : Vec3 × ℝ),
      |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z -
        rieszPressureJointDirection (fun q => A q k) l z| ≤
        D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ))) :
    ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3),
      |associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • A q) z i -
        associatedPressureTestCurl A z i| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let C : ℝ := 2 * ∑ k : Fin 3, D k
  have hsum : 0 ≤ ∑ k : Fin 3, D k := Finset.sum_nonneg fun k hk => hD k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAle (k : Fin 3) : D k ≤ ∑ l : Fin 3, D l :=
    Finset.single_le_sum (fun l hl => hD l) (Finset.mem_univ k)
  refine ⟨C, hC, ?_⟩
  intro n z i
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
    rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l z = _
    rw [← hjoint]
    rfl
  have hbasePartial (k l : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) l z =
        rieszPressureJointDirection (fun q => A q k) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    change CKN.spatialPartialProd (fun q => A q k) l z = _
    rw [← hjoint]
    rfl
  have hbase : 0 ≤ 1 + vec3EuclideanNorm z.1 := by
    have hn := vec3EuclideanNorm_nonneg z.1
    linarith only [hn]
  have hprofile : 0 ≤ (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg hbase _
  have hpair (k l m p : Fin 3) :
      |(associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l z -
        associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) m) p z) -
       (associatedPressureTestPartial (fun q => A q k) l z -
        associatedPressureTestPartial (fun q => A q m) p z)| ≤
      (D k + D m) * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    rw [hcutPartial, hcutPartial, hbasePartial, hbasePartial]
    calc
      _ ≤ |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z -
            rieszPressureJointDirection (fun q => A q k) l z| +
          |rieszPressureJointDirection
            (rieszPressurePotentialCutoffTest (fun q => A q m) n) p z -
            rieszPressureJointDirection (fun q => A q m) p z| :=
        associatedPressureAbs_sub_sub_le _ _ _ _
      _ ≤ _ := by
        calc
          _ ≤ D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) +
              D m * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) :=
            add_le_add (hdirErr k l n z) (hdirErr m p n z)
          _ = _ := by ring
  have hcoeff (k m : Fin 3) : D k + D m ≤ C := by
    calc
      D k + D m ≤ (∑ l : Fin 3, D l) + ∑ l : Fin 3, D l :=
        add_le_add (hAle k) (hAle m)
      _ = C := by dsimp [C]; ring
  fin_cases i
  · change |associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 0 -
        associatedPressureTestCurl A z 0| ≤ _
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero]
    exact (hpair 2 1 1 2).trans
      (mul_le_mul_of_nonneg_right (hcoeff 2 1) hprofile)
  · change |associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 1 -
        associatedPressureTestCurl A z 1| ≤ _
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one]
    exact (hpair 0 2 2 0).trans
      (mul_le_mul_of_nonneg_right (hcoeff 0 2) hprofile)
  · change |associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 2 -
        associatedPressureTestCurl A z 2| ≤ _
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two]
    exact (hpair 1 0 0 1).trans
      (mul_le_mul_of_nonneg_right (hcoeff 1 0) hprofile)

private theorem hp_cutoffCurl_eq_inner
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (n : ℕ) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n)) :
    associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoff n q.1 • A q) z =
      associatedPressureTestCurl A z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
    rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
  have hcutPartial (k l : Fin 3) :
      associatedPressureTestPartial
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hcutcomp k) l z
    change CKN.spatialPartialProd
      (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l z = _
    rw [← hjoint]
    rfl
  have hbasePartial (k l : Fin 3) :
      associatedPressureTestPartial (fun q => A q k) l z =
        rieszPressureJointDirection (fun q => A q k) l z := by
    have hjoint := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    change CKN.spatialPartialProd (fun q => A q k) l z = _
    rw [← hjoint]
    rfl
  have hdirEq (k l : Fin 3) :
      rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z =
        rieszPressureJointDirection (fun q => A q k) l z :=
    associatedPressurePotentialCutoff_direction_eq_of_inner (hAcomp k) l n z hx
  ext i
  fin_cases i
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 0 =
      associatedPressureTestCurl A z 0
    rw [associatedPressureTestCurl_zero, associatedPressureTestCurl_zero,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 1 =
      associatedPressureTestCurl A z 1
    rw [associatedPressureTestCurl_one, associatedPressureTestCurl_one,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]
  · change associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoff n q.1 • A q) z 2 =
      associatedPressureTestCurl A z 2
    rw [associatedPressureTestCurl_two, associatedPressureTestCurl_two,
      hcutPartial, hcutPartial, hbasePartial, hbasePartial, hdirEq, hdirEq]

/-- Each spatial derivative of the solenoidal cutoff curl has a uniform
fourth order error profile. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_error_profile
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3),
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j z -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j z| ≤
        C * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
  let A := associatedPressureHelmholtzVectorPotential φ
  let H : Fin 3 → ℝ := fun k =>
    Classical.choose (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.hessian_bound +
      6 * CKN.cutoffGradientConstant *
        Classical.choose (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound +
      9 * CKN.cutoffSecondDerivativeConstant *
        Classical.choose (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound
  let C : ℝ := 2 * ∑ k : Fin 3, H k
  have hGradC : 0 ≤ CKN.cutoffGradientConstant := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hSecondC : 0 ≤ CKN.cutoffSecondDerivativeConstant := by
    have h := CKN.mollifiedBallCutoff_second_derivative_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (norm_nonneg _) (by simpa using h)
  have hH (k : Fin 3) : 0 ≤ H k := by
    have h0 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.hessian_bound).1
    have h1 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.gradient_bound).1
    have h2 := (Classical.choose_spec
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1.value_bound).1
    dsimp [H]
    positivity
  have hsum : 0 ≤ ∑ k : Fin 3, H k := Finset.sum_nonneg fun k hk => hH k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAle (k : Fin 3) : H k ≤ ∑ l : Fin 3, H l :=
    Finset.single_le_sum (fun l hl => hH l) (Finset.mem_univ k)
  refine ⟨C, hC, ?_⟩
  intro n z i j
  have hAcont : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hAcont
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => rieszPressurePotentialCutoff n q.1 • A q) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadius_pos n)).comp contDiff_fst |>.smul hAcont
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
  have hcutCurl := hpCurlFormula hcutA i j z
  have hbaseCurl := hpCurlFormula hAcont i j z
  have hcutHess (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z =
        rieszPressureJointHessian
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) j l z := by
    have hcutcomp : ContDiff ℝ (⊤ : ℕ∞)
        (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
      rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
    have hjoint := rieszPressure_sliceMixedSecond_eq_joint hcutcomp j l z
    change CKN.mixedSecond
      (fun x : Vec3 => (rieszPressurePotentialCutoff n x • A (x, z.2)) k)
      j l z.1 = _
    exact hjoint
  have hbaseHess (k l : Fin 3) :
      CKN.spatialSecondPartialProd (fun q => A q k) l j z =
        rieszPressureJointHessian (fun q => A q k) j l z := by
    have hjoint := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    change CKN.mixedSecond (fun x : Vec3 => A (x, z.2) k) j l z.1 = _
    exact hjoint
  have hHessErr (k l : Fin 3) :
      |CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z -
        CKN.spatialSecondPartialProd (fun q => A q k) l j z| ≤
        H k * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    rw [hcutHess k l, hbaseHess k l]
    have herr := rieszPressurePotentialHessianCutoffError_bound
      (hAcomp k) (K := (Set.univ : Set ℝ))
      (by intro t ht x; exact (ht (Set.mem_univ t)).elim)
      (associatedPressureHelmholtzVectorPotential_component_decay hφ k).1
      j l n z
    simpa [H, rieszPressurePotentialHessianCutoffError,
      rieszPressurePotentialSpatialProfile] using herr
  have hprofile : 0 ≤ (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  have hpair (k l m p : Fin 3) :
      |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) m) p j z) -
       (CKN.spatialSecondPartialProd (fun q => A q k) l j z -
        CKN.spatialSecondPartialProd (fun q => A q m) p j z)| ≤
      (H k + H m) * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    calc
      _ ≤ |CKN.spatialSecondPartialProd
            (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z -
            CKN.spatialSecondPartialProd (fun q => A q k) l j z| +
          |CKN.spatialSecondPartialProd
            (fun q => (rieszPressurePotentialCutoff n q.1 • A q) m) p j z -
            CKN.spatialSecondPartialProd (fun q => A q m) p j z| :=
        associatedPressureAbs_sub_sub_le _ _ _ _
      _ ≤ _ := by
        calc
          _ ≤ H k * (1 + ‖z.1‖) ^ (-(4 : ℝ)) +
              H m * (1 + ‖z.1‖) ^ (-(4 : ℝ)) :=
            add_le_add (hHessErr k l) (hHessErr m p)
          _ = _ := by ring
  have hcoeff (k m : Fin 3) : H k + H m ≤ C := by
    calc
      H k + H m ≤ (∑ l : Fin 3, H l) + ∑ l : Fin 3, H l :=
        add_le_add (hAle k) (hAle m)
      _ = C := by dsimp [C]; ring
  have hcurlSub :
      |CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (fun w => rieszPressurePotentialCutoff n w.1 • A w) q i) j z -
        CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z| ≤
        C * (1 + ‖z.1‖) ^ (-(4 : ℝ)) := by
    rw [hcutCurl, hbaseCurl]
    fin_cases i
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 2) 1 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 1) 2 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 2) 1 j z -
        CKN.spatialSecondPartialProd (fun q => A q 1) 2 j z)| ≤ _
      exact (hpair 2 1 1 2).trans
        (mul_le_mul_of_nonneg_right (hcoeff 2 1) hprofile)
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 0) 2 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 2) 0 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 0) 2 j z -
        CKN.spatialSecondPartialProd (fun q => A q 2) 0 j z)| ≤ _
      exact (hpair 0 2 2 0).trans
        (mul_le_mul_of_nonneg_right (hcoeff 0 2) hprofile)
    · change |(CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 1) 0 j z -
        CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) 0) 1 j z) -
        (CKN.spatialSecondPartialProd (fun q => A q 1) 0 j z -
        CKN.spatialSecondPartialProd (fun q => A q 0) 1 j z)| ≤ _
      exact (hpair 1 0 0 1).trans
        (mul_le_mul_of_nonneg_right (hcoeff 1 0) hprofile)
  change |CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (fun w => rieszPressurePotentialCutoff n w.1 • A w) q i) j z -
    CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z| ≤ _
  exact hcurlSub

private theorem hp_cutoffCurl_spatialPartial_eq_inner
    (A : Vec3 × ℝ → Vec3) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (n : ℕ) (z : Vec3 × ℝ) (i j : Fin 3)
    (hxBall : z.1 ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n))
    (hxClosed : z.1 ∈ CKN.euclideanClosedBall 0
      (rieszPressurePotentialCutoffScale n)) :
    CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (fun w => rieszPressurePotentialCutoff n w.1 • A w) q i) j z =
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j z := by
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q => A q k) :=
    (contDiff_apply ℝ ℝ k).comp hA
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => rieszPressurePotentialCutoff n q.1 • A q) := by
    exact (CKN.mollifiedBallCutoff_smooth 0
      (rieszPressurePotentialCutoffRadius_pos n)).comp contDiff_fst |>.smul hA
  have hdouble (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => (rieszPressurePotentialCutoff n q.1 • A q) k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    have hcutcomp : ContDiff ℝ (⊤ : ℕ∞)
        (rieszPressurePotentialCutoffTest (fun q : Vec3 × ℝ => A q k) n) :=
      rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
    have hcutId := rieszPressure_sliceMixedSecond_eq_joint hcutcomp j l z
    have hEq := associatedPressurePotentialCutoff_hessian_eq_of_inner
      (hAcomp k) j l n z hxBall hxClosed
    have hAId := rieszPressure_sliceMixedSecond_eq_joint (hAcomp k) j l z
    change CKN.mixedSecond
        (fun x : Vec3 => (rieszPressurePotentialCutoff n x • A (x, z.2)) k)
        j l z.1 = _
    exact hcutId.trans (hEq.trans hAId.symm)
  have hdouble' (k l : Fin 3) :
      CKN.spatialSecondPartialProd
          (fun q => rieszPressurePotentialCutoff n q.1 * A q k) l j z =
        CKN.spatialSecondPartialProd (fun q => A q k) l j z := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hdouble k l
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
  fin_cases i
  · change CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (fun w => rieszPressurePotentialCutoff n w.1 • A w) q 0) j z =
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q 0) j z
    rw [hpCurlFormula hcutA 0 j z, hpCurlFormula hA 0 j z]
    simp [hdouble']
  · change CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (fun w => rieszPressurePotentialCutoff n w.1 • A w) q 1) j z =
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q 1) j z
    rw [hpCurlFormula hcutA 1 j z, hpCurlFormula hA 1 j z]
    simp [hdouble']
  · change CKN.spatialPartialProd
        (fun q => associatedPressureTestCurl
          (fun w => rieszPressurePotentialCutoff n w.1 • A w) q 2) j z =
      CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q 2) j z
    rw [hpCurlFormula hcutA 2 j z, hpCurlFormula hA 2 j z]
    simp [hdouble']

/-- Each fixed-time component of the cutoff curl gradient has the
`R⁻³ᐟ²` spatial `L²` error rate in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurl_spatialPartial_component_eLpNorm_error_le
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (n : ℕ) (t : ℝ) (i j : Fin 3),
      eLpNorm (fun x : Vec3 =>
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
        CKN.spatialPartialProd
          (fun q => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) q i) j (x, t))
        2 (volume : Measure Vec3) ≤
        ENNReal.ofReal C * ENNReal.ofReal
          (associatedPressureHelmholtzTailL2Constant *
            (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurl_spatialPartial_error_profile hφ
  refine ⟨C, hC, ?_⟩
  intro n t i j
  let s := rieszPressurePotentialCutoffScale n
  let ρ := s / 2
  let A := associatedPressureHelmholtzVectorPotential φ
  let f : Vec3 → ℝ := fun x =>
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) q i) j (x, t) -
    CKN.spatialPartialProd
      (fun q => associatedPressureTestCurl A q i) j (x, t)
  have hs1 : 1 ≤ s := by simpa [s] using rieszPressurePotentialCutoffScale_ge_one n
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hcutA : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureHelmholtzCutoffVectorPotential φ n) :=
    (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1
  have hbaseA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hcutCurl : ContDiff ℝ (⊤ : ℕ∞)
      (associatedPressureTestCurl (associatedPressureHelmholtzCutoffVectorPotential φ n)) :=
    associatedPressureTestCurl_contDiff hcutA
  have hbaseCurl : ContDiff ℝ (⊤ : ℕ∞) (associatedPressureTestCurl A) :=
    associatedPressureTestCurl_contDiff hbaseA
  have hcutPart : ContDiff ℝ (⊤ : ℕ∞)
      (fun q => CKN.spatialPartialProd
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) j q) :=
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
  have hpoint (x : Vec3) : |f x| ≤ C * hpTailProfile ρ x := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile n (x, t) i j
      have hx0 : 1 ≤ 1 + ‖x‖ := by
        have hn := norm_nonneg x
        linarith only [hn]
      have hdecay : (1 + ‖x‖) ^ (-(4 : ℝ)) ≤
          (1 + ‖x‖) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hx0 (by norm_num)
      have hprofileEq : hpTailProfile ρ x = (1 + ‖x‖) ^ (-(3 : ℝ)) := by
        unfold hpTailProfile
        split_ifs; simp_all
      rw [hprofileEq]
      dsimp [f, A] at herr ⊢
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
      have heq := hp_cutoffCurl_spatialPartial_eq_inner A hbaseA n (x, t) i j
        (by simpa [s] using hxBall) (by simpa [s] using hxClosed)
      have hz : f x = 0 := by
        dsimp [f, A]
        apply sub_eq_zero.mpr
        change CKN.spatialPartialProd
            (fun q => associatedPressureTestCurl
              (fun w => rieszPressurePotentialCutoff n w.1 • A w) q i) j (x, t) =
          CKN.spatialPartialProd (fun q => associatedPressureTestCurl A q i) j (x, t) at heq
        exact heq
      have hprofileZero : hpTailProfile ρ x = 0 := by
        unfold hpTailProfile
        split_ifs; simp_all
      rw [hz, hprofileZero]
      simp
  simpa [f, ρ, s] using hp_eLpNorm_le_of_tail_profile ρ hρpos C hC hfae hpoint

/-- The time derivative of the solenoidal cutoff curl has a uniform cubic
spatial error profile, by the potential decay in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_error_profile
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (n : ℕ) (z : Vec3 × ℝ) (i : Fin 3),
      |associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) z -
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) w i) z| ≤
        C * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
  let A := associatedPressureHelmholtzVectorPotentialTimePartial φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    apply contDiff_pi.2
    intro k
    exact CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  let hdecay : ∀ k : Fin 3, RieszPressurePotentialDecay (fun q => A q k) :=
    fun k => (associatedPressureHelmholtzVectorPotential_component_decay hφ k).2
  let D : Fin 3 → ℝ := fun k =>
    CKN.cutoffGradientConstant * (28 / 13 : ℝ) *
        Classical.choose (hdecay k).value_bound +
      2 * Classical.choose (hdecay k).gradient_bound
  have hCG : 0 ≤ CKN.cutoffGradientConstant := by
    have h := CKN.mollifiedBallCutoff_gradient_bound 0
      (by norm_num : (0 : ℝ) < 1) (0 : Vec3)
    exact le_trans (CKN.vecEuclideanNorm_nonneg _) (by simpa using h)
  have hD (k : Fin 3) : 0 ≤ D k := by
    dsimp [D]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hCG (by norm_num))
        (Classical.choose_spec (hdecay k).value_bound).1)
      (mul_nonneg (by norm_num)
        (Classical.choose_spec (hdecay k).gradient_bound).1)
  have hdirErr (k l : Fin 3) (n : ℕ) (z : Vec3 × ℝ) :
      |rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z -
        rieszPressureJointDirection (fun q => A q k) l z| ≤
        D k * (1 + vec3EuclideanNorm z.1) ^ (-(3 : ℝ)) := by
    have hAcomp : ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => A q k) :=
      (contDiff_apply ℝ ℝ k).comp hA
    have h := associatedPressurePotentialCutoff_direction_error_bound hAcomp
      (hdecay k) l n z
    simpa [D] using h
  obtain ⟨C, hC, hprofile⟩ := hp_cutoffCurl_error_profile A hA D hD hdirErr
  refine ⟨C, hC, ?_⟩
  intro n z i
  have hcut := associatedPressureHelmholtzCutoffCurl_timePartial_eq hφ n i z
  have hAorig := associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hbase := associatedPressureTestCurl_timePartial hAorig i z
  have hcut' :
      associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) z =
        associatedPressureTestCurl
          (fun q => rieszPressurePotentialCutoff n q.1 • A q) z i := by
    simpa [A] using hcut
  have hbase' :
      associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) w i) z =
        associatedPressureTestCurl A z i := by
    have hbaseVec :
        (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
          (fun y => associatedPressureHelmholtzVectorPotential φ y k) q) = A := by
      funext q k
      rfl
    rw [hbaseVec] at hbase
    exact hbase
  rw [hcut', hbase']
  simpa [A] using hprofile n z i

/-- Inside the cutoff's inner ball, the time derivatives of the cutoff curl
and the full Helmholtz curl agree. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_eq_of_inner
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (n : ℕ) (i : Fin 3) (z : Vec3 × ℝ)
    (hx : z.1 ∈ CKN.euclideanBall 0 (rieszPressurePotentialCutoffScale n)) :
    associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) z =
      associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzVectorPotential φ) w i) z := by
  let A := associatedPressureHelmholtzVectorPotentialTimePartial φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := by
    apply contDiff_pi.2
    intro k
    exact CKN.contDiff_timePartial
      ((contDiff_apply ℝ ℝ k).comp (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hcut := associatedPressureHelmholtzCutoffCurl_timePartial_eq hφ n i z
  have hbase := associatedPressureTestCurl_timePartial
    (associatedPressureHelmholtzVectorPotential_contDiff hφ) i z
  calc
    _ = associatedPressureTestCurl
        (fun q => rieszPressurePotentialCutoff n q.1 • A q) z i := by simpa [A] using hcut
    _ = associatedPressureTestCurl A z i := by
      exact congrFun (hp_cutoffCurl_eq_inner A hA n z hx) i
    _ = _ := by
      have hbaseVec :
          (fun q : Vec3 × ℝ => fun k => associatedPressureTestTimePartial
            (fun y => associatedPressureHelmholtzVectorPotential φ y k) q) = A := by
        funext q k
        rfl
      rw [hbaseVec] at hbase
      exact hbase.symm

/-- Each fixed-time component of the time derivative of the solenoidal cutoff
error has the `R⁻³ᐟ²` spatial `L²` rate in `lem:helmholtz-test`. -/
theorem associatedPressureHelmholtzCutoffCurl_timePartial_component_eLpNorm_error_le
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T)) :
    ∃ C ≥ 0, ∀ (n : ℕ) (t : ℝ) (i : Fin 3),
      eLpNorm (fun x : Vec3 =>
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) (x, t) -
        associatedPressureTestTimePartial
          (fun w => associatedPressureTestCurl
            (associatedPressureHelmholtzVectorPotential φ) w i) (x, t))
        2 (volume : Measure Vec3) ≤
        ENNReal.ofReal C * ENNReal.ofReal
          (associatedPressureHelmholtzTailL2Constant *
            (rieszPressurePotentialCutoffScale n / 2) ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hprofile⟩ :=
    associatedPressureHelmholtzCutoffCurl_timePartial_error_profile hφ
  refine ⟨C, hC, ?_⟩
  intro n t i
  let s := rieszPressurePotentialCutoffScale n
  let ρ := s / 2
  let f : Vec3 → ℝ := fun x =>
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) (x, t) -
    associatedPressureTestTimePartial
      (fun w => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) w i) (x, t)
  have hs1 : 1 ≤ s := by simpa [s] using rieszPressurePotentialCutoffScale_ge_one n
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hcut : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z i) := by
    exact (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzCutoffVectorPotential_mem_spaceTimeTestFunction hφ n).1)
  have hbase : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestCurl
        (associatedPressureHelmholtzVectorPotential φ) z i) := by
    exact (contDiff_apply ℝ ℝ i).comp
      (associatedPressureTestCurl_contDiff
        (associatedPressureHelmholtzVectorPotential_contDiff hφ))
  have hcutT : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => associatedPressureTestTimePartial
        (fun w => associatedPressureTestCurl
          (associatedPressureHelmholtzCutoffVectorPotential φ n) w i) z) :=
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
  have hpoint (x : Vec3) : |f x| ≤ C * hpTailProfile ρ x := by
    by_cases hx : ρ ≤ ‖x‖
    · have herr := hprofile n (x, t) i
      have hnorm := norm_le_vec3EuclideanNorm x
      have hdecay : (1 + vec3EuclideanNorm x) ^ (-(3 : ℝ)) ≤
          (1 + ‖x‖) ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity)
          (by linarith only [hnorm]) (by norm_num)
      have hprofileEq : hpTailProfile ρ x = (1 + ‖x‖) ^ (-(3 : ℝ)) := by
        unfold hpTailProfile
        split_ifs; simp_all
      rw [hprofileEq]
      dsimp [f] at herr ⊢
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
      have heq := associatedPressureHelmholtzCutoffCurl_timePartial_eq_of_inner
        hφ n i (x, t) (by simpa [s] using hxBall)
      have hz : f x = 0 := by
        dsimp [f]
        exact sub_eq_zero.mpr heq
      have hprofileZero : hpTailProfile ρ x = 0 := by
        unfold hpTailProfile
        split_ifs; simp_all
      rw [hz, hprofileZero]
      simp
  simpa [f, ρ, s] using hp_eLpNorm_le_of_tail_profile ρ hρpos C hC hfae hpoint

end CKN.Leray
