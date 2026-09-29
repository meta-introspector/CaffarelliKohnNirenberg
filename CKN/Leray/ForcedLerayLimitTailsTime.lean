-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Foundation.WeakDerivOneDim
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Increments from a distributional inequality in time

In the proof of `lem:forced-tails` the localized energy inequality
`eq:reg-local-energy-forced`, tested with a fixed spatial weight, gives for the
weighted kinetic energy Y a distributional inequality Y' ≤ H on (0,T).
When Y is continuous on [0,T] and H is integrable, this inequality holds
between any two times: Y t - Y s ≤ ∫ₛᵗ H. The proof tests with smooth ramps
Φ(τ - s) - Φ(τ - t), where Φ is the primitive of a narrow normalized bump,
and lets the width of the bump tend to zero.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- A smooth nonnegative bump of unit mass supported in (-r, r). -/
private theorem forcedTails_exists_bump {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ x, 0 ≤ φ x) ∧
      (∀ x, r ≤ |x| → φ x = 0) ∧ ∫ x, φ x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨b.normed volume, b.contDiff_normed, b.nonneg_normed, fun x hx => ?_,
    b.integral_normed⟩
  apply Function.notMem_support.1
  rw [b.support_normed_eq]
  simpa [Metric.mem_ball, Real.dist_eq, not_lt] using hx

/-- The primitive of a bump from -r is a smooth monotone ramp from 0 to 1. -/
private theorem forcedTails_ramp_props {r : ℝ} (hr : 0 < r) {φ : ℝ → ℝ}
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφsupp : ∀ x, r ≤ |x| → φ x = 0) (hφ1 : ∫ x, φ x = 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ σ in (-r)..x, φ σ) ∧
    (∀ x, HasDerivAt (fun x => ∫ σ in (-r)..x, φ σ) (φ x) x) ∧
    Monotone (fun x => ∫ σ in (-r)..x, φ σ) ∧
    (∀ x, x ≤ -r → ∫ σ in (-r)..x, φ σ = 0) ∧
    (∀ x, r ≤ x → ∫ σ in (-r)..x, φ σ = 1) ∧
    (∀ x, 0 ≤ ∫ σ in (-r)..x, φ σ ∧ ∫ σ in (-r)..x, φ σ ≤ 1) := by
  have hc : Continuous φ := hφs.continuous
  have hII : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b =>
    hc.intervalIntegrable a b
  have hderiv : ∀ x, HasDerivAt (fun x => ∫ σ in (-r)..x, φ σ) (φ x) x := fun x =>
    (hc.integral_hasStrictDerivAt (-r) x).hasDerivAt
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ σ in (-r)..x, φ σ) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    have hd : deriv (fun x => ∫ σ in (-r)..x, φ σ) = φ := by
      funext x
      exact (hderiv x).deriv
    rw [hd]
    exact hφs
  have hmono : Monotone (fun x => ∫ σ in (-r)..x, φ σ) := by
    intro x y hxy
    have h := intervalIntegral.integral_interval_sub_left (hII (-r) y) (hII (-r) x)
    have hnn : 0 ≤ ∫ σ in x..y, φ σ :=
      intervalIntegral.integral_nonneg hxy fun u _ => hφ0 u
    change (∫ σ in (-r)..x, φ σ) ≤ ∫ σ in (-r)..y, φ σ
    linarith only [h, hnn]
  have hzero : ∀ x, x ≤ -r → ∫ σ in (-r)..x, φ σ = 0 := by
    intro x hx
    have h : EqOn φ (fun _ => (0 : ℝ)) (uIcc (-r) x) := by
      intro σ hσ
      rw [uIcc_of_ge hx] at hσ
      exact hφsupp σ (by rw [abs_of_neg (by linarith only [hσ.2, hr])]; linarith only [hσ.2])
    rw [intervalIntegral.integral_congr h, intervalIntegral.integral_zero]
  have hone : ∀ x, r ≤ x → ∫ σ in (-r)..x, φ σ = 1 := by
    intro x hx
    rw [intervalIntegral.integral_of_le (by linarith only [hx, hr]), ← hφ1]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun σ hσ => ?_
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hσ
    rcases hσ with h | h
    · exact hφsupp σ (by rw [abs_of_nonpos (by linarith only [h, hr])]; linarith only [h])
    · exact hφsupp σ (by rw [abs_of_pos (by linarith only [h, hx, hr])]; linarith only [h, hx])
  refine ⟨hsmooth, hderiv, hmono, hzero, hone, fun x => ⟨?_, ?_⟩⟩
  · rcases le_total x (-r) with h | h
    · rw [hzero x h]
    · rw [← hzero (-r) le_rfl]
      exact hmono h
  · rw [← hone (max x r) (le_max_right _ _)]
    exact hmono (le_max_left _ _)

/-- Averaging a function continuous on [0,T] against narrow unit bumps
centered at an interior point recovers its value there. -/
private theorem forcedTails_bump_tendsto {T : ℝ} {Y : ℝ → ℝ} (hY : ContinuousOn Y (Icc 0 T))
    {c : ℝ} (hc : c ∈ Ioo 0 T) {r : ℕ → ℝ} (hrc : ∀ n, r n < c ∧ r n < T - c)
    (hrlim : Tendsto r atTop (𝓝 0)) {φ : ℕ → ℝ → ℝ} (hφc : ∀ n, Continuous (φ n))
    (hφ0 : ∀ n x, 0 ≤ φ n x) (hφsupp : ∀ n x, r n ≤ |x| → φ n x = 0)
    (hφ1 : ∀ n, ∫ x, φ n x = 1) :
    Tendsto (fun n => ∫ τ in Ioo 0 T, Y τ * φ n (τ - c)) atTop (𝓝 (Y c)) := by
  have hvan : ∀ n τ, τ ∉ Ioo 0 T → φ n (τ - c) = 0 := by
    intro n τ hτ
    simp only [mem_Ioo, not_and_or, not_lt] at hτ
    refine hφsupp n _ ?_
    rcases hτ with h | h
    · rw [abs_of_neg (by linarith only [h, hc.1])]
      linarith only [h, (hrc n).1]
    · rw [abs_of_pos (by linarith only [h, hc.2])]
      linarith only [h, (hrc n).2]
  have hint1 : ∀ n, ∫ τ in Ioo 0 T, φ n (τ - c) = 1 := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hvan n),
      integral_sub_right_eq_self (fun x => φ n x) c, hφ1 n]
  have hYφint : ∀ n, IntegrableOn (fun τ => Y τ * φ n (τ - c)) (Ioo 0 T) := fun n =>
    ((hY.mul ((hφc n).comp (continuous_id.sub continuous_const)).continuousOn).integrableOn_Icc
      ).mono_set Ioo_subset_Icc_self
  have hφint : ∀ n, IntegrableOn (fun τ => φ n (τ - c)) (Ioo 0 T) := fun n =>
    (((hφc n).comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_Icc
      ).mono_set Ioo_subset_Icc_self
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcw : ContinuousWithinAt Y (Icc 0 T) c := hY c (Ioo_subset_Icc_self hc)
  obtain ⟨δ, hδ, hδY⟩ := Metric.continuousWithinAt_iff.1 hcw (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hrlim.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn => ?_⟩
  have hYc : Y c = ∫ τ in Ioo 0 T, Y c * φ n (τ - c) := by
    rw [integral_const_mul, hint1 n, mul_one]
  rw [Real.dist_eq, hYc, ← integral_sub (hYφint n) ((hφint n).const_mul (Y c))]
  have hbound : ‖∫ τ in Ioo 0 T, (Y τ * φ n (τ - c) - Y c * φ n (τ - c))‖ ≤
      ∫ τ in Ioo 0 T, ε / 2 * φ n (τ - c) := by
    refine norm_integral_le_of_norm_le ((hφint n).const_mul (ε / 2)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφ0 n _)]
    by_cases hτc : |τ - c| < r n
    · have hd : dist τ c < δ := by
        rw [Real.dist_eq]
        exact hτc.trans (hN n hn)
      have := hδY (Ioo_subset_Icc_self hτ) hd
      rw [Real.dist_eq] at this
      exact mul_le_mul_of_nonneg_right this.le (hφ0 n _)
    · rw [hφsupp n _ (not_lt.1 hτc), mul_zero, mul_zero]
  rw [integral_const_mul, hint1 n, mul_one] at hbound
  rw [← Real.norm_eq_abs]
  exact hbound.trans_lt (half_lt_self hε)

/-- The interior case of `forcedTails_increment_le_of_weak`. -/
private theorem forcedTails_increment_le_interior {T : ℝ} {Y H : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc 0 T)) (hH : IntegrableOn H (Ioo 0 T))
    (hweak : ∀ θ : ℝ → ℝ, IsIntervalTest (Ioo 0 T) θ → (∀ τ, 0 ≤ θ τ) →
      -(∫ τ in Ioo 0 T, Y τ * deriv θ τ) ≤ ∫ τ in Ioo 0 T, H τ * θ τ)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < T) :
    Y t - Y s ≤ ∫ τ in s..t, H τ := by
  set r0 : ℝ := min s (T - t) / 2 with hr0def
  have hmin : 0 < min s (T - t) := lt_min hs (by linarith only [ht])
  have hr0 : 0 < r0 := half_pos hmin
  have hr0s : r0 < s := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hr0t : r0 < T - t := (half_lt_self hmin).trans_le (min_le_right _ _)
  let r : ℕ → ℝ := fun n => r0 / ((n : ℝ) + 1)
  have hrpos : ∀ n, 0 < r n := fun n => div_pos hr0 (by positivity)
  have hrle : ∀ n, r n ≤ r0 := fun n =>
    div_le_self hr0.le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith only [this])
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat r0).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp [r]
  have hsmall : ∀ δ > 0, ∀ᶠ n in atTop, r n < δ := fun δ hδ =>
    hrlim.eventually (gt_mem_nhds hδ)
  choose φ hφs hφ0 hφsupp hφ1 using fun n => forcedTails_exists_bump (hrpos n)
  have hramp := fun n => forcedTails_ramp_props (hrpos n) (hφs n) (hφ0 n) (hφsupp n) (hφ1 n)
  let Φ : ℕ → ℝ → ℝ := fun n x => ∫ σ in (-r n)..x, φ n σ
  let θ : ℕ → ℝ → ℝ := fun n τ => Φ n (τ - s) - Φ n (τ - t)
  have hθ0 : ∀ n τ, 0 ≤ θ n τ := fun n τ =>
    sub_nonneg.2 ((hramp n).2.2.1 (by linarith only [hst]))
  have hθ1 : ∀ n τ, θ n τ ≤ 1 := fun n τ => by
    have h1 := ((hramp n).2.2.2.2.2 (τ - s)).2
    have h2 := ((hramp n).2.2.2.2.2 (τ - t)).1
    show (∫ σ in (-r n)..(τ - s), φ n σ) - (∫ σ in (-r n)..(τ - t), φ n σ) ≤ 1
    linarith only [h1, h2]
  have hθlow : ∀ n τ, τ ≤ s - r n → θ n τ = 0 := fun n τ hτ => by
    show (∫ σ in (-r n)..(τ - s), φ n σ) - (∫ σ in (-r n)..(τ - t), φ n σ) = 0
    rw [(hramp n).2.2.2.1 (τ - s) (by linarith only [hτ]),
      (hramp n).2.2.2.1 (τ - t) (by linarith only [hτ, hst]), sub_zero]
  have hθhigh : ∀ n τ, t + r n ≤ τ → θ n τ = 0 := fun n τ hτ => by
    show (∫ σ in (-r n)..(τ - s), φ n σ) - (∫ σ in (-r n)..(τ - t), φ n σ) = 0
    rw [(hramp n).2.2.2.2.1 (τ - s) (by linarith only [hτ, hst]),
      (hramp n).2.2.2.2.1 (τ - t) (by linarith only [hτ]), sub_self]
  have hθmid : ∀ n τ, s + r n ≤ τ → τ ≤ t - r n → θ n τ = 1 := fun n τ h1 h2 => by
    show (∫ σ in (-r n)..(τ - s), φ n σ) - (∫ σ in (-r n)..(τ - t), φ n σ) = 1
    rw [(hramp n).2.2.2.2.1 (τ - s) (by linarith only [h1]),
      (hramp n).2.2.2.1 (τ - t) (by linarith only [h2]), sub_zero]
  have hθsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (θ n) := fun n =>
    ((hramp n).1.comp (contDiff_id.sub contDiff_const)).sub
      ((hramp n).1.comp (contDiff_id.sub contDiff_const))
  have hθderiv : ∀ n τ, deriv (θ n) τ = φ n (τ - s) - φ n (τ - t) := fun n τ =>
    (((hramp n).2.1 (τ - s)).comp_sub_const τ s |>.sub
      (((hramp n).2.1 (τ - t)).comp_sub_const τ t)).deriv
  have hθtest : ∀ n, IsIntervalTest (Ioo 0 T) (θ n) := by
    intro n
    have hsupp : Function.support (θ n) ⊆ Icc (s - r n) (t + r n) := by
      intro τ hτ
      by_contra hmem
      simp only [mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with h | h
      · exact hτ (hθlow n τ h.le)
      · exact hτ (hθhigh n τ h.le)
    have hts : tsupport (θ n) ⊆ Icc (s - r n) (t + r n) :=
      closure_minimal hsupp isClosed_Icc
    refine ⟨hθsmooth n, isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hts,
      hts.trans fun τ hτ => ⟨?_, ?_⟩⟩
    · linarith only [hτ.1, hrle n, hr0s]
    · linarith only [hτ.2, hrle n, hr0t]
  -- the inequality for each ramp
  have hφc : ∀ n, Continuous (φ n) := fun n => (hφs n).continuous
  have hYφint : ∀ n c, IntegrableOn (fun τ => Y τ * φ n (τ - c)) (Ioo 0 T) := fun n c =>
    ((hY.mul ((hφc n).comp (continuous_id.sub continuous_const)).continuousOn).integrableOn_Icc
      ).mono_set Ioo_subset_Icc_self
  have hineq : ∀ n, (∫ τ in Ioo 0 T, Y τ * φ n (τ - t)) -
      ∫ τ in Ioo 0 T, Y τ * φ n (τ - s) ≤ ∫ τ in Ioo 0 T, H τ * θ n τ := by
    intro n
    have h := hweak (θ n) (hθtest n) (hθ0 n)
    have heq : (∫ τ in Ioo 0 T, Y τ * deriv (θ n) τ) =
        (∫ τ in Ioo 0 T, Y τ * φ n (τ - s)) - ∫ τ in Ioo 0 T, Y τ * φ n (τ - t) := by
      rw [← integral_sub (hYφint n s) (hYφint n t)]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [hθderiv n τ, mul_sub]
    rw [heq] at h
    linarith only [h]
  have hsT : s ∈ Ioo 0 T := ⟨hs, by linarith only [hst, ht]⟩
  have htT : t ∈ Ioo 0 T := ⟨by linarith only [hs, hst], ht⟩
  have hlimt := forcedTails_bump_tendsto hY htT
    (fun n => ⟨by linarith only [hrle n, hr0s, hst], by linarith only [hrle n, hr0t]⟩)
    hrlim hφc hφ0 hφsupp hφ1
  have hlims := forcedTails_bump_tendsto hY hsT
    (fun n => ⟨by linarith only [hrle n, hr0s], by linarith only [hrle n, hr0t, hst]⟩)
    hrlim hφc hφ0 hφsupp hφ1
  -- the right side converges to the integral over (s,t)
  have hθlim : ∀ τ, τ ≠ s → τ ≠ t →
      Tendsto (fun n => θ n τ) atTop (𝓝 ((Ioo s t).indicator (fun _ => (1 : ℝ)) τ)) := by
    intro τ hτs hτt
    rcases lt_or_gt_of_ne hτs with h1 | h1
    · rw [indicator_of_notMem (fun h => by linarith only [h.1, h1])]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hsmall (s - τ) (by linarith only [h1])] with n hn
      exact (hθlow n τ (by linarith only [hn])).symm
    · rcases lt_or_gt_of_ne hτt with h2 | h2
      · rw [indicator_of_mem (show τ ∈ Ioo s t from ⟨h1, h2⟩)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hsmall (τ - s) (by linarith only [h1]),
          hsmall (t - τ) (by linarith only [h2])] with n hn1 hn2
        exact (hθmid n τ (by linarith only [hn1]) (by linarith only [hn2])).symm
      · rw [indicator_of_notMem (fun h => by linarith only [h.2, h2])]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hsmall (τ - t) (by linarith only [h2])] with n hn
        exact (hθhigh n τ (by linarith only [hn])).symm
  have hne : ∀ c : ℝ, ∀ᵐ τ ∂(volume.restrict (Ioo (0 : ℝ) T)), τ ≠ c := fun c => by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  have hlimH : Tendsto (fun n => ∫ τ in Ioo 0 T, H τ * θ n τ) atTop
      (𝓝 (∫ τ in Ioo 0 T, H τ * (Ioo s t).indicator (fun _ => (1 : ℝ)) τ)) := by
    refine tendsto_integral_of_dominated_convergence (fun τ => ‖H τ‖)
      (fun n => hH.aestronglyMeasurable.mul (hθsmooth n).continuous.aestronglyMeasurable)
      hH.norm (fun n => Eventually.of_forall fun τ => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (θ n τ), abs_of_nonneg (hθ0 n τ)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hθ1 n τ)
    · filter_upwards [hne s, hne t] with τ h1 h2
      exact (hθlim τ h1 h2).const_mul (H τ)
  have hlimval : (∫ τ in Ioo 0 T, H τ * (Ioo s t).indicator (fun _ => (1 : ℝ)) τ) =
      ∫ τ in s..t, H τ := by
    have heq : (fun τ => H τ * (Ioo s t).indicator (fun _ => (1 : ℝ)) τ) =
        (Ioo s t).indicator H := by
      funext τ
      by_cases h : τ ∈ Ioo s t
      · rw [indicator_of_mem h, indicator_of_mem h, mul_one]
      · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
    rw [heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.2 (Ioo_subset_Ioo hs.le ht.le), intervalIntegral.integral_of_le hst.le,
      integral_Ioc_eq_integral_Ioo]
  rw [← hlimval]
  exact le_of_tendsto_of_tendsto' (hlimt.sub hlims) hlimH hineq

/-- A function continuous on [0,T] whose distributional derivative on
(0,T) is at most an integrable H increases between any two times by at
most the integral of H; used for the localized energy in
`lem:forced-tails`. -/
theorem forcedTails_increment_le_of_weak {T : ℝ} (hT : 0 < T) {Y H : ℝ → ℝ}
    (hY : ContinuousOn Y (Icc 0 T)) (hH : IntegrableOn H (Ioo 0 T))
    (hweak : ∀ θ : ℝ → ℝ, IsIntervalTest (Ioo 0 T) θ → (∀ τ, 0 ≤ θ τ) →
      -(∫ τ in Ioo 0 T, Y τ * deriv θ τ) ≤ ∫ τ in Ioo 0 T, H τ * θ τ) :
    ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → Y t - Y s ≤ ∫ τ in s..t, H τ := by
  have hHi : IntervalIntegrable H volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).2 hH
  let P : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..x, H τ
  have hPc : ContinuousOn P (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hHi left_mem_uIcc
    rwa [uIcc_of_le hT.le] at h
  have hsub : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∫ τ in s..t, H τ = P t - P s := by
    intro s hs t ht
    have hi : ∀ x ∈ Icc 0 T, IntervalIntegrable H volume 0 x := fun x hx =>
      hHi.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hT.le]; exact hx))
    exact (intervalIntegral.integral_interval_sub_left (hi t ht) (hi s hs)).symm
  let g : ℝ → ℝ → ℝ := fun s t => Y t - Y s - (P t - P s)
  have hgc1 : ∀ s, ContinuousOn (g s) (Icc 0 T) := fun s =>
    ((hY.sub continuousOn_const).sub (hPc.sub continuousOn_const))
  have hgc2 : ∀ t, ContinuousOn (fun s => g s t) (Icc 0 T) := fun t =>
    ((continuousOn_const.sub hY).sub (continuousOn_const.sub hPc))
  have hint : ∀ s t, 0 < s → s < t → t < T → g s t ≤ 0 := by
    intro s t hs hst ht
    have h := forcedTails_increment_le_interior hY hH hweak hs hst ht
    rw [hsub s ⟨hs.le, by linarith only [hst, ht]⟩ t ⟨by linarith only [hs, hst], ht.le⟩] at h
    change Y t - Y s - (P t - P s) ≤ 0
    linarith only [h]
  have hstep1 : ∀ s t, 0 < s → s < t → t ≤ T → g s t ≤ 0 := by
    intro s t hs hst ht
    rcases ht.lt_or_eq with ht | ht
    · exact hint s t hs hst ht
    · subst ht
      have hlim : Tendsto (g s) (𝓝[Ioo s t] t) (𝓝 (g s t)) :=
        ((hgc1 s t ⟨by linarith only [hs, hst], le_rfl⟩).mono
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc hs.le le_rfl))).tendsto
      rw [nhdsWithin_Ioo_eq_nhdsLT hst] at hlim
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hst] with x hx
      exact hint s x hs hx.1 hx.2
  have hstep2 : ∀ t, 0 < t → t ≤ T → g 0 t ≤ 0 := by
    intro t ht htT
    have hlim : Tendsto (fun s => g s t) (𝓝[Ioo 0 t] 0) (𝓝 (g 0 t)) :=
      ((hgc2 t 0 ⟨le_rfl, hT.le⟩).mono
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl htT))).tendsto
    rw [nhdsWithin_Ioo_eq_nhdsGT ht] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with x hx
    exact hstep1 x t hx.1 hx.2 htT
  intro s hs t ht hst
  rw [hsub s hs t ht]
  have key : g s t ≤ 0 := by
    rcases hst.lt_or_eq with hlt | heq
    · rcases hs.1.lt_or_eq with hs0 | hs0
      · exact hstep1 s t hs0 hlt ht.2
      · subst hs0
        exact hstep2 t hlt ht.2
    · subst heq
      change Y s - Y s - (P s - P s) ≤ 0
      simp
  change Y t - Y s - (P t - P s) ≤ 0 at key
  linarith only [key]

end CKN.Leray

end
