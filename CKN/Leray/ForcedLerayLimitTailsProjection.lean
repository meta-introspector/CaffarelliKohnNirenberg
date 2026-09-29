-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.JSpaceMollify
public import CKN.Leray.ForcedRegularisedCancellation
public import CKN.Leray.StabilityBoundedPairing
public import CKN.Pressure.LeibnizLaplacian

/-!
# The projection cancellation for the force pressure

`eq:forced-projection-cancellation` in the proof of `lem:forced-tails`: if a
scalar P has the square-integrable weak gradient G and v is a weakly
divergence-free L² field, then for every smooth compactly supported weight
q, ∫ P v·∇q = -∫ (G·v) q. With P the force pressure and G = (I - ℙ) f
this combines the force-pressure flux with the force work into the work of
the projected force. The proof mollifies v, which keeps it divergence free,
tests the weak gradient with the smooth fields v_ε,i q, and passes to the
limit in L².
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- `eq:forced-projection-cancellation`: for a scalar P that is square
integrable on a compact K and has the weak gradient G ∈ L², a weakly
divergence-free v ∈ L², and a smooth weight q supported in K,
∫ P v·∇q = -∫ (G·v) q. -/
theorem forcedTails_projection_cancellation {P : Vec3 → ℝ} {G v : Vec3 → Vec3}
    {q : Vec3 → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) {K : Set Vec3} (hK : IsCompact K)
    (hqK : tsupport q ⊆ K) (hP : MemLp P 2 (volume.restrict K)) (hG : MemLp G 2 volume)
    (hPG : HasWeakGradientOn (Set.univ : Set Vec3) P G) (hv : IsWeakDivFreeL2 v) :
    ∫ x : Vec3, P x * ∑ i : Fin 3, v x i * spatialDeriv q i x =
      -∫ x : Vec3, ∑ i : Fin 3, G x i * v x i * q x := by
  have hqc : HasCompactSupport q := IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hqK
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hdqc : ∀ i, HasCompactSupport (spatialDeriv q i) := fun i =>
    hqc.fderiv_apply (𝕜 := ℝ) _
  have hdqK : ∀ i, tsupport (spatialDeriv q i) ⊆ K := fun i =>
    (tsupport_fderiv_apply_subset ℝ _).trans hqK
  have hdqcont : ∀ i, Continuous (spatialDeriv q i) := fun i =>
    (contDiff_spatialDeriv_smooth hq i).continuous
  have hdq0 : ∀ i x, x ∉ K → spatialDeriv q i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hdqK i h)
  obtain ⟨Cq, hCq⟩ := hq.continuous.bounded_above_of_compact_support hqc
  -- P times a bounded continuous function supported in K
  have hPmul : ∀ g : Vec3 → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ K →
      MemLp (fun x => P x * g x) 2 (volume.restrict K) ∧
        Integrable (fun x => P x * g x) := by
    intro g hg hgc hgK
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
    have hm : MemLp (fun x => P x * g x) 2 (volume.restrict K) := by
      refine (hP.const_mul C).of_le (hP.aestronglyMeasurable.mul
        hg.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, norm_mul, Real.norm_eq_abs C, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (norm_nonneg _)
    refine ⟨hm, ?_⟩
    have hon : IntegrableOn (fun x => P x * g x) K :=
      stability_integrable_mul_bounded_test (volume.restrict K) (by norm_num) hP
        (memLp_top_of_bound hg.aestronglyMeasurable C (ae_of_all _ hC))
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
    intro x hx
    by_contra hxK
    exact hx (by simp [image_eq_zero_of_notMem_tsupport fun h => hxK (hgK h)])
  have hGq : ∀ i, MemLp (fun x => G x i * q x) 2 volume := by
    intro i
    refine ((hG.eval i).const_mul Cq).of_le ((hG.eval i).aestronglyMeasurable.mul
      hq.continuous.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, Real.norm_eq_abs Cq, mul_comm (|Cq|)]
    exact mul_le_mul_of_nonneg_left ((hCq x).trans (le_abs_self Cq)) (norm_nonneg _)
  -- the two sides as sums of L² pairings
  have hconvL : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ∫ x : Vec3, P x * ∑ i : Fin 3, w x i * spatialDeriv q i x =
        ∑ i : Fin 3, ∫ x in K, w x i * (P x * spatialDeriv q i x) := by
    intro w hw
    have hint : ∀ i, Integrable (fun x => w x i * (P x * spatialDeriv q i x)) := by
      intro i
      have hon : IntegrableOn (fun x => w x i * (P x * spatialDeriv q i x)) K :=
        ((hw.eval i).mono_measure Measure.restrict_le_self).integrable_mul
          (hPmul _ (hdqcont i) (hdqc i) (hdqK i)).1
      refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
      intro x hx
      by_contra hxK
      exact hx (by simp [hdq0 i x hxK])
    calc ∫ x : Vec3, P x * ∑ i : Fin 3, w x i * spatialDeriv q i x
        = ∫ x : Vec3, ∑ i : Fin 3, w x i * (P x * spatialDeriv q i x) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin 3, ∫ x : Vec3, w x i * (P x * spatialDeriv q i x) :=
          integral_finsetSum _ fun i _ => hint i
      _ = ∑ i : Fin 3, ∫ x in K, w x i * (P x * spatialDeriv q i x) :=
          Finset.sum_congr rfl fun i _ =>
            (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
              simp [hdq0 i x hx]).symm
  have hconvR : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ∫ x : Vec3, ∑ i : Fin 3, G x i * w x i * q x =
        ∑ i : Fin 3, ∫ x : Vec3, w x i * (G x i * q x) := by
    intro w hw
    calc ∫ x : Vec3, ∑ i : Fin 3, G x i * w x i * q x
        = ∫ x : Vec3, ∑ i : Fin 3, w x i * (G x i * q x) :=
          integral_congr_ae (Eventually.of_forall fun x =>
            Finset.sum_congr rfl fun i _ => by ring)
      _ = ∑ i : Fin 3, ∫ x : Vec3, w x i * (G x i * q x) :=
          integral_finsetSum _ fun i _ => (hw.eval i).integrable_mul (hGq i)
  -- the identity for the mollified fields
  let V : ℕ → Vec3 → Vec3 := fun n =>
    CKN.spatialMollifyVec3 v (1 / ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hVs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (V n) := fun n =>
    CKN.spatialMollifyVec3_contDiff (by positivity) hv.1
  have hVL : ∀ n, MemLp (V n) 2 volume := fun n =>
    CKN.spatialMollifyVec3_memLp (by positivity) hv.1
  have hVdiv : ∀ n x, ∑ i : Fin 3, spatialDeriv (fun y => V n y i) i x = 0 := fun n x =>
    CKN.spatialMollifyVec3_divergence_eq_zero (by positivity) hv x
  have hkey : ∀ n, ∫ x : Vec3, P x * ∑ i : Fin 3, V n x i * spatialDeriv q i x =
      -∫ x : Vec3, ∑ i : Fin 3, G x i * V n x i * q x := by
    intro n
    have hVi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun y => V n y i) := fun i =>
      contDiff_pi.1 (hVs n) i
    let φ : Fin 3 → Vec3 → ℝ := fun i x => V n x i * q x
    have hφs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i) := fun i => (hVi i).mul hq
    have hφc : ∀ i, HasCompactSupport (φ i) := fun i => hqc.mul_left
    have hφK : ∀ i, tsupport (φ i) ⊆ K := fun i =>
      (closure_mono (Function.support_mul_subset_right _ _)).trans hqK
    have hderiv : ∀ i x, (fderiv ℝ (φ i) x) (basisVec i) =
        spatialDeriv (fun y => V n y i) i x * q x + V n x i * spatialDeriv q i x := fun i x =>
      spatialDeriv_mul ((hVi i).differentiable (by simp) x)
        (hq.differentiable (by simp) x) i
    have hweak : ∀ i, ∫ x : Vec3, P x * (fderiv ℝ (φ i) x) (basisVec i) =
        -∫ x : Vec3, G x i * φ i x := by
      intro i
      have h := hPG i (φ i) (hφs i) (hφc i) (subset_univ _)
      simpa only [Measure.restrict_univ] using h
    have hint : ∀ i, Integrable (fun x => P x * (fderiv ℝ (φ i) x) (basisVec i)) := fun i =>
      (hPmul _ (contDiff_spatialDeriv_smooth (hφs i) i).continuous
        ((hφc i).fderiv_apply (𝕜 := ℝ) _)
        ((tsupport_fderiv_apply_subset ℝ _).trans (hφK i))).2
    have hintG : ∀ i, Integrable (fun x => G x i * φ i x) := fun i =>
      (hG.eval i).integrable_mul ((hφs i).continuous.memLp_of_hasCompactSupport (p := 2) (hφc i))
    calc ∫ x : Vec3, P x * ∑ i : Fin 3, V n x i * spatialDeriv q i x
        = ∫ x : Vec3, ∑ i : Fin 3, P x * (fderiv ℝ (φ i) x) (basisVec i) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hderiv, Fin.sum_univ_three]
          have hd := hVdiv n x
          rw [Fin.sum_univ_three] at hd
          linear_combination (-(P x * q x)) * hd
      _ = ∑ i : Fin 3, ∫ x : Vec3, P x * (fderiv ℝ (φ i) x) (basisVec i) :=
          integral_finsetSum _ fun i _ => hint i
      _ = ∑ i : Fin 3, -∫ x : Vec3, G x i * φ i x := Finset.sum_congr rfl fun i _ => hweak i
      _ = -∫ x : Vec3, ∑ i : Fin 3, G x i * V n x i * q x := by
          rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hintG i]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun x =>
            Finset.sum_congr rfl fun i _ => ?_)
          simp only [φ]
          ring
  -- passage to the limit
  have hconv := CKN.spatialMollifyVec3_tendsto_L2 hv.1
  have hcomp : ∀ (μ : Measure Vec3), μ ≤ volume → ∀ i,
      Tendsto (fun n => eLpNorm (fun x => V n x i - v x i) 2 μ) atTop (𝓝 0) := by
    intro μ hμ i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    refine (eLpNorm_mono_measure _ hμ).trans (eLpNorm_mono
      (((hVL n).eval i).sub (hv.1.eval i)).aestronglyMeasurable fun x => ?_)
    exact norm_le_pi_norm (V n x - v x) i
  have hL : Tendsto (fun n => ∑ i : Fin 3, ∫ x in K, V n x i * (P x * spatialDeriv q i x))
      atTop (𝓝 (∑ i : Fin 3, ∫ x in K, v x i * (P x * spatialDeriv q i x))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    exact tendsto_integral_mul_of_tendsto_eLpNorm_two (μ := volume.restrict K)
      (fun n x => V n x i) (fun _ x => P x * spatialDeriv q i x) (fun x => v x i)
      (fun x => P x * spatialDeriv q i x)
      (fun n => ((hVL n).eval i).mono_measure Measure.restrict_le_self)
      (fun _ => (hPmul _ (hdqcont i) (hdqc i) (hdqK i)).1)
      ((hv.1.eval i).mono_measure Measure.restrict_le_self)
      (hPmul _ (hdqcont i) (hdqc i) (hdqK i)).1
      (hcomp _ Measure.restrict_le_self i) (by simp)
  have hR : Tendsto (fun n => -∑ i : Fin 3, ∫ x : Vec3, V n x i * (G x i * q x))
      atTop (𝓝 (-∑ i : Fin 3, ∫ x : Vec3, v x i * (G x i * q x))) := by
    refine (tendsto_finsetSum _ fun i _ => ?_).neg
    exact tendsto_integral_mul_of_tendsto_eLpNorm_two (μ := volume)
      (fun n x => V n x i) (fun _ x => G x i * q x) (fun x => v x i)
      (fun x => G x i * q x) (fun n => (hVL n).eval i) (fun _ => hGq i) (hv.1.eval i)
      (hGq i) (hcomp _ le_rfl i) (by simp)
  have heq : ∀ n, ∑ i : Fin 3, ∫ x in K, V n x i * (P x * spatialDeriv q i x) =
      -∑ i : Fin 3, ∫ x : Vec3, V n x i * (G x i * q x) := fun n => by
    rw [← hconvL (V n) (hVL n), ← hconvR (V n) (hVL n)]
    exact hkey n
  rw [hconvL v hv.1, hconvR v hv.1]
  exact tendsto_nhds_unique (hL.congr heq) hR

end CKN.Leray

end
