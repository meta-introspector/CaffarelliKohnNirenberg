-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedBesselGlobalPath
public import CKN.Leray.RegularisedBesselDerivativeL2Map

/-!
# Global higher regularity of the regularized solution

The global regularized mild solution issued from the mollified datum `J_ε a`
lies in `C([0,T]; H^k)` for every finite `T` and every integer `k`
(`thm:regularised`, global regularity): every spatial distributional
derivative `∂^α u(t)` with `|α| ≤ k` is a square-integrable field depending
continuously on `t ∈ [0,T]`. The derivatives are those of the complexified
field, which is how spatial distributions are formed here. The proof reads
them off the continuous lift of the curve to the Bessel potential space of
order `2k`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

open CKN CKN.Foundation.Parabolic

/-- `thm:regularised`, global regularity: for every integer `k` and every
finite `T`, the global regularized mild solution with initial state `J_ε a`
belongs to `C([0,T]; H^k)`. Every ordered coordinate derivative of order at
most `k` of its slice is a square-integrable field, continuous in time. -/
theorem regularised_higherRegularity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    let b₀ := realVectorL2OfCoordinateFunction
      (regUniformMollifiedInitial ρ ε hε a)
      (regMollifiedInitial_isInJ ρ ε hε ha).1
    let u : ℝ → RealVectorL2 := regularizedGlobalMildCurve ρ ε hε b₀
      (regUniformMollifiedInitial_mildJData ρ ε hε ha)
    ∀ α : List (Fin 3), α.length ≤ k →
      ∃ Dα : C(RegularizedMildTimeInterval T, ComplexVectorL2),
        ∀ t : RegularizedMildTimeInterval T,
          ((Dα t : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) =
            (α.map fun j => (WithLp.toLp 2 (basisVec j) : L2Vec3)).foldl
              (fun F m => ∂_{m} F)
              ((complexifyVectorL2 (u t.1) : ComplexVectorL2) :
                𝓢'(L2Vec3, ComplexVec3)) := by
  intro b₀ u α hα
  obtain ⟨v, hv⟩ := regUniformMollifiedInitial_global_bessel_path ρ ε hε a ha k T hT
  let αL : List L2Vec3 := α.map fun j => (WithLp.toLp 2 (basisVec j) : L2Vec3)
  have hαL : αL.length ≤ 2 * k := by
    simp only [αL, List.length_map]
    omega
  let D := regularisedBesselEvenOrderedDerivativeL2CLM k αL hαL
  refine ⟨⟨fun t => D (v t), D.continuous.comp v.continuous⟩, fun t => ?_⟩
  change ((regularisedBesselEvenOrderedDerivativeL2 k αL hαL (v t) : ComplexVectorL2) :
    𝓢'(L2Vec3, ComplexVec3)) = _
  rw [regularisedBesselEvenOrderedDerivativeL2_toDistr,
    regularisedOrderedDistributionDerivativeCLM_apply,
    ← regularisedBesselSobolevToL2_toTemperedDistribution_eq _ (by positivity)]
  have h := hv t
  rw [regularisedBesselSobolevToL2CLM_apply] at h
  rw [h]

end CKN.Leray
