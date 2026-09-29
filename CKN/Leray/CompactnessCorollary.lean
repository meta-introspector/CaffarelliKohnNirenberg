-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.CompactnessMain
public import CKN.Leray.CompactnessLp

@[expose] public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

set_option autoImplicit false

namespace CKN.Leray

/-- A uniform local `L^(10/3)` bound upgrades the selected strong local
`L²` convergence to every exponent below `10/3`. This is
`cor:compactness-Lq`. -/
theorem cor_compactness_Lq_of_local_energy
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U)
    (hI : IsOpen I) (hIconn : OrdConnected I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (hDuMeas : ∀ n, Measurable (Du n))
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ Icc a b →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hgradBound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∃ G : ℝ≥0∞, G < ⊤ ∧ ∀ n,
        (∫⁻ t in Icc a b, ∫⁻ x in C,
          ENNReal.ofReal (CKN.spatialGradientSq (u n) (Du n) (x,t))
            ∂volume) ≤ G)
    (hmod : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ a b : ℝ, Icc a b ⊆ I →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
        ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
          |(∫ x : Vec3, ∑ i : Fin 3, u n (x,t) i * w x i ∂volume) -
            (∫ x : Vec3, ∑ i : Fin 3, u n (x,s) i * w x i ∂volume)| ≤
            A * dist t s + B * (dist t s) ^ θ)
    (hhigh : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
      ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
        eLpNorm (fun z => (WithLp.toLp 2 (u n z) : L2Vec3))
          (10 / 3 : ℝ≥0∞) (volume.restrict Q) ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
    ∃ v : Vec3 × ℝ → Vec3, Measurable v ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
        Tendsto (fun k => eLpNorm
          ((fun z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
            (fun z => (WithLp.toLp 2 (v z) : L2Vec3))) 2
          (volume.restrict Q)) atTop (nhds 0)) ∧
      (∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
        ∀ p : ℝ≥0∞, 1 ≤ p → p < (10 / 3 : ℝ≥0∞) →
          Tendsto (fun k => eLpNorm
            ((fun z => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
              (fun z => (WithLp.toLp 2 (v z) : L2Vec3))) p
            (volume.restrict Q)) atTop (nhds 0)) := by
  obtain ⟨σ, hσ, v, hv, g, hg, hweak, hstrong, hgrad,
      hweakGradLimit, hcont, hslicebound, hgradientbound⟩ :=
    lem_compactness hU hI hIconn u Du huMeas hDuMeas
      hweakGrad hbound hgradBound hmod
  refine ⟨σ, hσ, v, hv, hstrong, ?_⟩
  intro Q hQ hQI p hp hpr
  let : IsFiniteMeasure ((volume : Measure (Vec3 × ℝ)).restrict Q) :=
    isFiniteMeasure_restrict.mpr hQ.measure_lt_top.ne
  obtain ⟨B, hB, hBb⟩ := hhigh Q hQ hQI
  exact tendsto_eLpNorm_sub_of_tendsto_two_of_uniform_ten_thirds
    ⟨B, hB, fun k => hBb (σ k)⟩
    (hstrong Q hQ hQI) p hp hpr

end CKN.Leray
