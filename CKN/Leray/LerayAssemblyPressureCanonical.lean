-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.LerayAssemblyContracts
public import CKN.Leray.RieszPressurePackageAgreement

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The finite-slab canonical pressure formed from a Leray--Hopf velocity
belongs to space-time L^(5/3), as in `thm:assoc-pressure`. Its L^(3/2) Riesz
representative agrees with the representative from the L^(5/3) tensor
extension. -/
theorem lerayProductPressureOnSlab_memLp_fiveThirds
    {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hLH : IsLerayHopfSolution T a u Du)
    (hu : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 3
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))) :
    MemLp
      (lerayProductPressureOnSlab T
        (fun z => u (parabolicHomeomorph.symm z))
        (fun z => u (parabolicHomeomorph.symm z)) hu hu)
      (ENNReal.ofReal (5 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) := by
  let v : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j =>
    (lerayPressureLimitSlab T).indicator (fun z => v z i * v z j)
  have hSet : parabolicHomeomorph.symm ⁻¹'
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) =
        lerayPressureLimitSlab T := by
    ext z
    change ((z.1, z.2) : ParabolicPoint) ∈
        (Set.univ : Set Vec3) ×ˢ Ioo 0 T ↔
      z ∈ (Set.univ : Set Vec3) ×ˢ Ioo 0 T
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_Ioo]
  have hF_eq (i j : Fin 3) (z : Vec3 × ℝ) :
      F i j z = associatedPressureTensor T u i j z := by
    simp [F, v, associatedPressureTensor, hSet]
  have hF32 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    simpa only [F, v, lerayPressureLimitSlab] using
      (rieszPressureSpaceTime_product_memLp_of_slab
        (MeasurableSet.univ.prod measurableSet_Ioo)
        (fun z => u (parabolicHomeomorph.symm z))
        (fun z => u (parabolicHomeomorph.symm z))
        (fun i => hu.eval i) (fun j => hu.eval j))
  have hF53 : ∀ i j, MemLp (F i j) (ENNReal.ofReal (5 / 3 : ℝ))
      (volume : Measure (Vec3 × ℝ)) := by
    intro i j
    have hbase := associatedPressureTensor_memLp_fiveThirds hLH i j
    have hAE : F i j =ᵐ[volume] associatedPressureTensor T u i j :=
      Filter.Eventually.of_forall (hF_eq i j)
    exact (memLp_congr_ae hAE).2 hbase
  have hAgree := rieszPressureSpaceTime_ae_eq_of_memLp_common
    (3 / 2 : ℝ) (by norm_num) (5 / 3 : ℝ) (by norm_num) F hF32 hF53
  have hAgreeSlab :=
    ae_restrict_of_ae (s := lerayPressureLimitSlab T) hAgree
  have hP53 := rieszPressureSpaceTime_memLp
    (5 / 3 : ℝ) (by norm_num) F hF53
  have hP53Slab : MemLp
      (rieszPressureSpaceTime (5 / 3 : ℝ) (by norm_num) F hF53)
      (ENNReal.ofReal (5 / 3 : ℝ))
      ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T)) :=
    hP53.restrict _
  change MemLp
    (rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF32)
    (ENNReal.ofReal (5 / 3 : ℝ))
    ((volume : Measure (Vec3 × ℝ)).restrict (lerayPressureLimitSlab T))
  simpa only [lerayProductPressureOnSlab, F, v] using
    (memLp_congr_ae hAgreeSlab).2 hP53Slab

end CKN.Leray

namespace CKN

/-- The pressure selected by the Leray pressure limit is the canonical product
Riesz pressure. It has space-time L^(5/3) on each finite slab, the pressure
clause of `thm:leray` supplied by `thm:assoc-pressure`. -/
theorem lerayExistence_canonicalPressure_memLp_fiveThirds
    (ρ : CKN.Leray.RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → ℝ)
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (_hεseq : Tendsto εseq atTop (nhds 0)),
      ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
        ∃ Du : ParabolicPoint → Fin 3 → Vec3,
        StrictMono σ ∧ Tendsto σ atTop atTop ∧
        Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
        (∀ x : Vec3, u (x, 0) = a x) ∧
        (∀ T : ℝ, 0 < T →
          let μ : Measure ParabolicPoint :=
            volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
          let U : ℕ → ParabolicPoint → Vec3 :=
            fun n => uε a ha (εseq (σ n))
          let J : ℕ → ParabolicPoint → Vec3 := fun n =>
            CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
              (by exact (hseq (σ n)).1) (U n)
          let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n z i j =>
            spatialPartial (fun y => U n y i) j z
          AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
          MemLp u 2 μ ∧ MemLp Du 2 μ ∧
          Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
          (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
            Tendsto (fun n => ∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
              atTop (nhds (∫ z in spaceTimeSet
                (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
          (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
            Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
              atTop (nhds 0)) ∧
          (∀ n, MemLp (U n) 3 μ) ∧
          (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
          Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
          (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
            MemLp w 2 volume →
            Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
                U n (x, t) i * w x i) atTop
              (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
          (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
            HasWeakGradientOn (Set.univ : Set Vec3)
              (fun x => u (x, t) i) (fun x => Du (x, t) i))) ∧
        (∀ z : Vec3 × ℝ, 0 < z.2 →
          u (parabolicHomeomorph.symm z) =
            CKN.Leray.compactnessMollifiedLimit
              (fun n => fun y =>
                uε a ha (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z))
    (hpressureLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (uε a ha (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (uε a ha (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0)),
      ∃ p : ParabolicPoint → ℝ,
        ∀ T : ℝ, 0 < T →
          let μ : Measure (Vec3 × ℝ) :=
            (volume : Measure (Vec3 × ℝ)).restrict
              (CKN.Leray.lerayPressureLimitSlab T)
          let uST : Vec3 × ℝ → Vec3 := fun z => u (parabolicHomeomorph.symm z)
          let pST : Vec3 × ℝ → ℝ := fun z => p (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            pε a ha (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp pST (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST =ᵐ[μ] CKN.Leray.lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0))
    (hhopfLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0)),
      let hlim := hlerayLimit a ha εseq hseq hεseq
      let _σ := Classical.choose hlim
      let hlim₁ := Classical.choose_spec hlim
      let u := Classical.choose hlim₁
      let hlim₂ := Classical.choose_spec hlim₁
      let Du := Classical.choose hlim₂
      ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du) :
    ∀ a : Vec3 → Vec3, IsInJ a →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ T : ℝ, 0 < T →
          ∃ hu : MemLp (fun z : Vec3 × ℝ =>
              u (parabolicHomeomorph.symm z)) 3
              ((volume : Measure (Vec3 × ℝ)).restrict
                (CKN.Leray.lerayPressureLimitSlab T)),
            (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) =ᵐ[
              (volume : Measure (Vec3 × ℝ)).restrict
                (CKN.Leray.lerayPressureLimitSlab T)]
              CKN.Leray.lerayProductPressureOnSlab T
                (fun z => u (parabolicHomeomorph.symm z))
                (fun z => u (parabolicHomeomorph.symm z)) hu hu ∧
            MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
              (volume.restrict
                (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  intro a ha
  let εseq : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1 := by
    intro n
    constructor
    · dsimp [εseq]
      positivity
    · dsimp [εseq]
      have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
      simpa only [ge_iff_le, one_div, ne_eq, one_ne_zero, not_false_eq_true, div_self] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
  have hεseq : Tendsto εseq atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let hlim := hlerayLimit a ha εseq hseq hεseq
  let σ := Classical.choose hlim
  let hlim₁ := Classical.choose_spec hlim
  let u := Classical.choose hlim₁
  let hlim₂ := Classical.choose_spec hlim₁
  let Du := Classical.choose hlim₂
  let hlimData := Classical.choose_spec hlim₂
  have hσ : StrictMono σ := hlimData.1
  have hσtop : Tendsto σ atTop atTop := hlimData.2.1
  have hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0) :=
    hlimData.2.2.1
  have hlimitOn (T : ℝ) (hT : 0 < T) := hlimData.2.2.2.2.1 T hT
  have hUseqLthree : ∀ T : ℝ, 0 < T →
      Tendsto (fun n => eLpNorm
        (uε a ha (εseq (Classical.choose hlim n)) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, hLq, _, _, _, _, _, _⟩
    have h := hLq 3 (by norm_num) (by norm_num)
    change Tendsto (fun n => eLpNorm
      (uε a ha (εseq (Classical.choose hlim n)) -
        Classical.choose (Classical.choose_spec hlim))
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
      ) atTop (nhds 0) at h
    simpa only [parabolicHomeomorph_symm_apply, measurableSet_Ioi, ae_restrict_eq,
      eventually_all, Prod.mk.eta, Prod.forall, exists_and_left, exists_and_right,
      ENNReal.ofReal_ofNat] using h
  have hJseqLthree : ∀ T : ℝ, 0 < T →
      Tendsto (fun n => eLpNorm
        (CKN.Leray.regUniformMollifiedVelocity ρ
          (εseq (Classical.choose hlim n))
          (by exact (hseq (Classical.choose hlim n)).1)
          (uε a ha (εseq (Classical.choose hlim n))) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, _, _, _, _, hJconv, _, _⟩
    simpa only [parabolicHomeomorph_symm_apply, measurableSet_Ioi, ae_restrict_eq,
      eventually_all, Prod.mk.eta, Prod.forall, exists_and_left, exists_and_right,
      ENNReal.ofReal_ofNat] using hJconv
  obtain ⟨p, hpLimit⟩ := hpressureLimit a ha εseq hseq hεseq
    (Classical.choose hlim) (Classical.choose (Classical.choose_spec hlim))
    hσ hσtop hεsubseq hUseqLthree hJseqLthree
  have hglobal : IsGlobalLerayHopfSolution a u Du := by
    intro T hT
    exact hhopfLimit a ha εseq hseq hεseq T hT
  have hpFiveThirds : ∀ T : ℝ, 0 < T →
      ∃ hu : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 3
          ((volume : Measure (Vec3 × ℝ)).restrict
            (CKN.Leray.lerayPressureLimitSlab T)),
        (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z)) =ᵐ[
          (volume : Measure (Vec3 × ℝ)).restrict
            (CKN.Leray.lerayPressureLimitSlab T)]
          CKN.Leray.lerayProductPressureOnSlab T
            (fun z => u (parabolicHomeomorph.symm z))
            (fun z => u (parabolicHomeomorph.symm z)) hu hu ∧
        MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    intro T hT
    rcases hpLimit T hT with ⟨hu, _, hcanonical, _⟩
    have hLH : IsLerayHopfSolution T a u Du :=
      hhopfLimit a ha εseq hseq hεseq T hT
    have hproduct := CKN.Leray.lerayProductPressureOnSlab_memLp_fiveThirds hLH hu
    have hpST : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
        (ENNReal.ofReal (5 / 3 : ℝ))
        ((volume : Measure (Vec3 × ℝ)).restrict
          (CKN.Leray.lerayPressureLimitSlab T)) :=
      (memLp_congr_ae hcanonical).2 hproduct
    exact ⟨hu, hcanonical,
      CKN.Leray.lerayAssembly_productSlab_memLp_to_parabolic hpST⟩
  exact ⟨u, Du, p, hglobal, hpFiveThirds⟩

end CKN

end
