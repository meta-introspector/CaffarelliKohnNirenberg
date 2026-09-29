-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedAssemblyMomentum
public import CKN.Leray.LerayAssemblyHopfData
public import CKN.Core.Caccioppoli.LocalBox
public import CKN.ClassEquivalence.TestSupport

/-!
# The forced weak momentum equation for the limit

This is the clause (FLH1) of `def:forced-leray-hopf` in the proof of
`thm:leray-forced`. For a solenoidal test supported in `ℝ³ × (0,T)` the
pressure term of the forced regularized identity `eq:reg-momentum-forced`
vanishes, and the limit passage of the forced momentum identity on a local
box around the support of the test applies with zero pressure.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The forced weak equation (FLH1) for the limit of the forced regularized
solutions, tested with solenoidal fields supported in `ℝ³ × (0,T)`. -/
theorem forcedHopf_momentum
    {T : ℝ} (U Jv : ℕ → ParabolicPoint → Vec3)
    (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3) (P : ℕ → ParabolicPoint → ℝ)
    (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (hmom : ∀ n, ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              Jv n z j * U n z i * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Dseq n z i j * spatialPartial (fun y => φ y i) j z
          - P n z * (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (hU3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hJ3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hu3 : ∀ s : ℝ, 0 < s → MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hUconv : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0))
    (hJconv : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0))
    (hD : ∀ s : ℝ, 0 < s → ∀ n, MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hDu : ∀ s : ℝ, 0 < s → MemLp Du 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))))
    (hweak : ∀ s : ℝ, 0 < s → ∀ i j, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) →
      Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
          Dseq n z i j * w z)
        atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s), Du z i j * w z)))
    (hf : ∀ s : ℝ, 0 < s → MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) :
    ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      (∀ z : ParabolicPoint,
        ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z = 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - ∑ i : Fin 3, f z i * φ z i = 0 := by
  intro φ hφ hdiv
  have hφpos : φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans (Set.prod_mono subset_rfl Ioo_subset_Ioi_self)⟩
  let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
  have hK : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
  have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    tsupport_parabolic_subset_spaceTimeSet hφpos
  obtain ⟨Ω', J, hbox, hKbox⟩ :=
    caccioppoli_localBox_of_compact_subset isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
  obtain ⟨δ, T', hδ, hδT', hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
  have hT' : 0 < T' := lt_trans hδ hδT'
  have hJT : J ⊆ Ioo 0 T' := fun t ht => ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
  have : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
    stability_localBox_finiteMeasure hbox
  have hle : (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω' J) ≤
      (volume : Measure ParabolicPoint).restrict
        (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T')) :=
    Measure.restrict_mono_set (volume : Measure ParabolicPoint)
      (Set.prod_mono (Set.subset_univ Ω') hJT)
  have hzero : ∀ n, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      (-(∑ i : Fin 3, U n z i * timePartial (fun y => φ y i) z))
        - ∑ i : Fin 3, ∑ j : Fin 3,
            Jv n z j * U n z i * spatialPartial (fun y => φ y i) j z
        + ∑ i : Fin 3, ∑ j : Fin 3,
            Dseq n z i j * spatialPartial (fun y => φ y i) j z
        - (fun _ : ParabolicPoint => (0 : ℝ)) z *
            (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
        - ∑ i : Fin 3, f z i * φ z i = 0 := by
    intro n
    have h := hmom n φ hφpos
    simp only [hdiv, mul_zero] at h ⊢
    exact h
  have hlim := forcedAssembly_momentum_limit hbox U Jv Dseq (fun _ _ => 0) u Du
    (fun _ => 0) f φ hφpos hKbox (fun n => (hU3 T' hT' n).mono_measure hle)
    (fun n => (hJ3 T' hT' n).mono_measure hle) ((hu3 T' hT').mono_measure hle)
    (by simpa only [ENNReal.ofReal_ofNat] using
      lerayAssembly_strongConv_localBox hJT U u (hUconv T' hT'))
    (by simpa only [ENNReal.ofReal_ofNat] using
      lerayAssembly_strongConv_localBox hJT Jv u (hJconv T' hT'))
    (fun n => (hD T' hT' n).mono_measure hle) ((hDu T' hT').mono_measure hle)
    (fun i j w hw => lerayAssembly_weakConv_localBox_all hbox hJT
      (fun n z => Dseq n z i j) (fun z => Du z i j) (hweak T' hT' i j) w hw)
    (fun _ => MemLp.zero) MemLp.zero
    (by simpa only [sub_self, eLpNorm_zero] using tendsto_const_nhds)
    ((hf T' hT').mono_measure hle) hzero
  simp only [hdiv, mul_zero, sub_zero] at hlim
  have hsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
    Set.prod_mono subset_rfl Ioo_subset_Ioi_self
  have hmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hsub] at hlim
  · exact hlim
  · intro z hz
    have hzK : (z : Vec3 × ℝ) ∉ tsupport (show Vec3 × ℝ → Vec3 from φ) := fun h =>
      hz.2 (hφ.2.2 h)
    have hoff : ∀ i, (z : Vec3 × ℝ) ∉ tsupport (fun w : Vec3 × ℝ => φ w i) := fun i h =>
      hzK (tsupport_component_subset (V := ℝ) (show Vec3 × ℝ → Vec3 from φ) i (fun _ h => by rw [h]; rfl) h)
    have hφz : φ z = 0 :=
      image_eq_zero_of_notMem_tsupport (f := (show Vec3 × ℝ → Vec3 from φ)) hzK
    have ht : ∀ i, timePartial (fun w => φ w i) z = 0 := fun i =>
      timePartial_eq_zero_off_tsupport (hoff i)
    have hs : ∀ i j, spatialPartial (fun w => φ w i) j z = 0 := fun i j =>
      spatialPartial_eq_zero_off_tsupport (hoff i) j
    simp only [ht, hs, hφz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero,
      sub_zero, add_zero]
