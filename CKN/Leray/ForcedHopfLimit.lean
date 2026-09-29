-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedHopfContinuity
public import CKN.Leray.ForcedHopfEnergy
public import CKN.Leray.ForcedHopfMomentum
public import CKN.Leray.LerayHopfLimitPropClass
public import CKN.Leray.LerayHopfLimitPropMollifier
public import CKN.Leray.LerayHopfLimitPropPairingModulus
public import CKN.Leray.RegularisedInitialData
public import CKN.Leray.FourierCoordinateL2Bridge
public import CKN.Leray.CompactnessRepresentative
public import CKN.Leray.RieszPressurePackageForce
public import CKN.Leray.JSpaceFourierLimit
public import CKN.Statements.IsForcedLerayHopfSolution
public import CKN.Statements.IsLocallySquareIntegrableForce

/-!
# The forced limit is a forced Leray--Hopf solution

This is the Leray--Hopf part of the proof of `thm:leray-forced`: for the
subsequence and limit fields of `prop:forced-limit`, and every `T > 0`, the
limit satisfies the clauses of `def:forced-leray-hopf` on `ℝ³ × [0,T]`. The
inputs are the forced regularized solutions of `lem:regularised-forced` with
their energy inequality `eq:reg-energy-forced`, the weak momentum identity
`eq:reg-momentum-forced`, and the convergence statements of
`prop:forced-limit`. The regularized solutions are only continuous `L²` mild
solutions, so weak continuity (LH2) comes from the weak momentum identity as
in `lem:forced-equicontinuity`; the work term of (FLH2) passes to the limit by
strong `L²` convergence, and (LH5) follows from (FLH2) and weak continuity
at `0`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The forced Leray--Hopf limit in `thm:leray-forced`: the limit fields of
`prop:forced-limit` are, on every finite slab, a forced Leray--Hopf solution
with the given datum and force. -/
theorem lerayHopfLimitForced
    (ρ : CKN.Leray.RegMollifierProfile)
    (pF : (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ParabolicPoint → ℝ)
    (uε : (a : Vec3 → Vec3) → IsInJ a →
      (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ℝ → ParabolicPoint → Vec3)
    (Duε : (a : Vec3 → Vec3) → IsInJ a →
      (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ℝ → ParabolicPoint → Fin 3 → Vec3)
    (pε : (a : Vec3 → Vec3) → IsInJ a →
      (f : ParabolicPoint → Vec3) → IsLocallySquareIntegrableForce f →
      ℝ → ParabolicPoint → ℝ)
    (hregularised : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε),
      let u := uε a ha f hf ε
      let Du := Duε a ha f hf ε
      let p := pε a ha f hf ε
      (∃ hSlice : ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => u (x, t)) 2 volume,
        Continuous (fun t : Set.Ici (0 : ℝ) =>
          CKN.Leray.realVectorL2OfCoordinateFunction
            (fun x : Vec3 => u (x, t.1)) (hSlice t.1 t.2)) ∧
        (fun x : Vec3 => u (x, 0)) =ᵐ[volume]
          CKN.Leray.regUniformMollifiedInitial ρ ε hε a ∧
        ∀ t : ℝ, 0 ≤ t → CKN.IsWeakDivFreeL2 (fun x => u (x, t))) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) ∧
      (∀ T : ℝ, 0 < T →
        MemLp Du 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp (fun z => p z - pF f hf z) 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) ∧
      (∀ t : ℝ, 0 < t →
        ∃ hF : ∀ i j : Fin 3, MemLp
            (fun x : Vec3 =>
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                u (x, t) j) (ENNReal.ofReal (2 : ℝ)) volume,
          (fun x : Vec3 => p (x, t) - pF f hf (x, t)) =ᵐ[volume]
            CKN.Leray.rieszPressureSliceRepresentative (2 : ℝ) (by norm_num)
              (fun i j => (hF i j).toLp
                (fun x : Vec3 =>
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j)) ∧
          ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
            (∫ x : Vec3, (p (x, t) - pF f hf (x, t)) *
                spatialLaplacian ψ x) =
              -∑ i : Fin 3, ∑ j : Fin 3,
                ∫ x : Vec3,
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε u (x, t) i *
                    u (x, t) j * mixedSecond ψ i j x) ∧
      (∀ t : ℝ, 0 ≤ t →
        eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
            2 * CKN.Leray.regUniformDissipation u Du t < ⊤ ∧
          (eLpNorm (CKN.Leray.regUniformVelocitySlice u t) 2 volume ^ (2 : ℕ) +
            2 * CKN.Leray.regUniformDissipation u Du t).toReal ≤
            (eLpNorm (CKN.Leray.regMollifyVector ρ ε hε
              (CKN.Leray.regUniformSpatialField a)) 2 volume ^ (2 : ℕ)).toReal +
            2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
              ∑ i : Fin 3, f z i * u z i))
    (hregMomentum : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε) (φ : ParabolicPoint → Vec3),
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i : Fin 3, uε a ha f hf ε z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                (uε a ha f hf ε) z j * uε a ha f hf ε z i *
                spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Duε a ha f hf ε z i j * spatialPartial (fun y => φ y i) j z
          - pε a ha f hf ε z *
              (∑ i : Fin 3, spatialPartial (fun y => φ y i) i z)
          - ∑ i : Fin 3, f z i * φ z i = 0)
    (hlerayLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
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
            fun n => uε a ha f hf (εseq (σ n))
          let J : ℕ → ParabolicPoint → Vec3 := fun n =>
            CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
              (by exact (hseq (σ n)).1) (U n)
          let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
            Duε a ha f hf (εseq (σ n))
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
                uε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z)) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0)),
      let hlim := hlerayLimit a ha f hf εseq hseq hεseq
      let _σ := Classical.choose hlim
      let hlim₁ := Classical.choose_spec hlim
      let u := Classical.choose hlim₁
      let hlim₂ := Classical.choose_spec hlim₁
      let Du := Classical.choose hlim₂
      ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du := by
  intro a ha f hf εseq hseq hεseq hlim σ hlim₁ u hlim₂ Du T hT
  obtain ⟨-, hσtop, hεsub, hu0, hslabAll, hrep⟩ := Classical.choose_spec hlim₂
  have hu0' : ∀ x, u (x, 0) = a x := hu0
  have hεn : ∀ n, 0 < εseq (σ n) := fun n => (hseq (σ n)).1
  let U : ℕ → ParabolicPoint → Vec3 := fun n => uε a ha f hf (εseq (σ n))
  let Jv : ℕ → ParabolicPoint → Vec3 := fun n =>
    regUniformMollifiedVelocity ρ (εseq (σ n)) (hεn n) (U n)
  let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n => Duε a ha f hf (εseq (σ n))
  let Pseq : ℕ → ParabolicPoint → ℝ := fun n => pε a ha f hf (εseq (σ n))
  have hR := fun n => hregularised a ha f hf (εseq (σ n)) (hεn n)
  have hSliceMem : ∀ n t, 0 ≤ t → MemLp (fun x => U n (x, t)) 2 volume :=
    fun n => (hR n).1.1
  have hSliceCont := fun n => (hR n).1.2.1
  have hSlice0 := fun n => (hR n).1.2.2.1
  have hSliceDiv : ∀ n t, 0 ≤ t → IsWeakDivFreeL2 (fun x => U n (x, t)) :=
    fun n => (hR n).1.2.2.2
  have hL2n : ∀ n (s : ℝ), 0 < s → MemLp (Dseq n) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun n s hs => ((hR n).2.2.1 s hs).1
  have hEn := fun n => (hR n).2.2.2.2
  -- the convergence data on every slab
  have hU3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (U n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun s hs => (hslabAll s hs).2.2.2.2.2.2.2.1
  have hJ3 : ∀ s : ℝ, 0 < s → ∀ n, MemLp (Jv n) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun s hs => (hslabAll s hs).2.2.2.2.2.2.2.2.1
  have hu3 : ∀ s : ℝ, 0 < s → MemLp u 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun s hs => (hslabAll s hs).2.2.2.2.2.2.2.2.2.1
  have hUconv3 : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (U n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0) := by
    intro s hs
    have h := (hslabAll s hs).2.2.2.2.2.2.1 3 (by norm_num) (by norm_num)
    rw [ENNReal.ofReal_ofNat] at h
    exact h
  have hJconv : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (Jv n - u) 3
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0) :=
    fun s hs => (hslabAll s hs).2.2.2.2.2.2.2.2.2.2.1
  have hu2 : ∀ s : ℝ, 0 < s → MemLp u 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun s hs => (hslabAll s hs).2.2.1
  have hDu2 : ∀ s : ℝ, 0 < s → MemLp Du 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) :=
    fun s hs => (hslabAll s hs).2.2.2.1
  have hUconv2 : ∀ s : ℝ, 0 < s → Tendsto (fun n => eLpNorm (U n - u) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s)))) atTop (𝓝 0) :=
    fun s hs => (hslabAll s hs).2.2.2.2.1
  have hweak : ∀ s : ℝ, 0 < s → ∀ i j, ∀ w : ParabolicPoint → ℝ,
      MemLp w 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) →
      Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s),
          Dseq n z i j * w z)
        atTop (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s), Du z i j * w z)) :=
    fun s hs => (hslabAll s hs).2.2.2.2.2.1
  have hweakSlice : ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, U n (x, t) i * w x i) atTop
        (𝓝 (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)) :=
    fun t ht => (hslabAll t ht).2.2.2.2.2.2.2.2.2.2.2.1 t ht
  have hf2 : ∀ s : ℝ, 0 < s → MemLp f 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 s))) := hf
  have hmom := fun n => hregMomentum a ha f hf (εseq (σ n)) (hεn n)
  -- continuity of the regularized pairings
  have hcontPair : ∀ n (w : Vec3 → Vec3) (hw : MemLp w 2 volume),
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, U n (x, t) i * w x i) (Ici 0) := by
    intro n w hw
    rw [continuousOn_iff_continuous_domRestrict]
    refine ((hSliceCont n).inner (continuous_const (y := realVectorL2OfCoordinateFunction w hw))).congr
      (fun t => ?_)
    exact lerayHopfLimit_inner_realVectorL2 _ _ _ hw
  -- the energy inequality of the regularized solutions in real form
  set Aa : ℝ := ∑ i : Fin 3, ∫ x, a x i ^ 2 with hAa
  have hAa0 : 0 ≤ Aa := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  let W : ℕ → ℝ → ℝ := fun n t =>
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), ∑ i : Fin 3, f z i * U n z i
  let Wlim : ℝ → ℝ := fun t =>
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), ∑ i : Fin 3, f z i * u z i
  have hEreal_n : ∀ n (t : ℝ), 0 < t →
      (∑ i : Fin 3, ∫ x, U n (x, t) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Dseq n z i j ^ 2) ≤
      Aa + 2 * W n t := fun n t ht =>
    forcedHopf_energy_real_of_regularised ρ (εseq (σ n)) (hεn n) a ha.1 (U n) f (Dseq n) t
      (hSliceMem n t ht.le) (hL2n n t ht) (hEn n t ht.le).2
  have hGn0 : ∀ n (t : ℝ), 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Dseq n z i j ^ 2 :=
    fun n t => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun z => sq_nonneg _)))
  have hWconv : ∀ t : ℝ, 0 < t → Tendsto (fun n => W n t) atTop (𝓝 (Wlim t)) :=
    fun t ht => forcedHopf_work_tendsto U u f
      (fun n => (hU3 t ht n).aestronglyMeasurable) (hu2 t ht) (hf2 t ht) (hUconv2 t ht)
  -- every positive-time slice of the limit is square integrable
  have hsliceU : ∀ t, 0 < t → MemLp (fun x => u (x, t)) 2 volume := by
    intro t ht
    have hev : ∀ᶠ n in atTop, (∑ i : Fin 3, ∫ x, U n (x, t) i ^ 2) ≤
        Aa + 2 * (Wlim t + 1) := by
      filter_upwards [(tendsto_order.mp (hWconv t ht)).2 (Wlim t + 1)
        (by linarith only)] with n hn
      linarith only [hEreal_n n t ht, hGn0 n t, hn]
    obtain ⟨B, hB0, hB⟩ := forcedHopf_exists_bound_of_eventually_le hev
    refine lerayHopfLimit_slice_memLp_of_representative
      (fun n y => uε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm y)) σ hσtop u t
      (fun x => by have h := hrep (x, t) ht; exact h)
      (fun n => hSliceMem n t ht.le) (Real.sqrt B) (Real.sqrt_nonneg _) (fun n => ?_)
      (hweakSlice t ht)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [forcedHopf_norm_toLp_sq]
    · exact hB n
    · exact hSliceMem n t ht.le
  -- the forced energy inequality of the limit at positive times
  have hEreal : ∀ t, 0 < t →
      (∑ i : Fin 3, ∫ x, u (x, t) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Du z i j ^ 2) ≤
      Aa + 2 * Wlim t := by
    intro t ht
    refine forcedHopf_energy_limit_real t U u Dseq Du (fun n => Aa + 2 * W n t)
      (Aa + 2 * Wlim t) (fun n => hSliceMem n t ht.le) (hsliceU t ht)
      (hweakSlice t ht _ (hsliceU t ht))
      (fun n i j => ((hL2n n t ht).eval i).eval j) (fun i j => ((hDu2 t ht).eval i).eval j)
      (fun i j => hweak t ht i j _ (((hDu2 t ht).eval i).eval j))
      (fun n => hEreal_n n t ht) ?_
    exact tendsto_const_nhds.add ((hWconv t ht).const_mul 2)
  have hG0 : ∀ t : ℝ, 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), Du z i j ^ 2 :=
    fun t => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun z => sq_nonneg _)))
  -- a uniform bound for the work on `[0,T]`
  let g : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, f z i * u z i
  have hgint : Integrable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    integrable_finsetSum _ (fun i _ => ((hf2 T hT).eval i).integrable_mul ((hu2 T hT).eval i))
  set Wm : ℝ := ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), |g z| with hWm
  have hWm0 : 0 ≤ Wm := integral_nonneg (fun z => abs_nonneg _)
  have hWbound : ∀ t ∈ Icc 0 T, Wlim t ≤ Wm := by
    intro t ht
    calc Wlim t ≤ |Wlim t| := le_abs_self _
      _ ≤ ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), |g z| :=
          abs_integral_le_integral_abs
      _ ≤ Wm := setIntegral_mono_set hgint.abs (ae_of_all _ fun z => abs_nonneg _)
          (Eventually.of_forall (Set.prod_mono subset_rfl (Ioo_subset_Ioo_right ht.2)))
  have hXbound : ∀ t ∈ Icc 0 T, ∑ i : Fin 3, ∫ x, u (x, t) i ^ 2 ≤ Aa + 2 * Wm := by
    intro t ht
    rcases ht.1.lt_or_eq with htpos | hzero
    · linarith only [hEreal t htpos, hG0 t, hWbound t ht]
    · subst hzero
      simp only [hu0']
      linarith only [hWm0]
  -- weak divergence freedom and norms of the slices on `[0,T]`
  have hdivPos : ∀ t, 0 < t → ∀ ψ : WeakTestFunction (Set.univ : Set Vec3),
      ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * ψ.partialDeriv i x = 0 := fun t ht =>
    lerayHopfLimit_divergence_of_weakSlice (fun n x => U n (x, t)) (fun x => u (x, t))
      (fun n => hSliceDiv n t ht.le) (hweakSlice t ht)
  have hdiv : ∀ t ∈ Icc 0 T, IsWeakDivFreeL2 (fun x => u (x, t)) := by
    intro t ht
    rcases ht.1.lt_or_eq with ht' | ht'
    · exact ⟨hsliceU t ht', hdivPos t ht'⟩
    · subst ht'
      have heq : (fun x => u (x, 0)) = a := funext hu0
      rw [heq]
      exact isInJ_weakDivFree ha
  have hnorm : ∀ t (ht : t ∈ Icc 0 T), ‖(lerayHopfLimit_toLp_memLp (hdiv t ht).1).toLp
      (fun x => (WithLp.toLp 2 (u (x, t)) : L2Vec3))‖ ≤ Real.sqrt (Aa + 2 * Wm) := by
    intro t ht
    rw [← Real.sqrt_sq (norm_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [forcedHopf_norm_toLp_sq]
    · exact hXbound t ht
    · exact (hdiv t ht).1
  -- (LH2)
  have hLH2 : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * w x i) (Icc 0 T) := by
    refine forcedHopf_weakContinuity T u _ (Real.sqrt_nonneg _) hdiv hnorm ?_
    intro wc hw hwc hdivw
    have hW : MemLp (fun x i => wc i x) 2 volume :=
      MemLp.of_eval (fun i => lerayHopfLimit_memLp_two_of_compact (hw i).continuous (hwc i))
    refine forcedHopf_limitPairing_continuousOn hT hw hwc hdivw U Jv Dseq Pseq u f Du hmom
      (fun n => hcontPair n _ hW) hU3 hJ3 hu3 hUconv3 hJconv (fun s hs n => hL2n n s hs)
      hDu2 hweak hf2 (fun t ht => ?_)
    rcases ht.1.lt_or_eq with ht' | ht'
    · exact hweakSlice t ht' (fun x i => wc i x) hW
    · subst ht'
      have hcongr : ∀ n, ∫ x, ∑ i : Fin 3, U n (x, 0) i * wc i x =
          ∫ x, ∑ i : Fin 3, regUniformMollifiedInitial ρ (εseq (σ n)) (hεn n) a x i *
            wc i x := by
        intro n
        refine integral_congr_ae ((hSlice0 n).mono (fun x hx => ?_))
        change ∑ i : Fin 3, U n (x, 0) i * wc i x = _
        rw [show U n (x, 0) = regUniformMollifiedInitial ρ (εseq (σ n)) (hεn n) a x from hx]
      have h := lerayHopfLimit_mollifiedInitial_pairing_tendsto ρ ha.1
        (fun n => εseq (σ n)) hεn hεsub (fun x i => wc i x) hW
      simp only [hcongr, hu0']
      exact h
  -- (FLH1)
  have hLH3 := forcedHopf_momentum (T := T) U Jv Dseq Pseq u f Du hmom hU3 hJ3 hu3 hUconv3
    hJconv (fun s hs n => hL2n n s hs) hDu2 hweak hf2
  -- the measurability, energy, gradient and divergence clauses
  obtain ⟨h1, h2, h3, h4, h5⟩ := lerayHopfLimit_LH1_core T u Du U
    (hslabAll T hT).1 (hslabAll T hT).2.1 (hu2 T hT) (hDu2 T hT)
    (ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
      (hslabAll T hT).2.2.2.2.2.2.2.2.2.2.2.2)
    hSliceDiv hweakSlice
  have hess : essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ := by
    refine lt_of_le_of_lt (essSup_le_of_ae_le (ENNReal.ofReal (Aa + 2 * Wm))
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_))) ENNReal.ofReal_lt_top
    calc ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (2 : ℝ) := by
          refine lintegral_mono (fun x => ENNReal.rpow_le_rpow ?_ (by norm_num))
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (norm_le_vec3EuclideanNorm _)
      _ = ENNReal.ofReal (∑ i : Fin 3, ∫ x, u (x, s) i ^ 2) :=
          lerayHopfLimit_lintegral_euclidean_sq (hsliceU s hs.1)
      _ ≤ ENNReal.ofReal (Aa + 2 * Wm) :=
          ENNReal.ofReal_le_ofReal (hXbound s ⟨hs.1.le, hs.2.le⟩)
  -- (FLH2)
  have hFLH2 : ∀ t₀ : ℝ, t₀ ∈ Icc 0 T →
      (ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z)) < ⊤ ∧
      ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z))).toReal ≤
        ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)))).toReal +
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ∑ i : Fin 3, f z i * u z i := by
    intro t₀ ht₀
    rcases ht₀.1.lt_or_eq with hpos | hzero
    · refine forcedHopf_energy_ennreal t₀ u f Du a (hsliceU t₀ hpos) (hDu2 t₀ hpos) ha.1 ?_
      have h := hEreal t₀ hpos
      exact h
    · subst hzero
      rw [Ioo_self, show spaceTimeSet (Set.univ : Set Vec3) (∅ : Set ℝ) = ∅ from
        Set.prod_empty, Measure.restrict_empty, lintegral_zero_measure, integral_zero_measure,
        add_zero, add_zero]
      simp only [hu0']
      refine ⟨?_, le_rfl⟩
      rw [lerayHopfLimit_lintegral_euclidean_sq ha.1]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  -- (LH5)
  have hWc : ContinuousOn Wlim (Icc 0 T) :=
    forcedHopf_continuousOn_setIntegral_slab Set.univ T g hgint
  have hW0 : Wlim 0 = 0 := by
    change ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 0), g z = 0
    rw [Ioo_self, show spaceTimeSet (Set.univ : Set Vec3) (∅ : Set ℝ) = ∅ from
      Set.prod_empty, Measure.restrict_empty, integral_zero_measure]
  have hWlim : Tendsto (fun t => 2 * Wlim t) (𝓝[>] 0) (𝓝 0) := by
    have hmem : Icc 0 T ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioc_mem_nhdsGT hT) Ioc_subset_Icc_self
    have h := ((hWc 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin hmem).tendsto
    rw [hW0] at h
    simpa only [mul_zero] using h.const_mul 2
  have hLH5 := forcedHopf_initialTrace T hT u a hu0' ha.1 hsliceU (fun t => 2 * Wlim t) hWlim
    (fun t ht _ => by linarith only [hEreal t ht, hG0 t]) (hLH2 a ha.1)
  exact ⟨hT, ha, hf2 T hT, h1, h2, hess, h3, h4, h5, hLH2, hLH3, hFLH2, hLH5⟩

end CKN.Leray

end
