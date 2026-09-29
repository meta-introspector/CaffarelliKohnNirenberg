-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.ForcedAssemblyEnergy
public import CKN.Leray.RegUniformEnergy
public import CKN.Leray.RegularisedInitialData
public import CKN.Leray.FourierCoordinateL2Bridge
public import CKN.Leray.CompactnessRepresentative
public import CKN.Leray.PressureLimitLeray
public import CKN.Leray.RieszPressurePackageForce
public import CKN.Statements.IsGlobalForcedLerayHopfSolution
public import CKN.Statements.IsLocallySquareIntegrableForce

/-!
# The forced Leray existence assembly

The direct limiting argument of `thm:leray-forced`, with the force pressure of
`lem:force-pressure`, the forced regularized solutions of
`lem:regularised-forced` with their momentum identity `eq:reg-momentum-forced`
and local energy inequality `eq:reg-local-energy-forced`, the compactness
limit of `prop:forced-limit`, the pressure limit and the forced
Leray--Hopf limit as explicit inputs. The conclusion is the statement of
`thm:leray-forced`: one velocity, weak gradient and pressure are suitable
for every exponent `q > 5/2` at which the force is locally `L^q`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The direct limiting argument for `thm:leray-forced`, with the force
pressure, the forced regularized identities and the convergence statements as
explicit inputs. -/
theorem lerayExistenceForced_of_limits
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
    (hforcePressure : ∀ (f : ParabolicPoint → Vec3)
      (hf : IsLocallySquareIntegrableForce f) (T : ℝ), 0 < T →
      AEStronglyMeasurable (pF f hf)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
      (∫⁻ t in Ioo 0 T,
        eLpNorm (fun x : Vec3 => pF f hf (x, t)) (ENNReal.ofReal (6 : ℝ))
          (volume : Measure Vec3) ^ (2 : ℝ) ∂(volume : Measure ℝ)) < ⊤ ∧
      (∀ᵐ t ∂(volume.restrict (Ioo 0 T)),
        ∃ hft : MemLp (fun x : Vec3 => f (x, t)) (2 : ℝ≥0∞) volume,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x : Vec3 => pF f hf (x, t))
            (fun x i => CKN.Leray.forcePressureGradientFunction
              (fun y : Vec3 => f (y, t)) hft x i)) ∧
      (∀ (K : Set Vec3) (I : Set ℝ), MeasurableSet K → MeasurableSet I →
        I ⊆ Ioo 0 T →
        eLpNorm (pF f hf) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (spaceTimeSet K I)) ≤
          volume K ^ (1 / 2 : ℝ) * volume I ^ (1 / 6 : ℝ) *
            (∫⁻ t in Ioo 0 T,
              eLpNorm (fun x : Vec3 => pF f hf (x, t))
                (ENNReal.ofReal (6 : ℝ)) (volume : Measure Vec3) ^ (2 : ℝ)
                ∂(volume : Measure ℝ)) ^ (1 / 2 : ℝ)))
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
    (hregLocalEnergy : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (ε : ℝ) (hε : 0 < ε) (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq (uε a ha f hf ε) (Duε a ha f hf ε) z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (uε a ha f hf ε z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (uε a ha f hf ε z)) ^ (2 : ℕ) *
                  CKN.Leray.regUniformMollifiedVelocity ρ ε hε
                    (uε a ha f hf ε) z i +
                2 * pε a ha f hf ε z * uε a ha f hf ε z i) *
                spatialPartial ψ i z +
            2 * (∑ i : Fin 3, f z i * uε a ha f hf ε z i) * ψ z)
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
                uε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm y)) σ z))
    (hpressureLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0))
      (σ : ℕ → ℕ) (u : ParabolicPoint → Vec3)
      (hσ : StrictMono σ) (hσtop : Tendsto σ atTop atTop)
      (hεsubseq : Tendsto (fun n => εseq (σ n)) atTop (nhds 0))
      (hUseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (uε a ha f hf (εseq (σ n)) - u) (ENNReal.ofReal (3 : ℝ))
          (volume.restrict
            (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
          atTop (nhds 0))
      (hJseqLthree : ∀ T : ℝ, 0 < T →
        Tendsto (fun n => eLpNorm
          (CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1)
            (uε a ha f hf (εseq (σ n))) - u) (ENNReal.ofReal (3 : ℝ))
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
          let pFST : Vec3 × ℝ → ℝ := fun z =>
            pF f hf (parabolicHomeomorph.symm z)
          let pseq : ℕ → Vec3 × ℝ → ℝ := fun n z =>
            pε a ha f hf (εseq (σ n)) (parabolicHomeomorph.symm z)
          ∃ hu : MemLp uST 3 μ,
            MemLp (pST - pFST) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
            pST - pFST =ᵐ[μ]
              CKN.Leray.lerayProductPressureOnSlab T uST uST hu hu ∧
            Tendsto (fun n => eLpNorm (pseq n - pST)
              (ENNReal.ofReal (3 / 2 : ℝ)) μ) atTop (nhds 0))
    (hhopfLimit : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (hεseq : Tendsto εseq atTop (nhds 0)),
      let hlim := hlerayLimit a ha f hf εseq hseq hεseq
      let _σ := Classical.choose hlim
      let hlim₁ := Classical.choose_spec hlim
      let u := Classical.choose hlim₁
      let hlim₂ := Classical.choose_spec hlim₁
      let Du := Classical.choose hlim₂
      ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du) :
    ∀ a : Vec3 → Vec3, IsInJ a →
    ∀ f : ParabolicPoint → Vec3,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      ∃ p : ParabolicPoint → ℝ,
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        ∀ q : ℝ, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          CKN.IsSuitableWeakSolution (Set.univ : Set Vec3) (Ioi 0) q u Du p f := by
  intro a ha f hf2 _
  let εseq : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1 := by
    intro n
    constructor
    · dsimp [εseq]
      positivity
    · dsimp [εseq]
      have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by
        exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
      simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden)
  have hεseq : Tendsto εseq atTop (nhds 0) := by
    simpa [εseq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let hlim := hlerayLimit a ha f hf2 εseq hseq hεseq
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
        (uε a ha f hf2 (εseq (Classical.choose hlim n)) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, hLq, _, _, _, _, _, _⟩
    have h := hLq 3 (by norm_num) (by norm_num)
    change Tendsto (fun n => eLpNorm
      (uε a ha f hf2 (εseq (Classical.choose hlim n)) -
        Classical.choose (Classical.choose_spec hlim))
      (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))
      ) atTop (nhds 0) at h
    exact h
  have hJseqLthree : ∀ T : ℝ, 0 < T →
      Tendsto (fun n => eLpNorm
        (CKN.Leray.regUniformMollifiedVelocity ρ
          (εseq (Classical.choose hlim n))
          (by exact (hseq (Classical.choose hlim n)).1)
          (uε a ha f hf2 (εseq (Classical.choose hlim n))) -
          Classical.choose (Classical.choose_spec hlim))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) atTop (nhds 0) := by
    intro T hT
    rcases hlimitOn T hT with
      ⟨_, _, _, _, _, _, _, _, _, _, hJconv, _, _⟩
    simpa only [ENNReal.ofReal_ofNat] using hJconv
  obtain ⟨p, hpLimit⟩ := hpressureLimit a ha f hf2 εseq hseq hεseq
    (Classical.choose hlim) (Classical.choose (Classical.choose_spec hlim))
    hσ hσtop hεsubseq hUseqLthree hJseqLthree
  have hglobal : ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du :=
    fun T hT => hhopfLimit a ha f hf2 εseq hseq hεseq T hT
  let U : ℕ → ParabolicPoint → Vec3 :=
    fun n => uε a ha f hf2 (εseq (σ n))
  let Jv : ℕ → ParabolicPoint → Vec3 := fun n =>
    CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
      (hseq (σ n)).1 (U n)
  let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 :=
    fun n => Duε a ha f hf2 (εseq (σ n))
  let Pseq : ℕ → ParabolicPoint → ℝ :=
    fun n => pε a ha f hf2 (εseq (σ n))
  let P : ParabolicPoint → ℝ := pF f hf2
  have hR2 (n : ℕ) (T : ℝ) (hT : 0 < T) :
      MemLp (Dseq n) 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        MemLp (fun z => Pseq n z - P z) 2 (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
    rcases hregularised a ha f hf2 (εseq (σ n)) (hseq (σ n)).1 with
      ⟨_, _, hR, _, _⟩
    exact hR T hT
  have hboxLE {Ω' : Set Vec3} {J : Set ℝ} {T : ℝ} (hJT : J ⊆ Ioo 0 T) :
      (volume : Measure ParabolicPoint).restrict (spaceTimeSet Ω' J) ≤
        (volume : Measure ParabolicPoint).restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    Measure.restrict_mono_set (volume : Measure ParabolicPoint)
      (Set.prod_mono (Set.subset_univ (Ω' : Set Vec3)) hJT)
  have hPFLocal (Ω' : Set Vec3) (J : Set ℝ)
      (hbox : CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J)
      (T : ℝ) (hT : 0 < T) (hJT : J ⊆ Ioo 0 T) :
      MemLp P (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
    obtain ⟨-, hfin, -, hbound⟩ := hforcePressure f hf2 T hT
    have hΩmeas : MeasurableSet Ω' := hbox.1.measurableSet
    have hJmeas : MeasurableSet J := hbox.2.2.2.1.measurableSet
    have hΩfin : volume Ω' ≠ ⊤ :=
      ((measure_mono subset_closure).trans_lt
        hbox.2.1.measure_lt_top).ne
    have hJfin : volume J ≠ ⊤ :=
      ((measure_mono subset_closure).trans_lt
        hbox.2.2.2.2.1.measure_lt_top).ne
    refine lt_of_le_of_lt (hbound Ω' J hΩmeas hJmeas hJT) ?_
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hΩfin)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJfin))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne)
  have hDiffLocal (Ω' : Set Vec3) (J : Set ℝ)
      (T : ℝ) (hT : 0 < T) (hJT : J ⊆ Ioo 0 T) :
      MemLp (fun z => p z - P z) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
    rcases hpLimit T hT with ⟨_, hpdiff, _, _⟩
    have hslab : MemLp (fun z => p z - P z) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
      lerayAssembly_productSlab_memLp_to_parabolic
        (f := fun z => p z - P z) hpdiff
    exact hslab.mono_measure (hboxLE hJT)
  have hpLocalBox : ∀ Ω' J,
      CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) := by
    intro Ω' J hbox
    obtain ⟨δ, T, hδ, hδT, hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
    have hT : 0 < T := lt_trans hδ hδT
    have hJT : J ⊆ Ioo 0 T := fun t ht =>
      ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
    have h := (hDiffLocal Ω' J T hT hJT).add (hPFLocal Ω' J hbox T hT hJT)
    have heq : (fun z => p z - P z) + P = p := by
      funext z
      simp
    rwa [heq] at h
  have hlocal : ∀ Ω' J,
      CKN.localBox (Set.univ : Set Vec3) (Ioi 0) Ω' J →
      ∀ T : ℝ, 0 < T → J ⊆ Ioo 0 T →
      (∀ n, MemLp (U n) 3 (volume.restrict (spaceTimeSet Ω' J))) ∧
      (∀ n, MemLp (Jv n) 3 (volume.restrict (spaceTimeSet Ω' J))) ∧
      MemLp u 3 (volume.restrict (spaceTimeSet Ω' J)) ∧
      Tendsto (fun n => eLpNorm (U n - u) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm (U n - u) 2
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) ∧
      Tendsto (fun n => eLpNorm (Jv n - u) 3
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) ∧
      (∀ n, MemLp (Dseq n) 2 (volume.restrict (spaceTimeSet Ω' J))) ∧
      MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) ∧
      (∀ i j : Fin 3, ∀ w : ParabolicPoint → ℝ,
        MemLp w 2 (volume.restrict (spaceTimeSet Ω' J)) →
        Tendsto (fun n => ∫ z in spaceTimeSet Ω' J,
          Dseq n z i j * w z) atTop
          (nhds (∫ z in spaceTimeSet Ω' J, Du z i j * w z))) ∧
      (∀ n, MemLp (Pseq n) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J))) ∧
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J)) ∧
      Tendsto (fun n => eLpNorm (Pseq n - p) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (spaceTimeSet Ω' J))) atTop (nhds 0) ∧
      MemLp f 2 (volume.restrict (spaceTimeSet Ω' J)) := by
    intro Ω' J hbox T hT hJT
    let : IsFiniteMeasure (volume.restrict (spaceTimeSet Ω' J)) :=
      stability_localBox_finiteMeasure hbox
    rcases hlimitOn T hT with
      ⟨_, _, _, hDu2, hL2conv, hweak, _, hUL3, hJL3, huL3, _, _, _⟩
    have hDiffSeq (n : ℕ) : MemLp (fun z => Pseq n z - P z) 2
        (volume.restrict (spaceTimeSet Ω' J)) :=
      (hR2 n T hT).2.mono_measure (hboxLE hJT)
    refine ⟨fun n => (hUL3 n).mono_measure (hboxLE hJT),
      fun n => (hJL3 n).mono_measure (hboxLE hJT),
      huL3.mono_measure (hboxLE hJT), ?_, ?_, ?_,
      fun n => (hR2 n T hT).1.mono_measure (hboxLE hJT),
      hDu2.mono_measure (hboxLE hJT), ?_, ?_, hpLocalBox Ω' J hbox, ?_,
      (hf2 T hT).mono_measure (hboxLE hJT)⟩
    · simpa only [ENNReal.ofReal_ofNat] using
        lerayAssembly_strongConv_localBox hJT U u (hUseqLthree T hT)
    · exact lerayAssembly_strongConv_localBox hJT U u hL2conv
    · simpa only [ENNReal.ofReal_ofNat] using
        lerayAssembly_strongConv_localBox hJT Jv u (hJseqLthree T hT)
    · intro i j w hw
      exact lerayAssembly_weakConv_localBox_all hbox hJT
        (fun n z => Dseq n z i j) (fun z => Du z i j) (hweak i j) w hw
    · intro n
      have h := ((hDiffSeq n).mono_exponent
        (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≤ 2)).add
        (hPFLocal Ω' J hbox T hT hJT)
      have heq : (fun z => Pseq n z - P z) + P = Pseq n := by
        funext z
        simp
      rwa [heq] at h
    · rcases hpLimit T hT with ⟨_, hpdiff, _, hconv⟩
      have hconv' : Tendsto (fun n => eLpNorm
          (fun z : Vec3 × ℝ =>
            (Pseq n (parabolicHomeomorph.symm z) -
                P (parabolicHomeomorph.symm z)) -
              (p (parabolicHomeomorph.symm z) -
                P (parabolicHomeomorph.symm z)))
          (ENNReal.ofReal (3 / 2 : ℝ))
          ((volume : Measure (Vec3 × ℝ)).restrict
            (lerayPressureLimitSlab T))) atTop (nhds 0) := by
        refine hconv.congr (fun n => ?_)
        congr 1
        funext z
        simp only [Pi.sub_apply]
        ring
      have h := lerayAssembly_pressureConv_localBox hbox hJT
        (fun n z => Pseq n z - P z) (fun z => p z - P z) hDiffSeq hpdiff
        hconv'
      refine h.congr (fun n => ?_)
      congr 1
      funext z
      simp only [Pi.sub_apply]
      ring
  have hmomentum : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (Set.univ : Set Vec3) (Ioi 0) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (-(∑ i, u z i * timePartial (fun w => φ w i) z))
          - ∑ i, ∑ j, u z i * u z j *
              spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, Du z i j *
              spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, f z i * φ z i = 0 := by
    intro φ hφ
    let K : Set ParabolicPoint := tsupport (show ParabolicPoint → Vec3 from φ)
    have hK : IsCompact K := isCompact_tsupport_parabolic hφ.2.1
    have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      tsupport_parabolic_subset_spaceTimeSet hφ
    obtain ⟨Ω', J, hbox, hKbox⟩ :=
      caccioppoli_localBox_of_compact_subset
        isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
    obtain ⟨δ, T, hδ, hδT, hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
    have hT : 0 < T := lt_trans hδ hδT
    have hJT : J ⊆ Ioo 0 T := fun t ht =>
      ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
    obtain ⟨hUL, hJL, huL, hUc, -, hJc, hDL, hDuL, hW, hPL, hpL, hPc, hfL⟩ :=
      hlocal Ω' J hbox T hT hJT
    exact forcedAssembly_momentum_limit hbox U Jv Dseq Pseq u Du p f φ hφ
      hKbox hUL hJL huL hUc hJc hDL hDuL hW hPL hpL hPc hfL
      (fun n => hregMomentum a ha f hf2 (εseq (σ n)) (hseq (σ n)).1 φ hφ)
  have henergy : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (Set.univ : Set Vec3) (Ioi 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          vec3EuclideanNorm (u z) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
            + (vec3EuclideanNorm (u z) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z
            + 2 * (∑ i, f z i * u z i) * ψ z := by
    intro ψ hψ hψpos
    let K : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
    have hK : IsCompact K := isCompact_tsupport_parabolic hψ.2.1
    have hKsub : K ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) :=
      tsupport_parabolic_subset_spaceTimeSet hψ
    obtain ⟨Ω', J, hbox, hKbox⟩ :=
      caccioppoli_localBox_of_compact_subset
        isOpen_univ isOpen_Ioi ordConnected_Ioi hK hKsub
    obtain ⟨δ, T, hδ, hδT, hJδ⟩ := lerayAssembly_localBox_time_bounds hbox
    have hT : 0 < T := lt_trans hδ hδT
    have hJT : J ⊆ Ioo 0 T := fun t ht =>
      ⟨lt_trans hδ (hJδ ht).1, (hJδ ht).2⟩
    obtain ⟨hUL, hJL, huL, hUc, hUc2, hJc, hDL, hDuL, hW, hPL, hpL, hPc,
      hfL⟩ := hlocal Ω' J hbox T hT hJT
    exact forcedAssembly_localEnergy_limit hbox U Jv Dseq Pseq u Du p f ψ hψ
      hKbox hψpos hUL hJL huL hUc hUc2 hJc hDL hDuL hW hPL hpL hPc hfL
      (fun n => hregLocalEnergy a ha f hf2 (εseq (σ n)) (hseq (σ n)).1 ψ hψ
        hψpos)
  refine ⟨u, Du, p, hglobal, ?_⟩
  intro q hq hfq
  unfold CKN.IsSuitableWeakSolution
  rcases forcedAssembly_hopfData hglobal hpLocalBox hq hfq with
    ⟨hopenSpace, hopenTime, hord, hq', hforce, hdataLocal⟩
  exact ⟨hopenSpace, hopenTime, hord, hq', hforce, hdataLocal,
    fun ψ hψ => forcedAssembly_hopfDivergence hglobal ψ hψ,
    hmomentum, henergy⟩

end CKN.Leray

end
