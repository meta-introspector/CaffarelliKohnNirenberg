-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Topology.MetricSpace.Snowflaking
public import CKN.Statements.LerayExistence
public import CKN.Statements.LerayExistenceSingularSet
public import CKN.Statements.LerayExistenceForced
public import CKN.Statements.LerayExistenceForcedSingularSet
public import CKN.Statements.AssociatedPressure

@[expose] public section

open CKN

/-!
# Leray's existence theorem, the pressure of a Leray--Hopf solution

A standalone, Mathlib-only statement of the existence theorems `thm:leray`,
`cor:ckn-headline`, `thm:leray-forced`, `thm:leray-forced-singularSet` and of
`thm:assoc-pressure`. Space-time has Euclidean coordinates `ℝ³ × ℝ`; the
parabolic metric enters only where it is mathematically relevant (the
Hausdorff measure of the singular set).
-/

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Gradient InnerProductSpace NNReal Topology

set_option autoImplicit false

noncomputable section

namespace CKNLerayChallenge

/-! ## Local weak Navier–Stokes solutions -/

/-- Three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Test functions and spatial differential operators -/

/-- Smooth compactly supported `Y`-valued functions supported in `Ω`. -/
def testFunctions
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Ω : Set X) : Set (X → Y) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}

local notation "Dₓ" g:arg z:arg =>
  fderiv ℝ (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "∂ₜ" g:arg z:arg =>
  fderiv ℝ (fun t : ℝ ↦ g (Prod.fst z, t)) (Prod.snd z) 1
local notation "∇ₓ" g:arg z:arg =>
  gradient (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "divₓ" g:arg z:arg =>
  LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap (Dₓ g z))
local notation "Δₓ" g:arg z:arg =>
  Laplacian.laplacian (fun x : ℝ³ ↦ g (x, Prod.snd z)) (Prod.fst z)
local notation "⟪" A ", " B "⟫ₕₛ" =>
  LinearMap.trace ℝ ℝ³
    (ContinuousLinearMap.toLinearMap (ContinuousLinearMap.adjoint A ∘L B))
local infixr:100 " ⊗ᵣ " => InnerProductSpace.rankOne ℝ

/-- `Du` is the weak derivative of `u` on `U` for the ambient measure. The
definition is coordinate-free for real Hilbert spaces equipped with a measure.
For the Euclidean spaces and volume used below, almost-everywhere
uniqueness on open sets follows from Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
structure HasWeakDerivativeOn
    {X Y : Type*}
    [MeasureSpace X]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (u : X → Y) (Du : X → (X →L[ℝ] Y)) : Prop where
  functionLocallyIntegrable : LocallyIntegrableOn u U volume
  derivativeLocallyIntegrable : LocallyIntegrableOn Du U volume
  integral_eq : ∀ φ ∈ testFunctions ℝ U, ∀ v (y' : Y →L[ℝ] ℝ),
    ∫ x in U, φ x * y' (Du x v) ∂volume =
      -∫ x in U, ⟪∇ φ x, v⟫_ℝ * y' (u x) ∂volume

/-! ### The solution class -/

/-- The fields of the Navier–Stokes system together with a chosen global weak
spatial gradient of the velocity. -/
structure NSEData (Ω : Set ℝ³) (I : Set ℝ) where
  isOpenSpace : IsOpen Ω
  isOpenTime : IsOpen I
  ordConnectedTime : OrdConnected I
  u : ℝ³ × ℝ → ℝ³
  Dxu : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)
  p : ℝ³ × ℝ → ℝ
  f : ℝ³ × ℝ → ℝ³
  weakDerivative :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakDerivativeOn Ω (fun x ↦ u (x, t)) (fun x ↦ Dxu (x, t))

/-- `U ⋐ Ω` means that the closure of `U` is compact and contained in `Ω`. -/
def IsCompactlyContained
    {X : Type*} [TopologicalSpace X] (U Ω : Set X) : Prop :=
  IsCompact (closure U) ∧ closure U ⊆ Ω

local infix:50 " ⋐ " => IsCompactlyContained

/-- The energy-class bounds on a fixed space-time product set `U × J`. -/
structure HasEnergyRegularityOn
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) (q : ℝ≥0)
    (U : Set ℝ³) (J : Set ℝ) : Prop where
  velocityTimeBound :
    essSup (fun t ↦ eLpNorm (fun x ↦ data.u (x, t)) 2
      (volume.restrict U)) (volume.restrict J) < ∞
  velocityMemLp : MemLp data.u 2 (volume.restrict (U ×ˢ J))
  gradientMemLp : MemLp data.Dxu 2 (volume.restrict (U ×ˢ J))
  pressureMemLp : MemLp data.p (3 / 2) (volume.restrict (U ×ˢ J))
  forceMemLp : MemLp data.f q (volume.restrict (U ×ˢ J))

/-- The incompressibility and momentum equations in distributional form. -/
structure SolvesDistributionalNSE
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop where
  incompressible : ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I, ⟪data.u z, ∇ₓ ψ z⟫_ℝ = 0
  momentum : ∀ φ ∈ testFunctions ℝ³ (Ω ×ˢ I),
    ∫ z in Ω ×ˢ I,
      ⟪data.u z, ∂ₜ φ z⟫_ℝ
        + ⟪data.u z ⊗ᵣ data.u z, Dₓ φ z⟫ₕₛ
        - ⟪data.Dxu z, Dₓ φ z⟫ₕₛ
        + data.p z * divₓ φ z
        + ⟪data.f z, φ z⟫_ℝ = 0

/-- The local energy inequality for nonnegative test functions. -/
def SatisfiesLocalEnergyInequality
    {Ω : Set ℝ³} {I : Set ℝ} (data : NSEData Ω I) : Prop :=
  ∀ ψ ∈ testFunctions ℝ (Ω ×ˢ I), (∀ z, 0 ≤ ψ z) →
    2 * ∫ z in Ω ×ˢ I, ⟪data.Dxu z, data.Dxu z⟫ₕₛ * ψ z ≤
      ∫ z in Ω ×ˢ I,
        ‖data.u z‖ ^ 2 * (∂ₜ ψ z + Δₓ ψ z)
          + (‖data.u z‖ ^ 2 + 2 * data.p z) * ⟪data.u z, ∇ₓ ψ z⟫_ℝ
          + 2 * ⟪data.f z, data.u z⟫_ℝ * ψ z

/-- A local suitable weak solution: finite-energy data satisfying the
distributional Navier–Stokes equations and the local energy inequality. -/
structure LocalWeakNSESolution
    (Ω : Set ℝ³) (I : Set ℝ) (q : ℝ≥0)
    extends NSEData Ω I where
  energyRegularity : ∀ (U : Set ℝ³) (J : Set ℝ),
    IsOpen U ∧ U ⋐ Ω ∧ OrdConnected J ∧ J ⋐ I →
      HasEnergyRegularityOn toNSEData q U J
  equations : SolvesDistributionalNSE toNSEData
  energyInequality : SatisfiesLocalEnergyInequality toNSEData

/-! ## Parabolic geometry and regularity -/

/-- `ℝ` equipped with the metric `dist s t = |s - t|^(1/2)`, used to define
the parabolic Hausdorff dimension. -/
abbrev Rpar :=
  Metric.Snowflaking ℝ (1 / 2 : ℝ) (by norm_num) (by norm_num)

instance : MeasurableSpace Rpar := borel Rpar
instance : BorelSpace Rpar := ⟨rfl⟩

/-- Hausdorff measure for the parabolic metric, written in ordinary
space-time coordinates. -/
def parabolicHausdorffMeasure (d : ℝ) : Measure (ℝ³ × ℝ) :=
  Measure.map
    ((Homeomorph.refl ℝ³).prodCongr
      (Metric.Snowflaking.homeomorph : Rpar ≃ₜ ℝ)).toMeasurableEquiv
    (Measure.hausdorffMeasure d : Measure (ℝ³ × Rpar))

/-- The Hölder norm of an almost-everywhere equivalence class: the infimum,
over all representatives, of the supremum norm plus Hölder seminorm. -/
def aeHolderNormOn
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (U : Set X) (g : X → Y) (γ : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (w : X → Y) (_ : w =ᵐ[volume.restrict U] g),
    (⨆ x : U, ‖w x‖ₑ) + eHolderNorm γ (U.domRestrict w)

/-- Local Hölder regularity at a point, for arbitrary metric-measure spaces. -/
def IsHolderRegularPoint
    {X Y : Type*} [PseudoEMetricSpace X] [MeasureSpace X]
    [SeminormedAddCommGroup Y]
    (u : X → Y) (x₀ : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
    ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ aeHolderNormOn U u γ < ∞

/-- The points of `Ω` where `u` has no local Hölder representative. Ordinary
space-time Hölder regularity is used here; on bounded cylinders it is
equivalent to parabolic Hölder regularity after halving the exponent. -/
def singularSet
    (Ω : Set ℝ³) (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) : Set (ℝ³ × ℝ) :=
  {z ∈ Ω ×ˢ I | ¬IsHolderRegularPoint u z}

/-! ## Leray--Hopf solutions -/

/-- The energy space `J` of `def:leray-hopf`: the `L²` limits of smooth,
compactly supported, divergence-free fields. -/
def IsInJ (a : ℝ³ → ℝ³) : Prop :=
  MemLp a 2 volume ∧
    ∃ aSeq : ℕ → ℝ³ → ℝ³,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (aSeq k)) ∧
      (∀ k, HasCompactSupport (aSeq k)) ∧
      (∀ k x, LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap (fderiv ℝ (aSeq k) x)) = 0) ∧
      Tendsto (fun k => eLpNorm (fun x => aSeq k x - a x) 2 volume)
        atTop (nhds 0)

/-- A finite-time Leray--Hopf solution of `def:leray-hopf`, with `Du` its weak
spatial gradient: energy class on `ℝ³ × (0,T)`, incompressibility, the
momentum equation against divergence-free test fields, weak continuity in time
on `[0,T]`, the energy inequality with the datum `a`, and strong attainment of
the initial datum. -/
def IsLerayHopfSolution (T : ℝ) (a : ℝ³ → ℝ³)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) : Prop :=
  0 < T ∧
    IsInJ a ∧
    essSup (fun s : ℝ => ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ∞ ∧
    MemLp u 2 (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
    MemLp Du 2 (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      HasWeakDerivativeOn (univ : Set ℝ³)
        (fun x => u (x, s)) (fun x => Du (x, s))) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ ∈ testFunctions ℝ (univ : Set ℝ³),
        ∫ x : ℝ³, ⟪u (x, s), ∇ ψ x⟫_ℝ = 0) ∧
    (∀ w : ℝ³ → ℝ³, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ) (Icc 0 T)) ∧
    (∀ φ ∈ testFunctions ℝ³ (univ ×ˢ Ioo 0 T),
      (∀ z : ℝ³ × ℝ, divₓ φ z = 0) →
      ∫ z in univ ×ˢ Ioo 0 T,
        ⟪u z, ∂ₜ φ z⟫_ℝ
          + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ
          - ⟪Du z, Dₓ φ z⟫ₕₛ = 0) ∧
    (∀ t₀ ∈ Icc 0 T,
      ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ ≤
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ)) ∧
    Tendsto (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0)

/-- A global Leray--Hopf solution: a Leray--Hopf solution on every finite
interval `(0,T)`, as in `rem:global-LH`. -/
def IsGlobalLerayHopfSolution (a : ℝ³ → ℝ³)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) : Prop :=
  ∀ T : ℝ, 0 < T → IsLerayHopfSolution T a u Du

/-- A finite-time forced Leray--Hopf solution of `def:forced-leray-hopf`: the
conditions of `IsLerayHopfSolution` with the force `f ∈ L²(ℝ³ × (0,T))` added to
the momentum equation, and the energy inequality replaced by its finiteness
and the work inequality. -/
def IsForcedLerayHopfSolution (T : ℝ) (a : ℝ³ → ℝ³) (f : ℝ³ × ℝ → ℝ³)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) : Prop :=
  0 < T ∧
    IsInJ a ∧
    MemLp f 2 (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
    essSup (fun s : ℝ => ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ∞ ∧
    MemLp u 2 (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
    MemLp Du 2 (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      HasWeakDerivativeOn (univ : Set ℝ³)
        (fun x => u (x, s)) (fun x => Du (x, s))) ∧
    (∀ᵐ s ∂(volume.restrict (Ioo 0 T)),
      ∀ ψ ∈ testFunctions ℝ (univ : Set ℝ³),
        ∫ x : ℝ³, ⟪u (x, s), ∇ ψ x⟫_ℝ = 0) ∧
    (∀ w : ℝ³ → ℝ³, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ) (Icc 0 T)) ∧
    (∀ φ ∈ testFunctions ℝ³ (univ ×ˢ Ioo 0 T),
      (∀ z : ℝ³ × ℝ, divₓ φ z = 0) →
      ∫ z in univ ×ˢ Ioo 0 T,
        ⟪u z, ∂ₜ φ z⟫_ℝ
          + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ
          - ⟪Du z, Dₓ φ z⟫ₕₛ
          + ⟪f z, φ z⟫_ℝ = 0) ∧
    (∀ t₀ ∈ Icc 0 T,
      (ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ) < ∞ ∧
      (ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ).toReal ≤
        (ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ)).toReal
          + ∫ z in univ ×ˢ Ioo 0 t₀, ⟪f z, u z⟫_ℝ) ∧
    Tendsto (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 0)

/-- A global forced Leray--Hopf solution: a forced Leray--Hopf solution on every
finite interval `(0,T)`. -/
def IsGlobalForcedLerayHopfSolution (a : ℝ³ → ℝ³) (f : ℝ³ × ℝ → ℝ³)
    (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) : Prop :=
  ∀ T : ℝ, 0 < T → IsForcedLerayHopfSolution T a f u Du

/-- Square integrability of the force on every finite positive-time slab
`ℝ³ × (0,T)`. -/
def IsLocallySquareIntegrableForce (f : ℝ³ × ℝ → ℝ³) : Prop :=
  ∀ T : ℝ, 0 < T → MemLp f 2 (volume.restrict (univ ×ˢ Ioo 0 T))

/-- Local `L^q` integrability of the force on the compactly contained
space-time boxes of `def:sws` in `ℝ³ × (0,∞)`. -/
def IsLocallyQIntegrableForce (q : ℝ≥0) (f : ℝ³ × ℝ → ℝ³) : Prop :=
  ∀ (U : Set ℝ³) (J : Set ℝ),
    IsOpen U ∧ U ⋐ (univ : Set ℝ³) ∧ OrdConnected J ∧ J ⋐ Ioi (0 : ℝ) →
      MemLp f q (volume.restrict (U ×ˢ J))

abbrev RawSpace := CKN.Foundation.Parabolic.Vec3
abbrev RawPoint := CKN.Foundation.Parabolic.ParabolicPoint

theorem volume_rawPoint_eq_product :
    (volume : Measure RawPoint) =
      (volume : Measure (RawSpace × ℝ)) := by
  rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod,
    MeasureTheory.Measure.volume_eq_prod]

theorem ofReal_three_halves :
    ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

def rawToEuclidean : RawSpace ≃L[ℝ] ℝ³ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm


def rawSpaceTimeLinear : (RawSpace × ℝ) ≃L[ℝ] (ℝ³ × ℝ) :=
  rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

@[simp] theorem rawSpaceTimeLinear_apply (z : RawSpace × ℝ) :
    rawSpaceTimeLinear z = (rawToEuclidean z.1, z.2) := by
  rfl

@[simp] theorem rawToEuclidean_prodCongr_refl_apply (z : RawSpace × ℝ) :
    (rawToEuclidean.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)) z =
      (rawToEuclidean z.1, z.2) := by
  rfl

def rawSpaceTimeToEuclidean : (RawSpace × ℝ) ≃ₜ (ℝ³ × ℝ) :=
  rawSpaceTimeLinear.toHomeomorph

/-- The identity on space-time coordinates, first forgetting the old
parabolic topology and then using Euclidean spatial coordinates. -/
def parabolicToEuclideanHomeomorph : RawPoint ≃ₜ (ℝ³ × ℝ) :=
  CKN.Foundation.Parabolic.parabolicHomeomorph.trans
    rawSpaceTimeToEuclidean

@[simp] theorem parabolicToEuclideanHomeomorph_apply (z : RawPoint) :
    parabolicToEuclideanHomeomorph z = (rawToEuclidean z.1, z.2) := by
  rfl

/-- The old parabolic metric is exactly the product of Euclidean space with
snowflaked time used by the comparator. -/
def rawParabolicIsometry : RawPoint ≃ᵢ (ℝ³ × Rpar) where
  toEquiv := CKN.Foundation.Parabolic.parabolicMeasurableEquiv.toEquiv
  isometry_toFun := fun _ _ ↦ rfl

@[simp] theorem rawParabolicIsometry_apply (z : RawPoint) :
    rawParabolicIsometry z =
      (rawToEuclidean z.1, Metric.Snowflaking.toSnowflaking z.2) := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_fst (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).1 = rawToEuclidean z.1 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_snd (z : RawSpace × ℝ) :
    (rawSpaceTimeToEuclidean z).2 = z.2 := by
  rfl

@[simp] theorem rawSpaceTimeToEuclidean_apply (z : RawSpace × ℝ) :
    rawSpaceTimeToEuclidean z = (rawToEuclidean z.1, z.2) := by
  rfl

theorem rawSpaceTimeToEuclidean_measurePreserving :
    MeasurePreserving rawSpaceTimeToEuclidean := by
  change MeasurePreserving (Prod.map (WithLp.toLp 2) id)
    (volume.prod volume) (volume.prod volume)
  exact (PiLp.volume_preserving_toLp (Fin 3)).prod (MeasurePreserving.id volume)

theorem parabolicToEuclidean_measurePreserving :
    MeasurePreserving parabolicToEuclideanHomeomorph
      (volume : Measure RawPoint) (volume : Measure (ℝ³ × ℝ)) := by
  refine ⟨parabolicToEuclideanHomeomorph.continuous.measurable, ?_⟩
  rw [volume_rawPoint_eq_product]
  exact rawSpaceTimeToEuclidean_measurePreserving.map_eq

theorem rawToEuclidean_measurePreserving : MeasurePreserving rawToEuclidean := by
  change MeasurePreserving (WithLp.toLp 2) volume volume
  exact PiLp.volume_preserving_toLp (Fin 3)

@[simp] theorem vec3EuclideanNorm_rawToEuclidean_symm (v : ℝ³) :
    CKN.Foundation.Parabolic.vec3EuclideanNorm (rawToEuclidean.symm v) = ‖v‖ := by
  rw [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  rfl

def euclideanSpace (U : Set RawSpace) : Set ℝ³ := rawToEuclidean '' U

def rawSpace (Ω : Set ℝ³) : Set RawSpace := rawToEuclidean ⁻¹' Ω

@[simp] theorem euclideanSpace_rawSpace (Ω : Set ℝ³) :
    euclideanSpace (rawSpace Ω) = Ω := by
  exact Equiv.image_preimage rawToEuclidean.toEquiv Ω

@[simp] theorem rawToEuclidean_preimage_euclideanSpace (U : Set RawSpace) :
    rawToEuclidean ⁻¹' euclideanSpace U = U := by
  exact Equiv.preimage_image rawToEuclidean.toEquiv U

@[simp] theorem rawSpaceTime_preimage_product (U : Set RawSpace) (J : Set ℝ) :
    rawSpaceTimeToEuclidean ⁻¹' (euclideanSpace U ×ˢ J) = U ×ˢ J := by
  ext z
  simp [rawSpaceTimeToEuclidean, rawSpaceTimeLinear, euclideanSpace]

theorem rawToEuclidean_restrict_measurePreserving (U : Set RawSpace) :
    MeasurePreserving rawToEuclidean
      (volume.restrict U) (volume.restrict (euclideanSpace U)) := by
  simpa using rawToEuclidean_measurePreserving.restrict_preimage_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding (euclideanSpace U)

theorem rawSpaceTime_restrict_measurePreserving (U : Set RawSpace) (J : Set ℝ) :
    MeasurePreserving rawSpaceTimeToEuclidean
      (volume.restrict (U ×ˢ J))
      (volume.restrict (euclideanSpace U ×ˢ J)) := by
  simpa using rawSpaceTimeToEuclidean_measurePreserving.restrict_preimage_emb
    rawSpaceTimeToEuclidean.measurableEmbedding (euclideanSpace U ×ˢ J)


def pullVelocity (u : ℝ³ × ℝ → ℝ³) : RawSpace × ℝ → RawSpace :=
  fun z ↦ rawToEuclidean.symm (u (rawSpaceTimeToEuclidean z))

def pullScalar (g : ℝ³ × ℝ → ℝ) : RawSpace × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean z)

def pushScalar (g : RawSpace × ℝ → ℝ) : ℝ³ × ℝ → ℝ :=
  fun z ↦ g (rawSpaceTimeToEuclidean.symm z)

def pushVector (g : RawSpace × ℝ → RawSpace) : ℝ³ × ℝ → ℝ³ :=
  fun z ↦ rawToEuclidean (g (rawSpaceTimeToEuclidean.symm z))

@[simp] theorem pushScalar_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawSpaceTimeToEuclidean z) = g z := by
  change g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z)) = g z
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushVector_rawSpaceTimeToEuclidean
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawSpaceTimeToEuclidean z) = rawToEuclidean (g z) := by
  change rawToEuclidean
    (g (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z))) = _
  rw [rawSpaceTimeToEuclidean.symm_apply_apply]

@[simp] theorem pushScalar_rawCoordinates
    (g : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    pushScalar g (rawToEuclidean z.1, z.2) = g z := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushScalar_rawSpaceTimeToEuclidean g z

@[simp] theorem pushVector_rawCoordinates
    (g : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    pushVector g (rawToEuclidean z.1, z.2) = rawToEuclidean (g z) := by
  rw [← rawSpaceTimeToEuclidean_apply z]
  exact pushVector_rawSpaceTimeToEuclidean g z

@[simp] theorem rawToEuclidean_pullVelocity
    (u : ℝ³ × ℝ → ℝ³) (z : RawSpace × ℝ) :
    rawToEuclidean (pullVelocity u z) = u (rawToEuclidean z.1, z.2) := by
  simp [pullVelocity]

theorem pushScalar_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {ψ : RawSpace × ℝ → ℝ}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushScalar ψ ∈ testFunctions ℝ (Ω ×ˢ I) := by
  rcases hψ with ⟨hψdiff, hψcompact, hψsupport⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hψdiff.comp rawSpaceTimeLinear.symm.contDiff
  · exact hψcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · change tsupport (ψ ∘ rawSpaceTimeToEuclidean.symm) ⊆ Ω ×ˢ I
    rw [tsupport_comp_eq_preimage ψ rawSpaceTimeToEuclidean.symm]
    intro z hz
    have hz' := hψsupport hz
    exact hz'

theorem pushVector_testFunction
    {Ω : Set ℝ³} {I : Set ℝ} {φ : RawSpace × ℝ → RawSpace}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I) :
    pushVector φ ∈ testFunctions ℝ³ (Ω ×ˢ I) := by
  rcases hφ with ⟨hφdiff, hφcompact, hφsupport⟩
  refine ⟨rawToEuclidean.contDiff.comp
    (hφdiff.comp rawSpaceTimeLinear.symm.contDiff), ?_, ?_⟩
  · rw [HasCompactSupport,
      show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm)]
    exact hφcompact.comp_homeomorph rawSpaceTimeToEuclidean.symm
  · rw [show pushVector φ = rawToEuclidean ∘
        (φ ∘ rawSpaceTimeToEuclidean.symm) by rfl,
      tsupport_comp_eq (fun {_} ↦ rawToEuclidean.map_eq_zero_iff)
        (φ ∘ rawSpaceTimeToEuclidean.symm),
      tsupport_comp_eq_preimage φ rawSpaceTimeToEuclidean.symm]
    intro z hz
    exact hφsupport hz

theorem pushScalar_gradient_apply
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
      (rawToEuclidean z.1)) i =
        fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1 (CKN.basisVec i) := by
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single i 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right i 1
        (gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
          (rawToEuclidean z.1))
    _ = fderiv ℝ (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) := inner_gradient_left
    _ = fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) z.1
        (CKN.basisVec i) := by
      change fderiv ℝ (fun x : ℝ³ ↦ ψ (rawToEuclidean.symm x, z.2))
        (rawToEuclidean z.1) (EuclideanSpace.single i 1) = _
      let g : ℝ³ → RawSpace × ℝ := fun x ↦ (rawToEuclidean.symm x, z.2)
      have hg : DifferentiableAt ℝ g (rawToEuclidean z.1) := by
        dsimp [g]
        fun_prop
      have hc : fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1) =
          fderiv ℝ ψ z ∘L fderiv ℝ g (rawToEuclidean z.1) := by
        simpa [g] using fderiv_comp (rawToEuclidean z.1)
          ((hψ.differentiable (by simp)) z) hg
      change (fderiv ℝ (ψ ∘ g) (rawToEuclidean z.1))
        (EuclideanSpace.single i 1) = _
      rw [hc]
      let k : RawSpace → RawSpace × ℝ := fun x ↦ (x, z.2)
      have hk : DifferentiableAt ℝ k z.1 := by
        dsimp [k]
        fun_prop
      have hc' : fderiv ℝ (ψ ∘ k) z.1 =
          fderiv ℝ ψ z ∘L fderiv ℝ k z.1 := by
        simpa [k] using fderiv_comp z.1 ((hψ.differentiable (by simp)) z) hk
      rw [show (fun x : RawSpace ↦ ψ (x, z.2)) = ψ ∘ k by rfl, hc']
      rw [(rawToEuclidean.symm.hasFDerivAt.prodMk
          (hasFDerivAt_const z.2 (rawToEuclidean z.1))).fderiv]
      have hkf : fderiv ℝ k z.1 =
          (ContinuousLinearMap.id ℝ RawSpace).prod 0 := by
        simpa [k] using ((hasFDerivAt_id (𝕜 := ℝ) z.1).prodMk
          (hasFDerivAt_const z.2 z.1)).fderiv
      rw [hkf]
      have hb : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
          (EuclideanSpace.single i 1) = CKN.basisVec i := by
        classical
        ext j
        by_cases hji : j = i
        · subst j
          simp [CKN.basisVec, EuclideanSpace.single]
        · simp [CKN.basisVec, EuclideanSpace.single, hji]
      simp [rawToEuclidean, hb]

theorem inner_pushScalar_gradient
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (v : RawSpace) :
    ⟪rawToEuclidean v,
      gradient (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1)⟫_ℝ =
      ∑ i, v i * fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2))
        z.1 (CKN.basisVec i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [pushScalar_gradient_apply ψ hψ z i]
  simp [rawToEuclidean, mul_comm]


def rawGradient (D : ℝ³ →L[ℝ] ℝ³) : Fin 3 → RawSpace :=
  fun i j ↦ WithLp.ofLp (D (EuclideanSpace.single j 1)) i

def rawGradientLinear : (ℝ³ →L[ℝ] ℝ³) →ₗ[ℝ] (Fin 3 → RawSpace) where
  toFun := rawGradient
  map_add' D E := by
    ext i j
    simp [rawGradient]
  map_smul' c D := by
    ext i j
    simp [rawGradient]

def rawGradientCLM : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] (Fin 3 → RawSpace) :=
  LinearMap.toContinuousLinearMap rawGradientLinear

theorem rawGradient_pushVector
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i j : Fin 3) :
    rawGradient
        (fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, z.2))
          (rawToEuclidean z.1)) i j =
      fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1
        (CKN.basisVec j) := by
  let F : ℝ³ → ℝ³ := fun x ↦ pushVector φ (x, z.2)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hF : DifferentiableAt ℝ F (rawToEuclidean z.1) := by
    have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
      rawToEuclidean.contDiff.comp
        (hφ.comp rawSpaceTimeLinear.symm.contDiff)
    have hfull : DifferentiableAt ℝ (pushVector φ)
        (rawToEuclidean z.1, z.2) :=
      (hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2)
    exact DifferentiableAt.comp (x := rawToEuclidean z.1)
      (f := fun x : ℝ³ ↦ (x, z.2)) (g := pushVector φ)
      hfull (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) (rawToEuclidean z.1) =
      proj ∘L fderiv ℝ F (rawToEuclidean z.1) := by
    simpa using fderiv_comp (rawToEuclidean z.1) proj.differentiableAt hF
  have hφi : ContDiff ℝ (⊤ : ℕ∞) (fun w ↦ φ w i) := by fun_prop
  have hscalar := pushScalar_gradient_apply (fun w ↦ φ w i) hφi z j
  rw [← hscalar]
  change (proj (fderiv ℝ F (rawToEuclidean z.1)
    (EuclideanSpace.single j 1))) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  change fderiv ℝ (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
      (rawToEuclidean z.1) (EuclideanSpace.single j 1) = _
  symm
  calc
    _ = ⟪gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
        (rawToEuclidean z.1), EuclideanSpace.single j 1⟫_ℝ := by
      symm
      simpa using EuclideanSpace.inner_single_right j 1
        (gradient (fun x : ℝ³ ↦ pushScalar (fun w ↦ φ w i) (x, z.2))
          (rawToEuclidean z.1))
    _ = _ := inner_gradient_left

theorem timeDerivative_pushVector_apply
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (i : Fin 3) :
    (rawToEuclidean.symm
      (fderiv ℝ (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1)) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 := by
  let F : ℝ → ℝ³ := fun t ↦ pushVector φ (rawToEuclidean z.1, t)
  let proj : ℝ³ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i
  have hpush : ContDiff ℝ (⊤ : ℕ∞) (pushVector φ) :=
    rawToEuclidean.contDiff.comp
      (hφ.comp rawSpaceTimeLinear.symm.contDiff)
  have hF : DifferentiableAt ℝ F z.2 := by
    exact DifferentiableAt.comp (x := z.2)
      (f := fun t : ℝ ↦ (rawToEuclidean z.1, t)) (g := pushVector φ)
      ((hpush.differentiable (by simp)) (rawToEuclidean z.1, z.2))
      (by fun_prop)
  have hcomp : fderiv ℝ (proj ∘ F) z.2 = proj ∘L fderiv ℝ F z.2 := by
    simpa using fderiv_comp z.2 proj.differentiableAt hF
  change proj (fderiv ℝ F z.2 1) = _
  rw [← ContinuousLinearMap.comp_apply, ← hcomp]
  congr 1


def pullGradient (D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    RawSpace × ℝ → Fin 3 → RawSpace :=
  fun z ↦ rawGradient (D (rawSpaceTimeToEuclidean z))


def pushSpatialScalar (g : RawSpace → ℝ) : ℝ³ → ℝ :=
  fun x ↦ g (rawToEuclidean.symm x)

theorem pushSpatialScalar_testFunction
    {U : Set RawSpace} {g : RawSpace → ℝ}
    (hgdiff : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ U) :
    pushSpatialScalar g ∈ testFunctions ℝ (euclideanSpace U) := by
  refine ⟨hgdiff.comp rawToEuclidean.symm.contDiff,
    hgcompact.comp_homeomorph rawToEuclidean.symm.toHomeomorph, ?_⟩
  change tsupport (g ∘ ⇑rawToEuclidean.symm.toHomeomorph) ⊆ euclideanSpace U
  rw [tsupport_comp_eq_preimage g rawToEuclidean.symm.toHomeomorph]
  intro x hx
  exact ⟨rawToEuclidean.symm x, hgsupport hx,
    rawToEuclidean.apply_symm_apply x⟩

theorem fderiv_pushSpatialScalar_basis
    (g : RawSpace → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : RawSpace) (j : Fin 3) :
    fderiv ℝ (pushSpatialScalar g) (rawToEuclidean x)
        (EuclideanSpace.single j 1) =
      fderiv ℝ g x (CKN.basisVec j) := by
  have hc := fderiv_comp (rawToEuclidean x)
    ((hg.differentiable (by simp)) x)
    rawToEuclidean.symm.differentiableAt
  change fderiv ℝ (g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace))
      (rawToEuclidean x) = _ at hc
  rw [show pushSpatialScalar g =
      g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace) by rfl,
    hc, rawToEuclidean.symm.fderiv]
  simp only [rawToEuclidean.symm_apply_apply,
    ContinuousLinearMap.comp_apply]
  congr 1


theorem weakGradient_transport
    {U : Set RawSpace} {t : ℝ}
    {u : ℝ³ × ℝ → ℝ³}
    {D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)}
    (hD : HasWeakDerivativeOn (euclideanSpace U)
      (fun x ↦ u (x, t)) (fun x ↦ D (x, t))) :
    ∀ i, CKN.HasWeakGradientOn U
      (fun x ↦ pullVelocity u (x, t) i)
      (fun x ↦ pullGradient D (x, t) i) := by
  intro i j g hgdiff hgcompact hgsupport
  let ge := pushSpatialScalar g
  have hge : ge ∈ testFunctions ℝ (euclideanSpace U) :=
    pushSpatialScalar_testFunction hgdiff hgcompact hgsupport
  have hscalar := hD.integral_eq ge hge
    (EuclideanSpace.single j 1)
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i)
  simp_rw [inner_gradient_left] at hscalar
  have hmp := rawToEuclidean_restrict_measurePreserving U
  have hemb := rawToEuclidean.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hemb, ← hmp.integral_comp hemb] at hscalar
  have hderiv (x : RawSpace) :
      fderiv ℝ ge (rawToEuclidean x) (EuclideanSpace.single j 1) =
        fderiv ℝ g x (CKN.basisVec j) :=
    fderiv_pushSpatialScalar_basis g hgdiff x j
  have hge_apply (x : RawSpace) : ge (rawToEuclidean x) = g x := by
    simp [ge, pushSpatialScalar]
  simp_rw [hge_apply, hderiv] at hscalar
  simp only [PiLp.proj_apply] at hscalar
  have hscalar' :
      (∫ x in U, g x * pullGradient D (x, t) i j) =
        -∫ x in U,
          fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
    simpa [pullVelocity, pullGradient, rawGradient,
      rawSpaceTimeToEuclidean, rawSpaceTimeLinear, rawToEuclidean,
      hderiv] using hscalar
  change
    ∫ x in U,
        pullVelocity u (x, t) i * fderiv ℝ g x (CKN.basisVec j) =
      -∫ x in U, pullGradient D (x, t) i j * g x
  calc
    _ = ∫ x in U,
        fderiv ℝ g x (CKN.basisVec j) * pullVelocity u (x, t) i := by
      congr 1
      funext x
      ring
    _ = -∫ x in U, g x * pullGradient D (x, t) i j := by
      linarith
    _ = _ := by
      congr 2
      funext x
      ring


theorem rawGradient_sq (D : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, (rawGradient D i j) ^ 2 =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L D)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j ^ 2 =
        ∑ j, ∑ i, rawGradient D i j ^ 2 := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          D (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, pow_two]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (D (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (D (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_pair (D E : ℝ³ →L[ℝ] ℝ³) :
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
      LinearMap.trace ℝ ℝ³
        (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L E)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  calc
    ∑ i, ∑ j, rawGradient D i j * rawGradient E i j =
        ∑ j, ∑ i, rawGradient D i j * rawGradient E i j := Finset.sum_comm
    _ = ∑ j, ⟪D (EuclideanSpace.single j 1),
          E (EuclideanSpace.single j 1)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.inner_apply]
      simp [rawGradient, mul_comm]
    _ = ∑ j, ⟪EuclideanSpace.single j 1,
          (ContinuousLinearMap.adjoint D) (E (EuclideanSpace.single j 1))⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (ContinuousLinearMap.adjoint_inner_right D _ _).symm
    _ = ∑ j, ((ContinuousLinearMap.adjoint D)
          (E (EuclideanSpace.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [EuclideanSpace.inner_single_left]
      simp

theorem rawGradient_rankOne (v : RawSpace) (i j : Fin 3) :
    rawGradient (InnerProductSpace.rankOne ℝ
      (rawToEuclidean v) (rawToEuclidean v)) i j = v i * v j := by
  simp [rawGradient, rawToEuclidean, InnerProductSpace.rankOne_apply,
    PiLp.inner_apply, mul_comm]

theorem trace_eq_sum_rawGradient_diagonal (D : ℝ³ →L[ℝ] ℝ³) :
    LinearMap.trace ℝ ℝ³ D.toLinearMap = ∑ i, rawGradient D i i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [Matrix.trace]
  rfl

theorem momentum_integrand_transport
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) (u f : RawSpace) (p : ℝ)
    (D : ℝ³ →L[ℝ] ℝ³) :
    let ze := rawSpaceTimeToEuclidean z
    let Dφ := fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, ze.2)) ze.1
    let dtφ := fderiv ℝ (fun t : ℝ ↦ pushVector φ (ze.1, t)) ze.2 1
    ⟪rawToEuclidean u, dtφ⟫_ℝ
        + LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint
            (InnerProductSpace.rankOne ℝ (rawToEuclidean u) (rawToEuclidean u)) ∘L Dφ))
        - LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
          (ContinuousLinearMap.adjoint D ∘L Dφ))
        + p * LinearMap.trace ℝ ℝ³ Dφ.toLinearMap
        + ⟪rawToEuclidean f, pushVector φ ze⟫_ℝ =
      -(-∑ i, u i * fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1
        - ∑ i, ∑ j, u i * u j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        + ∑ i, ∑ j, rawGradient D i j *
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec j)
        - p * ∑ i,
            fderiv ℝ (fun x : RawSpace ↦ φ (x, z.2) i) z.1 (CKN.basisVec i)
        - ∑ i, f i * φ z i) := by
  dsimp only
  simp only [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]
  rw [← rawGradient_pair, ← rawGradient_pair,
    trace_eq_sum_rawGradient_diagonal]
  simp_rw [rawGradient_rankOne]
  simp_rw [rawGradient_pushVector φ hφ z]
  have ht (i : Fin 3) := timeDerivative_pushVector_apply φ hφ z i
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [show ∀ i, (fderiv ℝ
      (fun t : ℝ ↦ pushVector φ (rawToEuclidean z.1, t)) z.2 1) i =
      fderiv ℝ (fun t : ℝ ↦ φ (z.1, t) i) z.2 1 by
    intro i
    simpa [rawToEuclidean] using ht i]
  have hzraw : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
      (WithLp.toLp 2 z.1) = z.1 := by
    ext i
    simp [PiLp.continuousLinearEquiv_apply]
  simp [pushVector, rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    rawToEuclidean, hzraw, mul_comm, mul_assoc]
  ring

theorem iteratedFDeriv_two_same
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x b : E) :
    iteratedFDeriv ℝ 2 g x ![b, b] =
      fderiv ℝ (fun y ↦ fderiv ℝ g y b) x b := by
  rw [iteratedFDeriv_two_apply]
  have hg2 : ContDiff ℝ (1 + 1) g := hg.of_le (by simp)
  have hfd_cont : ContDiff ℝ 1 (fderiv ℝ g) :=
    (contDiff_succ_iff_fderiv.mp hg2).2.2
  have hfd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hfd_cont.differentiable (by norm_num)) x
  have hc := fderiv_clm_apply hfd
    (differentiableAt_const (c := b) (x := x))
  rw [hc]
  simp

theorem laplacian_pushScalar
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) :
    Laplacian.laplacian (fun x : ℝ³ ↦ pushScalar ψ (x, z.2))
        (rawToEuclidean z.1) =
      ∑ i, fderiv ℝ
        (fun y : RawSpace ↦
          fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) y (CKN.basisVec i))
        z.1 (CKN.basisVec i) := by
  let g : RawSpace → ℝ := fun x ↦ ψ (x, z.2)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    exact hψ.comp (by fun_prop)
  change Laplacian.laplacian (g ∘ rawToEuclidean.symm)
      (rawToEuclidean z.1) = _
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (g ∘ rawToEuclidean.symm) (EuclideanSpace.basisFun (Fin 3) ℝ))
    (rawToEuclidean z.1)]
  apply Finset.sum_congr rfl
  intro i _
  change (iteratedFDeriv ℝ 2
      (g ∘ (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace))
      (rawToEuclidean z.1))
      ![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        (EuclideanSpace.basisFun (Fin 3) ℝ) i] = _
  rw [rawToEuclidean.symm.toContinuousLinearMap.iteratedFDeriv_comp_right
    hg (rawToEuclidean z.1) (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hb : rawToEuclidean.symm ((EuclideanSpace.basisFun (Fin 3) ℝ) i) =
      CKN.basisVec i := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [rawToEuclidean, CKN.basisVec, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single]
    · simp [rawToEuclidean, CKN.basisVec, EuclideanSpace.basisFun_apply,
        EuclideanSpace.single, hji]
  have hx : (rawToEuclidean.symm : ℝ³ → RawSpace) (rawToEuclidean z.1) = z.1 :=
    rawToEuclidean.symm_apply_apply z.1
  change (iteratedFDeriv ℝ 2 g
      ((rawToEuclidean.symm : ℝ³ → RawSpace) (rawToEuclidean z.1)))
      (fun k ↦ (rawToEuclidean.symm : ℝ³ → RawSpace)
        (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
          (EuclideanSpace.basisFun (Fin 3) ℝ) i] k)) = _
  rw [hx]
  have hm : (fun k ↦ (rawToEuclidean.symm : ℝ³ → RawSpace)
      (![(EuclideanSpace.basisFun (Fin 3) ℝ) i,
        (EuclideanSpace.basisFun (Fin 3) ℝ) i] k)) =
      ![CKN.basisVec i, CKN.basisVec i] := by
    funext k
    fin_cases k <;> exact hb
  rw [hm, iteratedFDeriv_two_same g hg z.1 (CKN.basisVec i)]

theorem timeDerivative_pushScalar
    (ψ : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) :
    fderiv ℝ (fun t : ℝ ↦ pushScalar ψ (rawToEuclidean z.1, t)) z.2 1 =
      fderiv ℝ (fun t : ℝ ↦ ψ (z.1, t)) z.2 1 := by
  congr 2

theorem energy_integrand_transport
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (z : RawSpace × ℝ) (u f : RawSpace) (p : ℝ) :
    let ze := rawSpaceTimeToEuclidean z
    ‖rawToEuclidean u‖ ^ 2 *
          (fderiv ℝ (fun t : ℝ ↦ pushScalar ψ (ze.1, t)) ze.2 1 +
            Laplacian.laplacian (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1)
        + (‖rawToEuclidean u‖ ^ 2 + 2 * p) *
            ⟪rawToEuclidean u,
              gradient (fun x : ℝ³ ↦ pushScalar ψ (x, ze.2)) ze.1⟫_ℝ
        + 2 * ⟪rawToEuclidean f, rawToEuclidean u⟫_ℝ * pushScalar ψ ze =
      (CKN.Foundation.Parabolic.vec3EuclideanNorm u) ^ 2 *
          (fderiv ℝ (fun t : ℝ ↦ ψ (z.1, t)) z.2 1 +
            ∑ i, fderiv ℝ
              (fun y : RawSpace ↦
                fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2)) y (CKN.basisVec i))
              z.1 (CKN.basisVec i))
        + ((CKN.Foundation.Parabolic.vec3EuclideanNorm u) ^ 2 + 2 * p) *
            ∑ i, u i * fderiv ℝ (fun x : RawSpace ↦ ψ (x, z.2))
              z.1 (CKN.basisVec i)
        + 2 * (∑ i, f i * u i) * ψ z := by
  dsimp only
  simp only [rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]
  rw [timeDerivative_pushScalar, laplacian_pushScalar ψ hψ z,
    inner_pushScalar_gradient ψ hψ z u,
    ← CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  rw [PiLp.inner_apply]
  have hzraw : (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ))
      (WithLp.toLp 2 z.1) = z.1 := by
    ext i
    simp [PiLp.continuousLinearEquiv_apply]
  simp [pushScalar, rawSpaceTimeToEuclidean, rawSpaceTimeLinear,
    rawToEuclidean, hzraw, mul_comm]


theorem parabolicDist_le_sqrt_dist_of_dist_le_one
    (z w : RawPoint)
    (hd : dist (rawSpaceTimeToEuclidean z)
      (rawSpaceTimeToEuclidean w) ≤ 1) :
    CKN.Foundation.Parabolic.parabolicDist z w ≤
      Real.sqrt (dist (rawSpaceTimeToEuclidean z)
        (rawSpaceTimeToEuclidean w)) := by
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean w)
  have hspace : dist (rawToEuclidean z.1) (rawToEuclidean w.1) ≤
      Real.sqrt d := by
    exact (le_max_left _ _).trans
      (Real.le_sqrt_self_iff.mpr hd)
  have htime : Real.sqrt (dist z.2 w.2) ≤ Real.sqrt d := by
    apply Real.sqrt_le_sqrt
    exact le_max_right _ _
  rw [CKN.Foundation.Parabolic.parabolicDist,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  have hspace_eq : ‖WithLp.toLp 2 (z.1 - w.1)‖ =
      dist (rawToEuclidean z.1) (rawToEuclidean w.1) := by
    rw [dist_eq_norm, ← map_sub]
    rfl
  rw [hspace_eq, ← Real.dist_eq]
  exact max_le hspace htime

theorem pushVector_dist_eq_vec3EuclideanNorm
    (w : RawSpace × ℝ → RawSpace) (z z' : RawSpace × ℝ) :
    dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z')) =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') := by
  rw [pushVector_rawSpaceTimeToEuclidean,
    pushVector_rawSpaceTimeToEuclidean, dist_eq_norm,
    CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2]
  change ‖rawToEuclidean (w z) - rawToEuclidean (w z')‖ =
    ‖rawToEuclidean (w z - w z')‖
  rw [map_sub]

theorem pushVector_holderOnWith_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {γ B K : ℝ}
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hsup : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B)
    (hseminorm : ∀ z ∈ N, ∀ z' ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
        K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ) :
    HolderOnWith ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ (pushVector w)
      (parabolicToEuclideanHomeomorph '' N) := by
  intro x hx x' hx'
  rcases hx with ⟨z, hz, hzx⟩
  rcases hx' with ⟨z', hz', hzx'⟩
  have hxcoord : x = rawSpaceTimeToEuclidean z := by rw [← hzx]; rfl
  have hx'coord : x' = rawSpaceTimeToEuclidean z' := by rw [← hzx']; rfl
  rw [hxcoord, hx'coord]
  have hout := pushVector_dist_eq_vec3EuclideanNorm w z z'
  let d := dist (rawSpaceTimeToEuclidean z) (rawSpaceTimeToEuclidean z')
  have hreal :
      dist (pushVector w (rawSpaceTimeToEuclidean z))
          (pushVector w (rawSpaceTimeToEuclidean z')) ≤
        max K (2 * B) * d ^ (γ / 2) := by
    rw [hout]
    by_cases hd : d ≤ 1
    · have hpar := parabolicDist_le_sqrt_dist_of_dist_le_one z z' hd
      have hpar0 : 0 ≤ CKN.Foundation.Parabolic.parabolicDist z z' := by
        unfold CKN.Foundation.Parabolic.parabolicDist
        positivity
      have hpow := Real.rpow_le_rpow hpar0 hpar hγ.le
      calc
        _ ≤ K * CKN.Foundation.Parabolic.parabolicDist z z' ^ γ :=
          hseminorm z hz z' hz'
        _ ≤ K * Real.sqrt d ^ γ :=
          mul_le_mul_of_nonneg_left hpow hK
        _ = K * d ^ (γ / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (dist_nonneg : 0 ≤ d)]
          congr 2
          ring
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          gcongr
          exact le_max_left _ _
    · have hnorm :
          CKN.Foundation.Parabolic.vec3EuclideanNorm (w z - w z') ≤
            CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) +
              CKN.Foundation.Parabolic.vec3EuclideanNorm (w z') := by
          simp only [CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2,
            WithLp.toLp_sub]
          exact norm_sub_le _ _
      have hd1 : 1 ≤ d := le_of_not_ge hd
      have hpow1 : 1 ≤ d ^ (γ / 2) := by
        exact Real.one_le_rpow hd1 (div_nonneg hγ.le (by norm_num))
      calc
        _ ≤ 2 * B := by linarith [hsup z hz, hsup z' hz']
        _ ≤ max K (2 * B) := le_max_right _ _
        _ ≤ max K (2 * B) * d ^ (γ / 2) := by
          nlinarith [hK.trans (le_max_left K (2 * B))]
  rw [edist_dist, edist_dist]
  let C : ℝ≥0 :=
    ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  change ENNReal.ofReal
      (dist (pushVector w (rawSpaceTimeToEuclidean z))
        (pushVector w (rawSpaceTimeToEuclidean z'))) ≤
    (C : ℝ≥0∞) * ENNReal.ofReal d ^ (γ / 2)
  rw [show (C : ℝ≥0∞) = ENNReal.ofReal (max K (2 * B)) by
      rw [ENNReal.ofReal_eq_coe_nnreal
        (hK.trans (le_max_left K (2 * B)))]; rfl,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg
      (div_nonneg hγ.le (by norm_num)),
    ← ENNReal.ofReal_mul (hK.trans (le_max_left K (2 * B)))]
  exact ENNReal.ofReal_le_ofReal hreal


theorem pushVector_aeEq_on_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace}
    {u : ℝ³ × ℝ → ℝ³}
    (hw : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u) :
    pushVector w =ᵐ[(volume : Measure (ℝ³ × ℝ)).restrict
      (parabolicToEuclideanHomeomorph '' N)] u := by
  let hmp := parabolicToEuclidean_measurePreserving.restrict_preimage_emb
    parabolicToEuclideanHomeomorph.measurableEmbedding
      (parabolicToEuclideanHomeomorph '' N)
  have hpre : parabolicToEuclideanHomeomorph ⁻¹'
      (parabolicToEuclideanHomeomorph '' N) = N :=
    Equiv.preimage_image parabolicToEuclideanHomeomorph.toEquiv N
  rw [hpre] at hmp
  rw [← hmp.map_eq]
  apply parabolicToEuclideanHomeomorph.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hw] with z hz
  change rawToEuclidean (w z) = u (rawToEuclidean z.1, z.2)
  rw [hz]
  change rawToEuclidean
    (rawToEuclidean.symm (u (rawToEuclidean z.1, z.2))) = _
  rw [rawToEuclidean.apply_symm_apply]

theorem pushVector_enorm_le_image
    {N : Set RawPoint} {w : RawSpace × ℝ → RawSpace} {B : ℝ}
    (hw : ∀ z ∈ N,
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) ≤ B) :
    ∀ z : parabolicToEuclideanHomeomorph '' N,
      ‖pushVector w z‖ₑ ≤ ENNReal.ofReal B := by
  rintro ⟨ze, z, hz, hze⟩
  subst ze
  change ‖rawToEuclidean (w z)‖ₑ ≤ ENNReal.ofReal B
  rw [← ofReal_norm,
    show ‖rawToEuclidean (w z)‖ =
      CKN.Foundation.Parabolic.vec3EuclideanNorm (w z) by
        exact (CKN.Foundation.Parabolic.vec3EuclideanNorm_eq_l2 _).symm]
  exact ENNReal.ofReal_le_ofReal (hw z hz)

theorem pushVector_aeHolderNormOn_image_lt_top
    {N : Set RawPoint} {u : ℝ³ × ℝ → ℝ³}
    {w : RawSpace × ℝ → RawSpace} {γ : ℝ} (hγ : 0 < γ)
    (hae : w =ᵐ[(volume : Measure RawPoint).restrict N] pullVelocity u)
    (hholder : CKN.ParabolicHolderVecOn N w γ) :
    aeHolderNormOn (parabolicToEuclideanHomeomorph '' N) u
      ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩ < ∞ := by
  rcases hholder with ⟨B, K, hB, hK, hsup, hseminorm⟩
  have haeImage := pushVector_aeEq_on_image hae
  have hHolder :=
    (pushVector_holderOnWith_image hγ hK hsup hseminorm).holderWith
  let C : ℝ≥0 := ⟨max K (2 * B), hK.trans (le_max_left _ _)⟩
  have hHolderNorm :
      eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
          ((parabolicToEuclideanHomeomorph '' N).domRestrict
            (pushVector w)) ≤ (C : ℝ≥0∞) :=
    hHolder.eHolderNorm_le
  unfold aeHolderNormOn
  calc
    (⨅ (v : ℝ³ × ℝ → ℝ³)
        (_ : v =ᵐ[volume.restrict
          (parabolicToEuclideanHomeomorph '' N)] u),
        (⨆ z : parabolicToEuclideanHomeomorph '' N, ‖v z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict v)) ≤
        (⨆ z : parabolicToEuclideanHomeomorph '' N,
          ‖pushVector w z‖ₑ) +
          eHolderNorm ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩
            ((parabolicToEuclideanHomeomorph '' N).domRestrict
              (pushVector w)) :=
      iInf_le_of_le (pushVector w) (iInf_le_of_le haeImage le_rfl)
    _ ≤ ENNReal.ofReal B + (C : ℝ≥0∞) :=
      add_le_add (iSup_le (pushVector_enorm_le_image hsup)) hHolderNorm
    _ < ∞ := ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, ENNReal.coe_lt_top⟩

theorem isHolderRegularPoint_of_rawRegular
    {Ω : Set ℝ³} {I : Set ℝ} {u : ℝ³ × ℝ → ℝ³} {z₀ : RawPoint}
    (hreg : CKN.IsRegularPoint (rawSpace Ω) I (pullVelocity u) z₀) :
    IsHolderRegularPoint u (parabolicToEuclideanHomeomorph z₀) := by
  rcases hreg with ⟨_, N, hNopen, hzN, _, γ, hγ, hγle, w, hae, hholder⟩
  refine ⟨parabolicToEuclideanHomeomorph '' N,
    parabolicToEuclideanHomeomorph.isOpenMap N hNopen,
    ⟨z₀, hzN, rfl⟩,
    ⟨γ / 2, div_nonneg hγ.le (by norm_num)⟩, ?_, ?_, ?_⟩
  · exact div_pos hγ (by norm_num)
  · change γ / 2 ≤ (1 : ℝ)
    linarith
  · exact pushVector_aeHolderNormOn_image_lt_top hγ hae hholder


theorem parabolicHausdorffMeasure_one_image (S : Set RawPoint) :
    parabolicHausdorffMeasure 1
        (parabolicToEuclideanHomeomorph '' S) =
      CKN.Foundation.Parabolic.parabolicHausdorffMeasure 1 S := by
  let e : (ℝ³ × Rpar) ≃ₜ (ℝ³ × ℝ) :=
    (Homeomorph.refl ℝ³).prodCongr
      (Metric.Snowflaking.homeomorph : Rpar ≃ₜ ℝ)
  have he (z : RawPoint) : e (rawParabolicIsometry z) =
      parabolicToEuclideanHomeomorph z := by
    rfl
  have hpre : e.toMeasurableEquiv ⁻¹'
      (parabolicToEuclideanHomeomorph '' S) = rawParabolicIsometry '' S := by
    ext y
    constructor
    · rintro ⟨z, hz, heq⟩
      refine ⟨z, hz, ?_⟩
      apply e.injective
      exact (he z).trans heq
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, (he z).symm⟩
  unfold parabolicHausdorffMeasure
  change Measure.map e.toMeasurableEquiv
      (Measure.hausdorffMeasure 1 : Measure (ℝ³ × Rpar))
        (parabolicToEuclideanHomeomorph '' S) = _
  rw [MeasurableEquiv.map_apply, hpre,
    rawParabolicIsometry.hausdorffMeasure_image]
  rfl



/-! ### Coordinate transport: gradients, sets, and Lebesgue spaces -/

theorem euclideanSpace_univ : euclideanSpace (Set.univ : Set RawSpace) = Set.univ :=
  Set.image_univ_of_surjective rawToEuclidean.surjective

theorem rawSpace_univ : rawSpace (Set.univ : Set ℝ³) = Set.univ := Set.preimage_univ

theorem eq_sum_single (v : ℝ³) :
    v = ∑ j, WithLp.ofLp v j • EuclideanSpace.single j (1 : ℝ) := by
  ext k
  simp [Pi.single_apply]

/-- The linear map of `ℝ³` with matrix `M`. -/
def matCLM (M : Fin 3 → RawSpace) : ℝ³ →L[ℝ] ℝ³ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => ∑ j, M i j * WithLp.ofLp v j)
      map_add' := by
        intro v w
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext i
        simp [Finset.mul_sum, mul_left_comm] }

theorem matCLM_apply (M : Fin 3 → RawSpace) (v : ℝ³) (i : Fin 3) :
    WithLp.ofLp (matCLM M v) i = ∑ j, M i j * WithLp.ofLp v j := rfl

theorem rawGradient_matCLM (M : Fin 3 → RawSpace) : rawGradient (matCLM M) = M := by
  ext i j
  simp [rawGradient, matCLM_apply]

theorem matCLM_rawGradient (D : ℝ³ →L[ℝ] ℝ³) : matCLM (rawGradient D) = D := by
  ext v i
  rw [matCLM_apply]
  conv_rhs => rw [eq_sum_single v]
  simp [_root_.map_sum, rawGradient, mul_comm]

/-- The Euclidean weak gradient corresponding to a coordinate gradient. -/
def pushGradient (M : RawSpace × ℝ → Fin 3 → RawSpace) : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³) :=
  fun z => matCLM (M (rawSpaceTimeToEuclidean.symm z))

theorem pullGradient_pushGradient (M : RawSpace × ℝ → Fin 3 → RawSpace) :
    pullGradient (pushGradient M) = M := by
  funext z
  change rawGradient (matCLM
    (M (rawSpaceTimeToEuclidean.symm (rawSpaceTimeToEuclidean z)))) = M z
  rw [rawSpaceTimeToEuclidean.symm_apply_apply, rawGradient_matCLM]

theorem pushGradient_pullGradient (D : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    pushGradient (pullGradient D) = D := by
  funext z
  simp [pullGradient, pushGradient, matCLM_rawGradient]

theorem pullVelocity_pushVector (g : RawSpace × ℝ → RawSpace) :
    pullVelocity (pushVector g) = g := by
  funext z
  simp [pullVelocity]

theorem pushVector_pullVelocity (u : ℝ³ × ℝ → ℝ³) :
    pushVector (pullVelocity u) = u := by
  funext z
  simp [pullVelocity, pushVector]

theorem pullScalar_pushScalar (g : RawSpace × ℝ → ℝ) :
    pullScalar (pushScalar g) = g := by
  funext z
  simp [pullScalar]

theorem pushScalar_pullScalar (g : ℝ³ × ℝ → ℝ) :
    pushScalar (pullScalar g) = g := by
  funext z
  simp [pullScalar, pushScalar]

theorem rawSpaceTimeToEuclidean_symm_apply (z : ℝ³ × ℝ) :
    rawSpaceTimeToEuclidean.symm z = (rawToEuclidean.symm z.1, z.2) := by
  rw [Homeomorph.symm_apply_eq]
  simp

/-- The coordinate representative of a spatial field. -/
def pullSpatial (a : ℝ³ → ℝ³) : RawSpace → RawSpace :=
  fun x => rawToEuclidean.symm (a (rawToEuclidean x))

/-- The Euclidean representative of a coordinate spatial field. -/
def pushSpatial (a : RawSpace → RawSpace) : ℝ³ → ℝ³ :=
  fun x => rawToEuclidean (a (rawToEuclidean.symm x))

theorem pullSpatial_pushSpatial (a : RawSpace → RawSpace) :
    pullSpatial (pushSpatial a) = a := by
  funext x
  simp [pullSpatial, pushSpatial]

theorem pushSpatial_pullSpatial (a : ℝ³ → ℝ³) : pushSpatial (pullSpatial a) = a := by
  funext x
  simp [pullSpatial, pushSpatial]

/-! ### Lebesgue spaces and integrals under the coordinate change -/

theorem memLp_clm_iff {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E ≃L[ℝ] F) (g : α → E) (p : ℝ≥0∞) :
    MemLp (fun x => T (g x)) p μ ↔ MemLp g p μ := by
  constructor
  · intro h
    have := h.continuousLinearMap_comp (T.symm : F →L[ℝ] E)
    simpa using this
  · intro h
    exact h.continuousLinearMap_comp (T : E →L[ℝ] F)

theorem aesm_clm_iff {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E ≃L[ℝ] F) (g : α → E) :
    AEStronglyMeasurable (fun x => T (g x)) μ ↔ AEStronglyMeasurable g μ := by
  constructor
  · intro h
    have := T.symm.continuous.comp_aestronglyMeasurable h
    simpa [Function.comp_def] using this
  · intro h
    exact T.continuous.comp_aestronglyMeasurable h

theorem memLp_euclid_iff {X : Type*} [NormedAddCommGroup X] (U : Set RawSpace) (J : Set ℝ)
    (F : ℝ³ × ℝ → X) (p : ℝ≥0∞) :
    MemLp F p (volume.restrict (euclideanSpace U ×ˢ J)) ↔
      MemLp (fun z => F (rawSpaceTimeToEuclidean z)) p (volume.restrict (U ×ˢ J)) := by
  have hmp := rawSpaceTime_restrict_measurePreserving U J
  have h := rawSpaceTimeToEuclidean.measurableEmbedding.memLp_map_measure_iff
    (μ := volume.restrict (U ×ˢ J)) (g := F) (p := p)
  rw [hmp.map_eq] at h
  exact h

theorem aesm_euclid_iff {X : Type*} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    (U : Set RawSpace) (J : Set ℝ) (F : ℝ³ × ℝ → X) :
    AEStronglyMeasurable F (volume.restrict (euclideanSpace U ×ˢ J)) ↔
      AEStronglyMeasurable (fun z => F (rawSpaceTimeToEuclidean z))
        (volume.restrict (U ×ˢ J)) :=
  ((rawSpaceTime_restrict_measurePreserving U J).aestronglyMeasurable_comp_iff
    rawSpaceTimeToEuclidean.measurableEmbedding (g := F)).symm

theorem lintegral_euclid (U : Set RawSpace) (J : Set ℝ) (F : ℝ³ × ℝ → ℝ≥0∞) :
    ∫⁻ z in euclideanSpace U ×ˢ J, F z = ∫⁻ z in U ×ˢ J, F (rawSpaceTimeToEuclidean z) :=
  ((rawSpaceTime_restrict_measurePreserving U J).lintegral_comp_emb
    rawSpaceTimeToEuclidean.measurableEmbedding F).symm

theorem integral_euclid {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set RawSpace) (J : Set ℝ) (F : ℝ³ × ℝ → X) :
    ∫ z in euclideanSpace U ×ˢ J, F z = ∫ z in U ×ˢ J, F (rawSpaceTimeToEuclidean z) :=
  ((rawSpaceTime_restrict_measurePreserving U J).integral_comp
    rawSpaceTimeToEuclidean.measurableEmbedding F).symm

theorem lintegral_euclid_space (F : ℝ³ → ℝ≥0∞) :
    ∫⁻ x, F x = ∫⁻ x : RawSpace, F (rawToEuclidean x) :=
  (rawToEuclidean_measurePreserving.lintegral_comp_emb
    rawToEuclidean.toHomeomorph.measurableEmbedding F).symm

theorem integral_euclid_space {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : ℝ³ → X) :
    ∫ x, F x = ∫ x : RawSpace, F (rawToEuclidean x) :=
  (rawToEuclidean_measurePreserving.integral_comp
    rawToEuclidean.toHomeomorph.measurableEmbedding F).symm

theorem spaceTimeSet_eq (Ω : Set RawSpace) (I : Set ℝ) :
    CKN.spaceTimeSet Ω I = Ω ×ˢ I := rfl

theorem volume_slab_eq (I : Set ℝ) :
    (volume : Measure RawPoint).restrict (CKN.spaceTimeSet (Set.univ : Set RawSpace) I) =
      (volume : Measure (RawSpace × ℝ)).restrict (Set.univ ×ˢ I) := by
  rw [volume_rawPoint_eq_product]
  rfl

theorem enorm_clm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) :
    ∃ c : ℝ≥0, ∀ x, ‖T x‖ₑ ≤ (c : ℝ≥0∞) * ‖x‖ₑ := by
  refine ⟨‖T‖₊, fun x => ?_⟩
  have h := T.le_opNNNorm x
  simpa [enorm, ← ENNReal.coe_mul] using ENNReal.coe_le_coe.2 h

/-- A squared `L²` integrand is controlled by a constant multiple under a continuous
linear change of the values. -/
theorem lintegral_enorm_sq_clm_le {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ g : α → E,
      ∫⁻ x, ‖T (g x)‖ₑ ^ (2 : ℝ) ∂μ ≤ c * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  obtain ⟨c, hc⟩ := enorm_clm_le T
  refine ⟨(c : ℝ≥0∞) ^ (2 : ℝ), by simp, fun g => ?_⟩
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_mono
  intro x
  calc ‖T (g x)‖ₑ ^ (2 : ℝ) ≤ ((c : ℝ≥0∞) * ‖g x‖ₑ) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow (hc _) (by norm_num)
    _ = (c : ℝ≥0∞) ^ (2 : ℝ) * ‖g x‖ₑ ^ (2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

theorem essSup_lt_top_of_le {f g : ℝ → ℝ≥0∞} {ν : Measure ℝ} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ s, f s ≤ c * g s) (hg : essSup g ν < ∞) : essSup f ν < ∞ := by
  calc essSup f ν ≤ essSup (fun s => c * g s) ν :=
        essSup_mono_ae (Filter.Eventually.of_forall h)
    _ = c * essSup g ν := ENNReal.essSup_const_mul
    _ < ∞ := ENNReal.mul_lt_top hc.lt_top hg

/-! ### Test functions under the coordinate change -/

theorem pullScalar_testFunction {Ω : Set ℝ³} {I : Set ℝ} {ψ : ℝ³ × ℝ → ℝ}
    (hψ : ψ ∈ testFunctions ℝ (Ω ×ˢ I)) :
    pullScalar ψ ∈ CKN.spaceTimeTestFunction (rawSpace Ω) I := by
  rcases hψ with ⟨hdiff, hcompact, hsupport⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hdiff.comp rawSpaceTimeLinear.contDiff
  · exact hcompact.comp_homeomorph rawSpaceTimeToEuclidean
  · change tsupport (ψ ∘ rawSpaceTimeToEuclidean) ⊆ rawSpace Ω ×ˢ I
    rw [tsupport_comp_eq_preimage ψ rawSpaceTimeToEuclidean]
    intro z hz
    exact hsupport hz

theorem pullVelocity_testFunction {Ω : Set ℝ³} {I : Set ℝ} {φ : ℝ³ × ℝ → ℝ³}
    (hφ : φ ∈ testFunctions ℝ³ (Ω ×ˢ I)) :
    pullVelocity φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) (rawSpace Ω) I := by
  rcases hφ with ⟨hdiff, hcompact, hsupport⟩
  refine ⟨?_, ?_, ?_⟩
  · exact rawToEuclidean.symm.contDiff.comp (hdiff.comp rawSpaceTimeLinear.contDiff)
  · exact (hcompact.comp_homeomorph rawSpaceTimeToEuclidean).comp_left
      (g := rawToEuclidean.symm) (by simp)
  · refine (tsupport_comp_subset (g := rawToEuclidean.symm) (by simp)
      (φ ∘ rawSpaceTimeToEuclidean)).trans ?_
    rw [tsupport_comp_eq_preimage φ rawSpaceTimeToEuclidean]
    intro z hz
    exact hsupport hz

/-- Coordinate representative of a scalar spatial test function. -/
def pullSpatialScalar (g : ℝ³ → ℝ) : RawSpace → ℝ := fun x => g (rawToEuclidean x)

theorem pushSpatialScalar_pullSpatialScalar (g : ℝ³ → ℝ) :
    pushSpatialScalar (pullSpatialScalar g) = g := by
  funext x
  simp [pushSpatialScalar, pullSpatialScalar]

theorem pullSpatialScalar_testFunction {ψ : ℝ³ → ℝ}
    (hψ : ψ ∈ testFunctions ℝ (Set.univ : Set ℝ³)) :
    ContDiff ℝ (⊤ : ℕ∞) (pullSpatialScalar ψ) ∧ HasCompactSupport (pullSpatialScalar ψ) :=
  ⟨hψ.1.comp rawToEuclidean.contDiff,
    hψ.2.1.comp_homeomorph rawToEuclidean.toHomeomorph⟩

/-! ### Weak derivatives: coordinate to Euclidean -/

theorem slice_memLp_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (I : Set ℝ) (F : ℝ³ × ℝ → V) (hF : MemLp F 2 (volume.restrict (Set.univ ×ˢ I))) :
    ∀ᵐ s ∂(volume.restrict I), MemLp (fun x : ℝ³ => F (x, s)) 2 volume := by
  have hμ : (volume : Measure (ℝ³ × ℝ)).restrict (Set.univ ×ˢ I) =
      (volume : Measure ℝ³).prod (volume.restrict I) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hμ] at hF
  have hint : Integrable (fun z => ‖F z‖ ^ 2)
      ((volume : Measure ℝ³).prod (volume.restrict I)) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  filter_upwards [hint.prod_left_ae, hF.aestronglyMeasurable.prodMk_right] with s h1 h2
  exact (memLp_two_iff_integrable_sq_norm h2).mpr h1

theorem clm_expand_vec (y' : ℝ³ →L[ℝ] ℝ) (w : ℝ³) :
    y' w = ∑ i, y' (EuclideanSpace.single i 1) * WithLp.ofLp w i := by
  conv_lhs => rw [eq_sum_single w]
  simp [_root_.map_sum, mul_comm]

theorem clm_expand_mat (y' : ℝ³ →L[ℝ] ℝ) (D : ℝ³ →L[ℝ] ℝ³) (v : ℝ³) :
    y' (D v) = ∑ i, ∑ j, y' (EuclideanSpace.single i 1) * WithLp.ofLp v j *
      rawGradient D i j := by
  rw [clm_expand_vec y' (D v)]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [eq_sum_single v]
  simp only [_root_.map_sum, map_smul, rawGradient]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fderiv_expand (f : ℝ³ → ℝ) (x v : ℝ³) :
    fderiv ℝ f x v = ∑ j, WithLp.ofLp v j * fderiv ℝ f x (EuclideanSpace.single j 1) := by
  conv_lhs => rw [eq_sum_single v]
  simp [_root_.map_sum]

theorem memLp_entry {D : ℝ³ → (ℝ³ →L[ℝ] ℝ³)}
    (hD : MemLp D 2 volume) (i j : Fin 3) :
    MemLp (fun x => rawGradient (D x) i j) 2 volume := by
  let evalEntry : (ℝ³ →L[ℝ] ℝ³) →L[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i).comp
      (ContinuousLinearMap.apply ℝ ℝ³ (EuclideanSpace.single j 1))
  have h := hD.continuousLinearMap_comp evalEntry
  simpa [evalEntry, rawGradient] using h

theorem hasWeakDerivativeOn_univ_of_raw {u : ℝ³ → ℝ³} {D : ℝ³ → (ℝ³ →L[ℝ] ℝ³)}
    (hu : MemLp u 2 volume) (hD : MemLp D 2 volume)
    (h : ∀ i : Fin 3, CKN.HasWeakGradientOn (Set.univ : Set RawSpace)
      (fun x => WithLp.ofLp (u (rawToEuclidean x)) i)
      (fun x => rawGradient (D (rawToEuclidean x)) i)) :
    HasWeakDerivativeOn (Set.univ : Set ℝ³) u D := by
  have huloc : LocallyIntegrable u volume := hu.locallyIntegrable (by norm_num)
  have hDloc : LocallyIntegrable D volume := hD.locallyIntegrable (by norm_num)
  refine ⟨huloc.locallyIntegrableOn _, hDloc.locallyIntegrableOn _, ?_⟩
  intro φ hφ v y'
  obtain ⟨hφdiff, hφcompact, -⟩ := hφ
  set g := pullSpatialScalar φ with hg
  have hg' := pullSpatialScalar_testFunction (ψ := φ) ⟨hφdiff, hφcompact, by simp⟩
  -- integrability
  have hA : ∀ i j : Fin 3, Integrable (fun x => φ x * rawGradient (D x) i j) volume := by
    intro i j
    have hloc : LocallyIntegrable (fun x => rawGradient (D x) i j) volume :=
      (memLp_entry hD i j).locallyIntegrable (by norm_num)
    simpa using hloc.integrable_smul_left_of_hasCompactSupport hφdiff.continuous hφcompact
  have hB : ∀ i j : Fin 3, Integrable
      (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1) * WithLp.ofLp (u x) i) volume := by
    intro i j
    have hloc : LocallyIntegrable (fun x => WithLp.ofLp (u x) i) volume := by
      have := hu.continuousLinearMap_comp (EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ)
      simpa using this.locallyIntegrable (by norm_num)
    have hc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      (hφdiff.continuous_fderiv (by simp)).clm_apply continuous_const
    have hs : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
      hφcompact.fderiv_apply ℝ _
    simpa using hloc.integrable_smul_left_of_hasCompactSupport hc hs
  -- the identity in each component
  have hcomp : ∀ i j : Fin 3,
      ∫ x, φ x * rawGradient (D x) i j =
        -∫ x, fderiv ℝ φ x (EuclideanSpace.single j 1) * WithLp.ofLp (u x) i := by
    intro i j
    have h1 := h i j g hg'.1 hg'.2 (by simp)
    simp only [Measure.restrict_univ] at h1
    rw [integral_euclid_space, integral_euclid_space]
    have hd : ∀ x : RawSpace, fderiv ℝ φ (rawToEuclidean x) (EuclideanSpace.single j 1) =
        fderiv ℝ g x (CKN.basisVec j) := by
      intro x
      have := fderiv_pushSpatialScalar_basis g hg'.1 x j
      rwa [hg, pushSpatialScalar_pullSpatialScalar] at this
    simp_rw [hd]
    have e1 : ∀ x : RawSpace, φ (rawToEuclidean x) * rawGradient (D (rawToEuclidean x)) i j =
        rawGradient (D (rawToEuclidean x)) i j * g x := fun x => by rw [hg]; simp [pullSpatialScalar, mul_comm]
    have e2 : ∀ x : RawSpace, fderiv ℝ g x (CKN.basisVec j) * WithLp.ofLp (u (rawToEuclidean x)) i =
        WithLp.ofLp (u (rawToEuclidean x)) i * fderiv ℝ g x (CKN.basisVec j) := fun x => mul_comm _ _
    simp_rw [e1, e2]
    linarith only [h1]
  -- expand both sides
  set c : Fin 3 → Fin 3 → ℝ := fun i j => y' (EuclideanSpace.single i 1) * WithLp.ofLp v j with hc
  have hL : ∀ x, φ x * y' (D x v) = ∑ i, ∑ j, c i j * (φ x * rawGradient (D x) i j) := by
    intro x
    rw [clm_expand_mat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hc]
    ring
  have hR : ∀ x, ⟪∇ φ x, v⟫_ℝ * y' (u x) = ∑ i, ∑ j,
      c i j * (fderiv ℝ φ x (EuclideanSpace.single j 1) * WithLp.ofLp (u x) i) := by
    intro x
    rw [inner_gradient_left, fderiv_expand φ x v, clm_expand_vec y' (u x), Finset.sum_mul_sum,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [hc]
    ring
  have hsum : ∀ (F : Fin 3 → Fin 3 → ℝ³ → ℝ), (∀ i j, Integrable (F i j) volume) →
      ∫ x, ∑ i, ∑ j, c i j * F i j x = ∑ i, ∑ j, c i j * ∫ x, F i j x := by
    intro F hF
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hF i j).const_mul _))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => (hF i j).const_mul _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
  simp only [Measure.restrict_univ]
  simp_rw [hL, hR]
  rw [hsum (fun i j x => φ x * rawGradient (D x) i j) hA,
    hsum (fun i j x => fderiv ℝ φ x (EuclideanSpace.single j 1) * WithLp.ofLp (u x) i) hB]
  simp_rw [hcomp]
  simp [Finset.sum_neg_distrib]

/-! ### The momentum, incompressibility and energy identities -/

/-- The momentum integrand of the Euclidean formulation. -/
def natMom (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (p : ℝ³ × ℝ → ℝ)
    (f : ℝ³ × ℝ → ℝ³) (φ : ℝ³ × ℝ → ℝ³) (z : ℝ³ × ℝ) : ℝ :=
  ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ
    + p z * divₓ φ z + ⟪f z, φ z⟫_ℝ

/-- The momentum integrand of the coordinate formulation. -/
def rawMom (u : RawSpace × ℝ → RawSpace) (Du : RawSpace × ℝ → Fin 3 → RawSpace)
    (p : RawSpace × ℝ → ℝ) (f : RawSpace × ℝ → RawSpace) (φ : RawSpace × ℝ → RawSpace)
    (z : RawSpace × ℝ) : ℝ :=
  (-(∑ i, u z i * CKN.timePartial (fun w => φ w i) z))
    - ∑ i, ∑ j, u z i * u z j * CKN.spatialPartial (fun w => φ w i) j z
    + ∑ i, ∑ j, Du z i j * CKN.spatialPartial (fun w => φ w i) j z
    - p z * ∑ i, CKN.spatialPartial (fun w => φ w i) i z
    - ∑ i, f z i * φ z i

theorem natMom_pushVector (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³)
    (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z : RawSpace × ℝ) :
    natMom u Du p f (pushVector φ) (rawSpaceTimeToEuclidean z) =
      -rawMom (pullVelocity u) (pullGradient Du) (pullScalar p) (pullVelocity f) φ z := by
  have h := momentum_integrand_transport φ hφ z (pullVelocity u z) (pullVelocity f z)
    (pullScalar p z) (Du (rawSpaceTimeToEuclidean z))
  simpa [natMom, rawMom, pullGradient, pullScalar, CKN.timePartial, CKN.spatialPartial] using h

theorem div_pushVector (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : RawSpace × ℝ) :
    divₓ (pushVector φ) (rawSpaceTimeToEuclidean z) =
      ∑ i, CKN.spatialPartial (fun w => φ w i) i z := by
  change LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap
    (fderiv ℝ (fun x : ℝ³ ↦ pushVector φ (x, (rawSpaceTimeToEuclidean z).2))
      (rawSpaceTimeToEuclidean z).1)) = _
  rw [trace_eq_sum_rawGradient_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  rw [rawSpaceTimeToEuclidean_fst, rawSpaceTimeToEuclidean_snd,
    rawGradient_pushVector φ hφ z i i]
  rfl

theorem div_iff_pushVector (φ : RawSpace × ℝ → RawSpace) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∀ z : RawSpace × ℝ, ∑ i, CKN.spatialPartial (fun w => φ w i) i z = 0) ↔
      ∀ z : ℝ³ × ℝ, divₓ (pushVector φ) z = 0 := by
  constructor
  · intro h z
    obtain ⟨z', rfl⟩ := rawSpaceTimeToEuclidean.surjective z
    rw [div_pushVector φ hφ]
    exact h z'
  · intro h z
    rw [← div_pushVector φ hφ]
    exact h _

theorem pushVector_testFunction_univ {I : Set ℝ} {φ : RawSpace × ℝ → RawSpace}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I) :
    pushVector φ ∈ testFunctions ℝ³ (Set.univ ×ˢ I) := by
  have h := pushVector_testFunction (Ω := (Set.univ : Set ℝ³)) (I := I)
    (by rwa [rawSpace_univ])
  exact h

theorem pullVelocity_testFunction_univ {I : Set ℝ} {φ : ℝ³ × ℝ → ℝ³}
    (hφ : φ ∈ testFunctions ℝ³ (Set.univ ×ˢ I)) :
    pullVelocity φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I := by
  have h := pullVelocity_testFunction hφ
  rwa [rawSpace_univ] at h

theorem pushScalar_testFunction_univ {I : Set ℝ} {ψ : RawSpace × ℝ → ℝ}
    (hψ : ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ I) :
    pushScalar ψ ∈ testFunctions ℝ (Set.univ ×ˢ I) := by
  have h := pushScalar_testFunction (Ω := (Set.univ : Set ℝ³)) (I := I)
    (by rwa [rawSpace_univ])
  exact h

theorem pullScalar_testFunction_univ {I : Set ℝ} {ψ : ℝ³ × ℝ → ℝ}
    (hψ : ψ ∈ testFunctions ℝ (Set.univ ×ˢ I)) :
    pullScalar ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ I := by
  have h := pullScalar_testFunction hψ
  rwa [rawSpace_univ] at h

/-- The momentum identity against a class of test fields, in Euclidean and coordinate
form. -/
theorem momentum_iff (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³)
    (P : (ℝ³ × ℝ → ℝ³) → Prop) (Q : (RawSpace × ℝ → RawSpace) → Prop)
    (hPQ : ∀ φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I,
      (Q φ ↔ P (pushVector φ))) :
    (∀ φ ∈ testFunctions ℝ³ (Set.univ ×ˢ I), P φ →
      ∫ z in Set.univ ×ˢ I, natMom u Du p f φ z = 0) ↔
    (∀ φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I, Q φ →
      ∫ z in Set.univ ×ˢ I,
        rawMom (pullVelocity u) (pullGradient Du) (pullScalar p) (pullVelocity f) φ z = 0) := by
  have hint : ∀ φ : RawSpace × ℝ → RawSpace, ContDiff ℝ (⊤ : ℕ∞) φ →
      ∫ z in Set.univ ×ˢ I, natMom u Du p f (pushVector φ) z =
        -∫ z in Set.univ ×ˢ I,
          rawMom (pullVelocity u) (pullGradient Du) (pullScalar p) (pullVelocity f) φ z := by
    intro φ hφ
    have hE := integral_euclid Set.univ I (natMom u Du p f (pushVector φ))
    rw [euclideanSpace_univ] at hE
    rw [hE, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    exact natMom_pushVector u Du p f φ hφ z
  constructor
  · intro h φ hφ hQ
    have := h (pushVector φ) (pushVector_testFunction_univ hφ) ((hPQ φ hφ).mp hQ)
    rw [hint φ hφ.1] at this
    linarith only [this]
  · intro h φ' hφ' hP
    have hφ := pullVelocity_testFunction_univ hφ'
    have hQ : Q (pullVelocity φ') := by
      rw [hPQ _ hφ, pushVector_pullVelocity]
      exact hP
    have := h _ hφ hQ
    have h2 := hint (pullVelocity φ') hφ.1
    rw [pushVector_pullVelocity] at h2
    rw [h2, this]
    simp

/-- Incompressibility against scalar space-time tests, coordinate to Euclidean. -/
theorem incompressible_native_of_raw (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³)
    (h : ∀ ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ I,
      ∫ z in CKN.spaceTimeSet Set.univ I,
        ∑ i, pullVelocity u z i * CKN.spatialPartial ψ i z = 0) :
    ∀ ψ ∈ testFunctions ℝ (Set.univ ×ˢ I), ∫ z in Set.univ ×ˢ I, ⟪u z, ∇ₓ ψ z⟫_ℝ = 0 := by
  intro ψ' hψ'
  have hψ := pullScalar_testFunction_univ hψ'
  have hraw := h _ hψ
  have hE := integral_euclid Set.univ I (fun z : ℝ³ × ℝ => ⟪u z, ∇ₓ ψ' z⟫_ℝ)
  rw [euclideanSpace_univ] at hE
  rw [hE]
  rw [← hraw]
  apply integral_congr_ae
  filter_upwards with z
  have hi := inner_pushScalar_gradient (pullScalar ψ') hψ.1 z (pullVelocity u z)
  rw [rawToEuclidean_pullVelocity, pushScalar_pullScalar] at hi
  simpa [rawSpaceTimeToEuclidean, rawSpaceTimeLinear, CKN.spatialPartial] using hi

/-- The energy integrand of the Euclidean formulation. -/
def natEnergyR (u : ℝ³ × ℝ → ℝ³) (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³)
    (ψ : ℝ³ × ℝ → ℝ) (z : ℝ³ × ℝ) : ℝ :=
  ‖u z‖ ^ 2 * (∂ₜ ψ z + Δₓ ψ z) + (‖u z‖ ^ 2 + 2 * p z) * ⟪u z, ∇ₓ ψ z⟫_ℝ
    + 2 * ⟪f z, u z⟫_ℝ * ψ z

/-- The energy integrand of the coordinate formulation. -/
def rawEnergyR (u : RawSpace × ℝ → RawSpace) (p : RawSpace × ℝ → ℝ)
    (f : RawSpace × ℝ → RawSpace) (ψ : RawSpace × ℝ → ℝ) (z : RawSpace × ℝ) : ℝ :=
  (CKN.Foundation.Parabolic.vec3EuclideanNorm (u z)) ^ 2 *
      (CKN.timePartial ψ z + ∑ i, CKN.spatialSecondPartial ψ i i z)
    + ((CKN.Foundation.Parabolic.vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
        ∑ i, u z i * CKN.spatialPartial ψ i z
    + 2 * (∑ i, f z i * u z i) * ψ z

theorem natEnergyR_pushScalar (u : ℝ³ × ℝ → ℝ³) (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³)
    (ψ : RawSpace × ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : RawSpace × ℝ) :
    natEnergyR u p f (pushScalar ψ) (rawSpaceTimeToEuclidean z) =
      rawEnergyR (pullVelocity u) (pullScalar p) (pullVelocity f) ψ z := by
  have h := energy_integrand_transport ψ hψ z (pullVelocity u z) (pullVelocity f z)
    (pullScalar p z)
  simpa [natEnergyR, rawEnergyR, pullScalar, CKN.timePartial, CKN.spatialPartial,
    CKN.spatialSecondPartial] using h

/-- The local energy inequality, coordinate to Euclidean. -/
theorem energy_native_of_raw (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³)
    (h : ∀ ψ ∈ CKN.spaceTimeTestFunction (V := ℝ) Set.univ I, (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in CKN.spaceTimeSet Set.univ I,
          CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z * ψ z ≤
        ∫ z in CKN.spaceTimeSet Set.univ I,
          rawEnergyR (pullVelocity u) (pullScalar p) (pullVelocity f) ψ z) :
    ∀ ψ ∈ testFunctions ℝ (Set.univ ×ˢ I), (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in Set.univ ×ˢ I, ⟪Du z, Du z⟫ₕₛ * ψ z ≤
        ∫ z in Set.univ ×ˢ I, natEnergyR u p f ψ z := by
  intro ψ' hψ' hnonneg
  have hψ := pullScalar_testFunction_univ hψ'
  have hraw := h _ hψ (fun z => hnonneg _)
  have hE1 := integral_euclid Set.univ I (fun z : ℝ³ × ℝ => ⟪Du z, Du z⟫ₕₛ * ψ' z)
  have hE2 := integral_euclid Set.univ I (natEnergyR u p f ψ')
  rw [euclideanSpace_univ] at hE1 hE2
  rw [hE1, hE2]
  have hpush : pushScalar (pullScalar ψ') = ψ' := pushScalar_pullScalar ψ'
  refine le_of_eq_of_le ?_ (le_of_le_of_eq hraw ?_)
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    have h1 : ⟪Du (rawSpaceTimeToEuclidean z), Du (rawSpaceTimeToEuclidean z)⟫ₕₛ *
        ψ' (rawSpaceTimeToEuclidean z) =
        (∑ i, ∑ j, (rawGradient (Du (rawSpaceTimeToEuclidean z)) i j) ^ 2) * pullScalar ψ' z := by
      rw [rawGradient_sq]
      rfl
    exact h1
  · apply integral_congr_ae
    filter_upwards with z
    have := natEnergyR_pushScalar u p f (pullScalar ψ') hψ.1 z
    rw [hpush] at this
    exact this.symm

/-! ### The energy space `J` -/

theorem rawToEuclidean_homeomorph_measurePreserving :
    MeasurePreserving (⇑rawToEuclidean.toHomeomorph) (volume : Measure RawSpace)
      (volume : Measure ℝ³) := rawToEuclidean_measurePreserving

theorem eLpNorm_volume_comp (b : ℝ³ → ℝ³) :
    eLpNorm b 2 volume = eLpNorm (fun x : RawSpace => b (rawToEuclidean x)) 2 volume := by
  have h := rawToEuclidean.toHomeomorph.measurableEmbedding.eLpNorm_map_measure
    (μ := (volume : Measure RawSpace)) (g := b) (p := 2)
  rw [rawToEuclidean_homeomorph_measurePreserving.map_eq] at h
  exact h

theorem memLp_space_iff (a : ℝ³ → ℝ³) :
    MemLp a 2 volume ↔ MemLp (pullSpatial a) 2 (volume : Measure RawSpace) := by
  have h := rawToEuclidean.toHomeomorph.measurableEmbedding.memLp_map_measure_iff
    (μ := (volume : Measure RawSpace)) (g := a) (p := 2)
  rw [rawToEuclidean_homeomorph_measurePreserving.map_eq] at h
  rw [h]
  exact (memLp_clm_iff rawToEuclidean.symm (fun x => a (rawToEuclidean x)) 2).symm

theorem aesm_pullSpatial {b : ℝ³ → ℝ³} (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (fun x : RawSpace => b (rawToEuclidean x)) volume :=
  hb.comp_measurePreserving rawToEuclidean_measurePreserving

theorem eLpNorm_pull_le :
    ∃ c : ℝ≥0, ∀ b : ℝ³ → ℝ³, AEStronglyMeasurable b volume →
      eLpNorm (pullSpatial b) 2 volume ≤ c • eLpNorm b 2 volume := by
  refine ⟨‖(rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace)‖₊, fun b hb => ?_⟩
  rw [eLpNorm_volume_comp b]
  have hf : AEStronglyMeasurable (pullSpatial b) volume :=
    (aesm_clm_iff rawToEuclidean.symm (fun x => b (rawToEuclidean x))).mpr (aesm_pullSpatial hb)
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hf
  filter_upwards with x
  exact (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace).le_opNNNorm (b (rawToEuclidean x))

theorem eLpNorm_push_le :
    ∃ c : ℝ≥0, ∀ b : ℝ³ → ℝ³, AEStronglyMeasurable b volume →
      eLpNorm b 2 volume ≤ c • eLpNorm (pullSpatial b) 2 volume := by
  refine ⟨‖(rawToEuclidean : RawSpace →L[ℝ] ℝ³)‖₊, fun b hb => ?_⟩
  rw [eLpNorm_volume_comp b]
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (aesm_pullSpatial hb)
  filter_upwards with x
  have := (rawToEuclidean : RawSpace →L[ℝ] ℝ³).le_opNNNorm (pullSpatial b x)
  simpa [pullSpatial] using this

theorem tendsto_eLpNorm_iff (aS : ℕ → ℝ³ → ℝ³) (a : ℝ³ → ℝ³)
    (haS : ∀ k, AEStronglyMeasurable (aS k) volume) (ha : AEStronglyMeasurable a volume) :
    Tendsto (fun k => eLpNorm (fun x => aS k x - a x) 2 volume) atTop (nhds 0) ↔
      Tendsto (fun k => eLpNorm (fun x => pullSpatial (aS k) x - pullSpatial a x) 2 volume)
        atTop (nhds 0) := by
  have hsub : ∀ k, (fun x => pullSpatial (aS k) x - pullSpatial a x) =
      pullSpatial (fun x => aS k x - a x) := by
    intro k
    funext x
    simp [pullSpatial]
  simp_rw [hsub]
  obtain ⟨c₁, h₁⟩ := eLpNorm_pull_le
  obtain ⟨c₂, h₂⟩ := eLpNorm_push_le
  have hscale : ∀ (c : ℝ≥0) {g : ℕ → ℝ≥0∞}, Tendsto g atTop (nhds 0) →
      Tendsto (fun k => c • g k) atTop (nhds 0) := by
    intro c g hg
    have := ENNReal.Tendsto.const_mul hg (Or.inr (ENNReal.coe_ne_top : (c : ℝ≥0∞) ≠ ∞))
    simpa [ENNReal.smul_def] using this
  constructor
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hscale c₁ h)
      (fun k => bot_le) (fun k => h₁ _ ((haS k).sub ha))
  · intro h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hscale c₂ h)
      (fun k => bot_le) (fun k => h₂ _ ((haS k).sub ha))

theorem contDiff_pullSpatial {b : ℝ³ → ℝ³} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (pullSpatial b) :=
  rawToEuclidean.symm.contDiff.comp (hb.comp rawToEuclidean.contDiff)

theorem contDiff_pushSpatial {b : RawSpace → RawSpace} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    ContDiff ℝ (⊤ : ℕ∞) (pushSpatial b) :=
  rawToEuclidean.contDiff.comp (hb.comp rawToEuclidean.symm.contDiff)

theorem hasCompactSupport_pullSpatial {b : ℝ³ → ℝ³} (hb : HasCompactSupport b) :
    HasCompactSupport (pullSpatial b) :=
  (hb.comp_homeomorph rawToEuclidean.toHomeomorph).comp_left
    (g := rawToEuclidean.symm) (by simp)

theorem hasCompactSupport_pushSpatial {b : RawSpace → RawSpace} (hb : HasCompactSupport b) :
    HasCompactSupport (pushSpatial b) :=
  (hb.comp_homeomorph rawToEuclidean.symm.toHomeomorph).comp_left
    (g := rawToEuclidean) (by simp)

theorem trace_fderiv_eq (b : ℝ³ → ℝ³) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (x : RawSpace) :
    LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.toLinearMap (fderiv ℝ b (rawToEuclidean x))) =
      ∑ i, CKN.spatialDeriv (fun y => pullSpatial b y i) i x := by
  rw [trace_eq_sum_rawGradient_diagonal]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun w : RawSpace × ℝ => pullSpatial b w.1) :=
    (contDiff_pullSpatial hb).comp contDiff_fst
  have hfun : (fun x' : ℝ³ => pushVector (fun w : RawSpace × ℝ => pullSpatial b w.1)
      (x', (0 : ℝ))) = b := by
    funext x'
    simp [pushVector, pullSpatial, rawSpaceTimeToEuclidean_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h := rawGradient_pushVector (fun w : RawSpace × ℝ => pullSpatial b w.1) hφ (x, 0) i i
  dsimp only at h
  simp only [hfun] at h
  simpa [CKN.spatialDeriv] using h

theorem isInJ_iff (a : ℝ³ → ℝ³) : IsInJ a ↔ CKN.IsInJ (pullSpatial a) := by
  constructor
  · rintro ⟨hmem, aS, hdiff, hcompact, hdiv, htend⟩
    refine ⟨(memLp_space_iff a).mp hmem, fun k => pullSpatial (aS k),
      fun k => contDiff_pullSpatial (hdiff k),
      fun k => hasCompactSupport_pullSpatial (hcompact k), ?_,
      (tendsto_eLpNorm_iff aS a (fun k => (hdiff k).continuous.aestronglyMeasurable)
        hmem.aestronglyMeasurable).mp htend⟩
    intro k x
    rw [← trace_fderiv_eq (aS k) (hdiff k) x]
    exact hdiv k _
  · rintro ⟨hmem, aR, hdiff, hcompact, hdiv, htend⟩
    refine ⟨(memLp_space_iff a).mpr hmem, fun k => pushSpatial (aR k),
      fun k => contDiff_pushSpatial (hdiff k),
      fun k => hasCompactSupport_pushSpatial (hcompact k), ?_, ?_⟩
    · intro k x'
      obtain ⟨x, rfl⟩ := rawToEuclidean.surjective x'
      rw [trace_fderiv_eq _ (contDiff_pushSpatial (hdiff k)) x]
      simp only [pullSpatial_pushSpatial]
      exact hdiv k x
    · rw [tendsto_eLpNorm_iff _ _
        (fun k => (contDiff_pushSpatial (hdiff k)).continuous.aestronglyMeasurable)
        ((memLp_space_iff a).mpr hmem).aestronglyMeasurable]
      simpa [pullSpatial_pushSpatial] using htend

/-! ### Slices, energy class and initial trace -/

theorem memLp_two_iff_lintegral {α V : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup V] (F : α → V) :
    MemLp F 2 μ ↔ AEStronglyMeasurable F μ ∧ ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ∞ := by
  constructor
  · intro h
    refine ⟨h.aestronglyMeasurable, ?_⟩
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) h
  · rintro ⟨h1, h2⟩
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) h1).mpr
      (by simpa using h2)

/-- The matrix-to-operator equivalence. -/
def matEquiv : (Fin 3 → RawSpace) ≃L[ℝ] (ℝ³ →L[ℝ] ℝ³) :=
  ContinuousLinearEquiv.equivOfInverse
    (LinearMap.toContinuousLinearMap
      { toFun := matCLM
        map_add' := by
          intro M N
          ext v i
          simp [matCLM_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro c M
          ext v i
          simp [matCLM_apply, Finset.mul_sum, mul_assoc] })
    rawGradientCLM
    (fun M => rawGradient_matCLM M)
    (fun D => matCLM_rawGradient D)

theorem matEquiv_apply (M : Fin 3 → RawSpace) : matEquiv M = matCLM M := rfl

theorem memLp_vec_iff (U : Set RawSpace) (J : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (p : ℝ≥0∞) :
    MemLp u p (volume.restrict (euclideanSpace U ×ˢ J)) ↔
      MemLp (pullVelocity u) p (volume.restrict (U ×ˢ J)) := by
  rw [memLp_euclid_iff U J u p, ← memLp_clm_iff rawToEuclidean (pullVelocity u) p]
  simp only [rawSpaceTimeToEuclidean_apply, rawToEuclidean_pullVelocity]

theorem memLp_mat_iff (U : Set RawSpace) (J : Set ℝ) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ≥0∞) :
    MemLp Du p (volume.restrict (euclideanSpace U ×ˢ J)) ↔
      MemLp (pullGradient Du) p (volume.restrict (U ×ˢ J)) := by
  rw [memLp_euclid_iff U J Du p, ← memLp_clm_iff matEquiv (pullGradient Du) p]
  have : (fun z : RawSpace × ℝ => matEquiv (pullGradient Du z)) =
      fun z => Du (rawSpaceTimeToEuclidean z) := by
    funext z
    simp [matEquiv_apply, pullGradient, matCLM_rawGradient]
  rw [this]

theorem class_iff (U : Set RawSpace) (J : Set ℝ) (u : ℝ³ × ℝ → ℝ³)
    (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    (MemLp u 2 (volume.restrict (euclideanSpace U ×ˢ J)) ∧
        MemLp Du 2 (volume.restrict (euclideanSpace U ×ˢ J))) ↔
      (AEStronglyMeasurable (pullVelocity u) (volume.restrict (U ×ˢ J)) ∧
        AEStronglyMeasurable (pullGradient Du) (volume.restrict (U ×ˢ J)) ∧
        ∫⁻ z in U ×ˢ J, ‖pullVelocity u z‖ₑ ^ (2 : ℝ) + ‖pullGradient Du z‖ₑ ^ (2 : ℝ)
          < ∞) := by
  rw [memLp_vec_iff U J u 2, memLp_mat_iff U J Du 2, memLp_two_iff_lintegral,
    memLp_two_iff_lintegral]
  constructor
  · rintro ⟨⟨hu, hu'⟩, ⟨hD, hD'⟩⟩
    refine ⟨hu, hD, ?_⟩
    rw [lintegral_add_left' (hu.enorm.pow_const (2 : ℝ))]
    exact ENNReal.add_lt_top.mpr ⟨hu', hD'⟩
  · rintro ⟨hu, hD, hfin⟩
    rw [lintegral_add_left' (hu.enorm.pow_const (2 : ℝ))] at hfin
    exact ⟨⟨hu, (ENNReal.add_lt_top.mp hfin).1⟩, ⟨hD, (ENNReal.add_lt_top.mp hfin).2⟩⟩

theorem lh_class_iff (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    (MemLp u 2 (volume.restrict (Set.univ ×ˢ I)) ∧
        MemLp Du 2 (volume.restrict (Set.univ ×ˢ I))) ↔
      (AEStronglyMeasurable (pullVelocity u) (volume.restrict (Set.univ ×ˢ I)) ∧
        AEStronglyMeasurable (pullGradient Du) (volume.restrict (Set.univ ×ˢ I)) ∧
        ∫⁻ z in Set.univ ×ˢ I, ‖pullVelocity u z‖ₑ ^ (2 : ℝ) + ‖pullGradient Du z‖ₑ ^ (2 : ℝ)
          < ∞) := by
  have := class_iff Set.univ I u Du
  rwa [euclideanSpace_univ] at this

theorem lintegral_norm_sq_euclid (b : ℝ³ → ℝ³) (q : ℝ) :
    ∫⁻ x, ‖b x‖ₑ ^ q =
      ∫⁻ x : RawSpace,
        ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpatial b x)) ^ q := by
  rw [lintegral_euclid_space]
  apply lintegral_congr
  intro x
  unfold pullSpatial
  rw [vec3EuclideanNorm_rawToEuclidean_symm, ofReal_norm]

theorem pullSpatial_slice (u : ℝ³ × ℝ → ℝ³) (t : ℝ) :
    pullSpatial (fun x => u (x, t)) = fun x => pullVelocity u (x, t) := by
  funext x
  simp [pullSpatial, pullVelocity]

theorem essSup_slice_iff (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) :
    essSup (fun s : ℝ => ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict I) < ∞ ↔
      essSup (fun s : ℝ => ∫⁻ x : RawSpace, ‖pullVelocity u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict I) < ∞ := by
  obtain ⟨c₁, hc₁, h₁⟩ := lintegral_enorm_sq_clm_le (μ := (volume : Measure RawSpace))
    (rawToEuclidean : RawSpace →L[ℝ] ℝ³)
  obtain ⟨c₂, hc₂, h₂⟩ := lintegral_enorm_sq_clm_le (μ := (volume : Measure RawSpace))
    (rawToEuclidean.symm : ℝ³ →L[ℝ] RawSpace)
  have hnat : ∀ s, ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ) =
      ∫⁻ x : RawSpace, ‖rawToEuclidean (pullVelocity u (x, s))‖ₑ ^ (2 : ℝ) := by
    intro s
    rw [lintegral_euclid_space]
    simp
  have hraw : ∀ s, ∫⁻ x : RawSpace, ‖pullVelocity u (x, s)‖ₑ ^ (2 : ℝ) =
      ∫⁻ x : RawSpace, ‖rawToEuclidean.symm (u (rawToEuclidean x, s))‖ₑ ^ (2 : ℝ) := by
    intro s
    simp [pullVelocity]
  have hnat' : ∀ s, ∫⁻ x : ℝ³, ‖u (x, s)‖ₑ ^ (2 : ℝ) =
      ∫⁻ x : RawSpace, ‖u (rawToEuclidean x, s)‖ₑ ^ (2 : ℝ) := by
    intro s
    exact lintegral_euclid_space _
  constructor
  · intro h
    refine essSup_lt_top_of_le hc₂ (fun s => ?_) h
    rw [hraw s, hnat' s]
    exact h₂ (fun x => u (rawToEuclidean x, s))
  · intro h
    refine essSup_lt_top_of_le hc₁ (fun s => ?_) h
    rw [hnat s]
    exact h₁ (fun x => pullVelocity u (x, s))

theorem inner_pushSpatialScalar_gradient (g : RawSpace → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x v : RawSpace) :
    ⟪rawToEuclidean v, gradient (pushSpatialScalar g) (rawToEuclidean x)⟫_ℝ =
      ∑ i, v i * fderiv ℝ g x (CKN.basisVec i) := by
  have h := inner_pushScalar_gradient (fun w : RawSpace × ℝ => g w.1)
    (hg.comp contDiff_fst) (x, 0) v
  have hfun : (fun x' : ℝ³ => pushScalar (fun w : RawSpace × ℝ => g w.1) (x', ((x, (0 : ℝ)).2))) =
      pushSpatialScalar g := by
    funext x'
    simp [pushScalar, pushSpatialScalar, rawSpaceTimeToEuclidean_symm_apply]
  dsimp only at h
  simp only [hfun] at h
  simpa using h

theorem div_slice_iff (s : ℝ) (u : ℝ³ × ℝ → ℝ³) :
    (∀ ψ ∈ testFunctions ℝ (Set.univ : Set ℝ³), ∫ x : ℝ³, ⟪u (x, s), ∇ ψ x⟫_ℝ = 0) ↔
      (∀ ψ : CKN.WeakTestFunction (Set.univ : Set RawSpace),
        ∫ x : RawSpace, ∑ i, pullVelocity u (x, s) i * ψ.partialDeriv i x = 0) := by
  constructor
  · intro h ψ
    have hψ : pushSpatialScalar ψ.toFun ∈ testFunctions ℝ (Set.univ : Set ℝ³) := by
      have := pushSpatialScalar_testFunction ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset
      rwa [euclideanSpace_univ] at this
    have h0 := h _ hψ
    rw [integral_euclid_space] at h0
    rw [← h0]
    apply integral_congr_ae
    filter_upwards with x
    have hi := inner_pushSpatialScalar_gradient ψ.toFun ψ.contDiff x (pullVelocity u (x, s))
    rw [show rawToEuclidean (pullVelocity u (x, s)) = u (rawToEuclidean x, s) by simp] at hi
    rw [show ∑ i, pullVelocity u (x, s) i * ψ.partialDeriv i x =
      ∑ i, pullVelocity u (x, s) i * fderiv ℝ ψ.toFun x (CKN.basisVec i) from rfl]
    exact hi.symm
  · intro h ψ hψ
    let ψR : CKN.WeakTestFunction (Set.univ : Set RawSpace) :=
      { toFun := pullSpatialScalar ψ
        contDiff := (pullSpatialScalar_testFunction hψ).1
        hasCompactSupport := (pullSpatialScalar_testFunction hψ).2
        tsupport_subset := Set.subset_univ _ }
    have h0 := h ψR
    rw [integral_euclid_space]
    rw [← h0]
    apply integral_congr_ae
    filter_upwards with x
    have hi := inner_pushSpatialScalar_gradient ψR.toFun ψR.contDiff x (pullVelocity u (x, s))
    rw [show rawToEuclidean (pullVelocity u (x, s)) = u (rawToEuclidean x, s) by simp] at hi
    have hpush : pushSpatialScalar ψR.toFun = ψ := pushSpatialScalar_pullSpatialScalar ψ
    rw [hpush] at hi
    rw [show ∑ i, pullVelocity u (x, s) i * ψR.partialDeriv i x =
      ∑ i, pullVelocity u (x, s) i * fderiv ℝ ψR.toFun x (CKN.basisVec i) from rfl]
    exact hi

theorem integral_pair_euclid (u : ℝ³ × ℝ → ℝ³) (t : ℝ) (w : ℝ³ → ℝ³) :
    ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ =
      ∫ x : RawSpace, ∑ i, pullVelocity u (x, t) i * pullSpatial w x i := by
  rw [integral_euclid_space]
  apply integral_congr_ae
  filter_upwards with x
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [pullVelocity, pullSpatial, rawToEuclidean, mul_comm]

theorem cont_iff (T : ℝ) (u : ℝ³ × ℝ → ℝ³) :
    (∀ w : ℝ³ → ℝ³, MemLp w 2 volume →
      ContinuousOn (fun t : ℝ => ∫ x : ℝ³, ⟪u (x, t), w x⟫_ℝ) (Icc 0 T)) ↔
      (∀ w : RawSpace → RawSpace, MemLp w (2 : ℝ≥0∞) volume →
        ContinuousOn (fun t : ℝ => ∫ x : RawSpace, ∑ i, pullVelocity u (x, t) i * w x i)
          (Icc 0 T)) := by
  constructor
  · intro h w hw
    have hwN : MemLp (pushSpatial w) 2 volume := by
      rw [memLp_space_iff, pullSpatial_pushSpatial]
      exact hw
    have := h _ hwN
    simp_rw [integral_pair_euclid, pullSpatial_pushSpatial] at this
    exact this
  · intro h w hw
    have := h (pullSpatial w) ((memLp_space_iff w).mp hw)
    simp_rw [integral_pair_euclid]
    exact this

theorem lintegral_slice_norm_iff (u : ℝ³ × ℝ → ℝ³) (a : ℝ³ → ℝ³) (t : ℝ) :
    ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ) =
      ∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (pullVelocity u (x, t) - pullSpatial a x)) ^ (2 : ℝ) := by
  have := lintegral_norm_sq_euclid (fun x => u (x, t) - a x) 2
  rw [this]
  apply lintegral_congr
  intro x
  simp [pullSpatial, pullVelocity]

theorem lintegral_slice_norm (u : ℝ³ × ℝ → ℝ³) (t : ℝ) :
    ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (2 : ℝ) =
      ∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (pullVelocity u (x, t))) ^ (2 : ℝ) := by
  have := lintegral_norm_sq_euclid (fun x => u (x, t)) 2
  rw [this, pullSpatial_slice]

theorem lintegral_dirichlet' (I : Set ℝ) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    ∫⁻ z in Set.univ ×ˢ I, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ =
      ∫⁻ z in Set.univ ×ˢ I,
        ENNReal.ofReal (∑ i, ∑ j, (pullGradient Du z i j) ^ 2) := by
  have hE := lintegral_euclid Set.univ I (fun z : ℝ³ × ℝ => ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ)
  rw [euclideanSpace_univ] at hE
  rw [hE]
  apply lintegral_congr
  intro z
  congr 1
  change _ = ∑ i, ∑ j, (rawGradient (Du (rawSpaceTimeToEuclidean z)) i j) ^ 2
  rw [rawGradient_sq]

/-! ### Leray--Hopf solutions: equivalence of the two formulations -/

theorem pullScalar_zero : pullScalar (0 : ℝ³ × ℝ → ℝ) = 0 := rfl

theorem pullVelocity_zero : pullVelocity (0 : ℝ³ × ℝ → ℝ³) = 0 := by
  funext z
  simp [pullVelocity]

theorem energy_lhs_eq (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (t₀ : ℝ) :
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ =
      ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
            (pullVelocity u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 t₀),
            ENNReal.ofReal (CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z) := by
  rw [lintegral_slice_norm, lintegral_dirichlet' (Ioo 0 t₀) Du, volume_slab_eq]
  rfl

theorem energy_rhs_eq (a : ℝ³ → ℝ³) :
    ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (1 / 2 : ℝ) *
        ∫⁻ x : RawSpace, ENNReal.ofReal
          (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpatial a x)) ^ (2 : ℝ) := by
  rw [lintegral_norm_sq_euclid a 2]

theorem natMom_unforced (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (φ : ℝ³ × ℝ → ℝ³) (z : ℝ³ × ℝ) :
    natMom u Du 0 0 φ z =
      ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ := by
  simp [natMom]

theorem natMom_forced (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (f φ : ℝ³ × ℝ → ℝ³) (z : ℝ³ × ℝ) :
    natMom u Du 0 f φ z =
      ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ + ⟪f z, φ z⟫_ℝ := by
  simp [natMom]

theorem natMom_pressure (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (φ : ℝ³ × ℝ → ℝ³) (z : ℝ³ × ℝ) :
    natMom u Du p 0 φ z =
      ⟪u z, ∂ₜ φ z⟫_ℝ + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ - ⟪Du z, Dₓ φ z⟫ₕₛ + p z * divₓ φ z := by
  simp [natMom]

theorem rawMom_unforced (u : RawSpace × ℝ → RawSpace) (Du : RawSpace × ℝ → Fin 3 → RawSpace)
    (φ : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    rawMom u Du 0 0 φ z =
      (-(∑ i, u z i * CKN.timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * CKN.spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, Du z i j * CKN.spatialPartial (fun w => φ w i) j z := by
  simp [rawMom]

theorem rawMom_forced (u : RawSpace × ℝ → RawSpace) (Du : RawSpace × ℝ → Fin 3 → RawSpace)
    (f φ : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    rawMom u Du 0 f φ z =
      (-(∑ i, u z i * CKN.timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * CKN.spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, Du z i j * CKN.spatialPartial (fun w => φ w i) j z
        - ∑ i, f z i * φ z i := by
  simp [rawMom]

theorem rawMom_pressure (u : RawSpace × ℝ → RawSpace) (Du : RawSpace × ℝ → Fin 3 → RawSpace)
    (p : RawSpace × ℝ → ℝ) (φ : RawSpace × ℝ → RawSpace) (z : RawSpace × ℝ) :
    rawMom u Du p 0 φ z =
      (-(∑ i, u z i * CKN.timePartial (fun w => φ w i) z))
        - ∑ i, ∑ j, u z i * u z j * CKN.spatialPartial (fun w => φ w i) j z
        + ∑ i, ∑ j, Du z i j * CKN.spatialPartial (fun w => φ w i) j z
        - p z * ∑ i, CKN.spatialPartial (fun w => φ w i) i z
        - ∑ i, ((0 : RawSpace × ℝ → RawSpace) z i) * φ z i := by
  simp [rawMom]

/-- The divergence-free momentum equation, Euclidean to coordinate form and back. -/
theorem momentum_div_iff (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³) :
    (∀ φ ∈ testFunctions ℝ³ (Set.univ ×ˢ I), (∀ z : ℝ³ × ℝ, divₓ φ z = 0) →
      ∫ z in Set.univ ×ˢ I, natMom u Du p f φ z = 0) ↔
    (∀ φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I,
      (∀ z : RawSpace × ℝ, ∑ i, CKN.spatialPartial (fun w => φ w i) i z = 0) →
      ∫ z in Set.univ ×ˢ I,
        rawMom (pullVelocity u) (pullGradient Du) (pullScalar p) (pullVelocity f) φ z = 0) :=
  momentum_iff I u Du p f (fun φ => ∀ z : ℝ³ × ℝ, divₓ φ z = 0)
    (fun φ => ∀ z : RawSpace × ℝ, ∑ i, CKN.spatialPartial (fun w => φ w i) i z = 0)
    (fun φ hφ => div_iff_pushVector φ hφ.1)

theorem momentum_all_iff (I : Set ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (p : ℝ³ × ℝ → ℝ) (f : ℝ³ × ℝ → ℝ³) :
    (∀ φ ∈ testFunctions ℝ³ (Set.univ ×ˢ I),
      ∫ z in Set.univ ×ˢ I, natMom u Du p f φ z = 0) ↔
    (∀ φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) Set.univ I,
      ∫ z in Set.univ ×ˢ I,
        rawMom (pullVelocity u) (pullGradient Du) (pullScalar p) (pullVelocity f) φ z = 0) := by
  have h := momentum_iff I u Du p f (fun _ => True) (fun _ => True) (fun φ hφ => Iff.rfl)
  simpa using h

theorem lh_iff (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
    (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    IsLerayHopfSolution T a u Du ↔
      CKN.IsLerayHopfSolution T (pullSpatial a) (pullVelocity u) (pullGradient Du) := by
  unfold IsLerayHopfSolution CKN.IsLerayHopfSolution
  simp only [volume_slab_eq]
  have hclass := lh_class_iff (Ioo 0 T) u Du
  have hmom := momentum_div_iff (Ioo 0 T) u Du 0 0
  simp only [pullScalar_zero, pullVelocity_zero, natMom_unforced, rawMom_unforced] at hmom
  have hen : ∀ t₀ : ℝ,
      (ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ ≤
      ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ)) ↔
      (ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
            (pullVelocity u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀,
            ENNReal.ofReal (CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z) ≤
      ENNReal.ofReal (1 / 2 : ℝ) *
        ∫⁻ x : RawSpace, ENNReal.ofReal
          (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpatial a x)) ^ (2 : ℝ)) := by
    intro t₀
    rw [energy_lhs_eq u Du t₀, energy_rhs_eq a, volume_slab_eq]
    rfl
  have hten : (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ)) =
      fun t : ℝ => ∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (pullVelocity u (x, t) - pullSpatial a x)) ^ (2 : ℝ) :=
    funext (lintegral_slice_norm_iff u a)
  rw [hten]
  constructor
  · rintro ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩
    obtain ⟨hA1, hA2, hA3⟩ := hclass.mp ⟨n4, n5⟩
    refine ⟨n1, (isInJ_iff a).mp n2, hA1, hA2, (essSup_slice_iff _ u).mp n3, hA3, ?_, ?_,
      (cont_iff T u).mp n8, ?_, ?_, n11⟩
    · filter_upwards [n6] with s hs
      intro i
      have := weakGradient_transport (U := Set.univ) (by rwa [euclideanSpace_univ]) i
      exact this
    · filter_upwards [n7] with s hs
      exact (div_slice_iff s u).mp hs
    · exact hmom.mp n9
    · intro t₀ ht₀
      exact (hen t₀).mp (n10 t₀ ht₀)
  · rintro ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩
    obtain ⟨n4, n5⟩ := hclass.mpr ⟨r3, r4, r6⟩
    refine ⟨r1, (isInJ_iff a).mpr r2, (essSup_slice_iff _ u).mpr r5, n4, n5, ?_, ?_,
      (cont_iff T u).mpr r9, hmom.mpr r10, ?_, r12⟩
    · filter_upwards [r7, slice_memLp_two (Ioo 0 T) u n4, slice_memLp_two (Ioo 0 T) Du n5]
        with s hs hu hD
      exact hasWeakDerivativeOn_univ_of_raw hu hD (fun i => hs i)
    · filter_upwards [r8] with s hs
      exact (div_slice_iff s u).mpr hs
    · intro t₀ ht₀
      exact (hen t₀).mpr (r11 t₀ ht₀)

/-! ### Forced Leray--Hopf solutions and force classes -/

theorem work_eq (I : Set ℝ) (f u : ℝ³ × ℝ → ℝ³) :
    ∫ z in Set.univ ×ˢ I, ⟪f z, u z⟫_ℝ =
      ∫ z in Set.univ ×ˢ I, ∑ i, pullVelocity f z i * pullVelocity u z i := by
  have hE := integral_euclid Set.univ I (fun z : ℝ³ × ℝ => ⟪f z, u z⟫_ℝ)
  rw [euclideanSpace_univ] at hE
  rw [hE]
  apply integral_congr_ae
  filter_upwards with z
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [pullVelocity, rawToEuclidean, mul_comm]

theorem locallySquare_iff (f : ℝ³ × ℝ → ℝ³) :
    IsLocallySquareIntegrableForce f ↔ CKN.IsLocallySquareIntegrableForce (pullVelocity f) := by
  unfold IsLocallySquareIntegrableForce CKN.IsLocallySquareIntegrableForce
  simp only [volume_slab_eq]
  refine forall_congr' fun T => forall_congr' fun hT => ?_
  have := memLp_vec_iff Set.univ (Ioo 0 T) f 2
  rwa [euclideanSpace_univ] at this

theorem rawBox_of_nativeBox {I : Set ℝ} {U : Set ℝ³} {J : Set ℝ} (hU : IsOpen U)
    (hUc : U ⋐ (Set.univ : Set ℝ³)) (hJ : OrdConnected J) (hJc : J ⋐ I) :
    CKN.localBox (Set.univ : Set RawSpace) I (rawSpace U) J := by
  refine ⟨hU.preimage rawToEuclidean.continuous, ?_, Set.subset_univ _, hJ, hJc.1, hJc.2⟩
  have h : rawToEuclidean.toHomeomorph ⁻¹' closure U =
      closure (rawToEuclidean.toHomeomorph ⁻¹' U) :=
    rawToEuclidean.toHomeomorph.preimage_closure U
  have hc : IsCompact (rawToEuclidean.toHomeomorph ⁻¹' closure U) :=
    rawToEuclidean.toHomeomorph.isCompact_preimage.mpr hUc.1
  rw [h] at hc
  exact hc

theorem nativeBox_of_rawBox {I : Set ℝ} {Ω' : Set RawSpace} {J : Set ℝ}
    (h : CKN.localBox (Set.univ : Set RawSpace) I Ω' J) :
    IsOpen (euclideanSpace Ω') ∧ euclideanSpace Ω' ⋐ (Set.univ : Set ℝ³) ∧ OrdConnected J ∧
      J ⋐ I := by
  rcases h with ⟨hUopen, hUcompact, -, hJconn, hJcompact, hJI⟩
  refine ⟨rawToEuclidean.toHomeomorph.isOpenMap Ω' hUopen, ⟨?_, Set.subset_univ _⟩,
    hJconn, hJcompact, hJI⟩
  change IsCompact (closure (rawToEuclidean '' Ω'))
  have hclosure : closure (rawToEuclidean '' Ω') = rawToEuclidean '' closure Ω' :=
    (rawToEuclidean.toHomeomorph.image_closure Ω').symm
  rw [hclosure]
  exact hUcompact.image rawToEuclidean.continuous

theorem locallyQ_iff_of_native (q : ℝ≥0) (f : ℝ³ × ℝ → ℝ³)
    (h : IsLocallyQIntegrableForce q f) :
    CKN.IsLocallyQIntegrableForce (q : ℝ) (pullVelocity f) := by
  intro Ω' J hbox i
  obtain ⟨hU, hUc, hJ, hJc⟩ := nativeBox_of_rawBox hbox
  have hmem := h _ J ⟨hU, hUc, hJ, hJc⟩
  have h2 := (memLp_vec_iff Ω' J f (q : ℝ≥0∞)).mp hmem
  have h3 := memLp_pi_iff.mp h2 i
  unfold CKN.localLp CKN.spaceTimeSet
  rw [volume_rawPoint_eq_product, ENNReal.ofReal_coe_nnreal]
  exact h3

theorem forced_iff (T : ℝ) (a : ℝ³ → ℝ³) (f : ℝ³ × ℝ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
    (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) :
    IsForcedLerayHopfSolution T a f u Du ↔
      CKN.IsForcedLerayHopfSolution T (pullSpatial a) (pullVelocity f) (pullVelocity u)
        (pullGradient Du) := by
  unfold IsForcedLerayHopfSolution CKN.IsForcedLerayHopfSolution
  simp only [volume_slab_eq]
  have hclass := lh_class_iff (Ioo 0 T) u Du
  have hmom := momentum_div_iff (Ioo 0 T) u Du 0 f
  simp only [pullScalar_zero, natMom_forced, rawMom_forced] at hmom
  have hf : MemLp f 2 (volume.restrict (Set.univ ×ˢ Ioo 0 T)) ↔
      MemLp (pullVelocity f) (2 : ℝ≥0∞) (volume.restrict (Set.univ ×ˢ Ioo 0 T)) := by
    have := memLp_vec_iff Set.univ (Ioo 0 T) f 2
    rwa [euclideanSpace_univ] at this
  have hen : ∀ t₀ : ℝ,
      ((ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ) < ∞ ∧
      (ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x : ℝ³, ‖u (x, t₀)‖ₑ ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀, ENNReal.ofReal ⟪Du z, Du z⟫ₕₛ).toReal ≤
        (ENNReal.ofReal (1 / 2 : ℝ) * ∫⁻ x : ℝ³, ‖a x‖ₑ ^ (2 : ℝ)).toReal
          + ∫ z in Set.univ ×ˢ Ioo 0 t₀, ⟪f z, u z⟫_ℝ) ↔
      ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
            (pullVelocity u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀,
            ENNReal.ofReal (CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z)) < ∞ ∧
      (ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
            (pullVelocity u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in Set.univ ×ˢ Ioo 0 t₀,
            ENNReal.ofReal (CKN.spatialGradientSq (pullVelocity u) (pullGradient Du) z)).toReal ≤
        (ENNReal.ofReal (1 / 2 : ℝ) *
          ∫⁻ x : RawSpace, ENNReal.ofReal
            (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullSpatial a x)) ^ (2 : ℝ)).toReal
          + ∫ z in Set.univ ×ˢ Ioo 0 t₀, ∑ i, pullVelocity f z i * pullVelocity u z i) := by
    intro t₀
    have e1 := energy_lhs_eq u Du t₀
    have e2 := energy_rhs_eq a
    rw [volume_slab_eq] at e1
    rw [e1, e2, work_eq]
    exact Iff.rfl
  have hten : (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t) - a x‖ₑ ^ (2 : ℝ)) =
      fun t : ℝ => ∫⁻ x : RawSpace, ENNReal.ofReal (CKN.Foundation.Parabolic.vec3EuclideanNorm
        (pullVelocity u (x, t) - pullSpatial a x)) ^ (2 : ℝ) :=
    funext (lintegral_slice_norm_iff u a)
  rw [hten]
  constructor
  · rintro ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩
    obtain ⟨hA1, hA2, hA3⟩ := hclass.mp ⟨n5, n6⟩
    refine ⟨n1, (isInJ_iff a).mp n2, hf.mp n3, hA1, hA2, (essSup_slice_iff _ u).mp n4, hA3,
      ?_, ?_, (cont_iff T u).mp n9, ?_, ?_, n12⟩
    · filter_upwards [n7] with s hs
      intro i
      have := weakGradient_transport (U := Set.univ) (by rwa [euclideanSpace_univ]) i
      exact this
    · filter_upwards [n8] with s hs
      exact (div_slice_iff s u).mp hs
    · exact hmom.mp n10
    · intro t₀ ht₀
      exact (hen t₀).mp (n11 t₀ ht₀)
  · rintro ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩
    obtain ⟨n5, n6⟩ := hclass.mpr ⟨r4, r5, r7⟩
    refine ⟨r1, (isInJ_iff a).mpr r2, hf.mpr r3, (essSup_slice_iff _ u).mpr r6, n5, n6, ?_, ?_,
      (cont_iff T u).mpr r10, hmom.mpr r11, ?_, r13⟩
    · filter_upwards [r8, slice_memLp_two (Ioo 0 T) u n5, slice_memLp_two (Ioo 0 T) Du n6]
        with s hs hu hD
      exact hasWeakDerivativeOn_univ_of_raw hu hD (fun i => hs i)
    · filter_upwards [r9] with s hs
      exact (div_slice_iff s u).mpr hs
    · intro t₀ ht₀
      exact (hen t₀).mpr (r12 t₀ ht₀)

/-! ### Suitable weak solutions from coordinate data -/

theorem timeBound_of_raw (U : Set RawSpace) (J : Set ℝ) (u : ℝ³ × ℝ → ℝ³)
    (h : essSup (fun s : ℝ => ∫⁻ x in U, ‖pullVelocity u (x, s)‖ₑ ^ (2 : ℝ))
      (volume.restrict J) < ∞)
    (hm : ∀ᵐ t ∂(volume.restrict J),
      AEStronglyMeasurable (fun x : ℝ³ => u (x, t)) (volume.restrict (euclideanSpace U))) :
    essSup (fun t : ℝ => eLpNorm (fun x : ℝ³ => u (x, t)) 2
      (volume.restrict (euclideanSpace U))) (volume.restrict J) < ∞ := by
  obtain ⟨c, hc, hle⟩ := lintegral_enorm_sq_clm_le (μ := (volume : Measure RawSpace).restrict U)
    (rawToEuclidean : RawSpace →L[ℝ] ℝ³)
  set A : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in U, ‖pullVelocity u (x, s)‖ₑ ^ (2 : ℝ) with hA
  set M := essSup A (volume.restrict J) with hM
  have hAM : ∀ᵐ t ∂(volume.restrict J), A t ≤ M := ENNReal.ae_le_essSup A
  have hbound : ∀ t, A t ≤ M → AEStronglyMeasurable (fun x : ℝ³ => u (x, t))
      (volume.restrict (euclideanSpace U)) →
      eLpNorm (fun x : ℝ³ => u (x, t)) 2 (volume.restrict (euclideanSpace U)) ≤
        (c * M) ^ (1 / 2 : ℝ) := by
    intro t ht hmt
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmt]
    simp only [ENNReal.toReal_ofNat]
    have h1 : ∫⁻ x in euclideanSpace U, ‖u (x, t)‖ₑ ^ (2 : ℝ) =
        ∫⁻ x in U, ‖u (rawToEuclidean x, t)‖ₑ ^ (2 : ℝ) :=
      ((rawToEuclidean_restrict_measurePreserving U).lintegral_comp_emb
        rawToEuclidean.toHomeomorph.measurableEmbedding
        (fun y => ‖u (y, t)‖ₑ ^ (2 : ℝ))).symm
    rw [h1]
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    calc ∫⁻ x in U, ‖u (rawToEuclidean x, t)‖ₑ ^ (2 : ℝ)
        = ∫⁻ x in U, ‖rawToEuclidean (pullVelocity u (x, t))‖ₑ ^ (2 : ℝ) := by simp
      _ ≤ c * ∫⁻ x in U, ‖pullVelocity u (x, t)‖ₑ ^ (2 : ℝ) := hle _
      _ ≤ c * M := by gcongr
  have := essSup_le_of_ae_le ((c * M) ^ (1 / 2 : ℝ)) ((hAM.and hm).mono fun t ht => hbound t ht.1 ht.2)
  exact lt_of_le_of_lt this
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hc h.ne))

theorem localWeakNSE_of_raw (q : ℝ≥0)
    (uR : RawSpace × ℝ → RawSpace) (DuR : RawSpace × ℝ → Fin 3 → RawSpace)
    (pR : RawSpace × ℝ → ℝ) (fR : RawSpace × ℝ → RawSpace)
    (hsuit : CKN.IsSuitableWeakSolution (Set.univ : Set RawSpace) (Ioi (0 : ℝ)) (q : ℝ)
      uR DuR pR fR)
    (hweak : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      HasWeakDerivativeOn (Set.univ : Set ℝ³) (fun x => pushVector uR (x, t))
        (fun x => pushGradient DuR (x, t))) :
    ∃ sol : LocalWeakNSESolution (Set.univ : Set ℝ³) (Ioi (0 : ℝ)) q,
      sol.u = pushVector uR ∧ sol.Dxu = pushGradient DuR ∧ sol.p = pushScalar pR ∧
        sol.f = pushVector fR := by
  obtain ⟨-, -, -, -, -, hreg, hdiv, hmom, hen⟩ := hsuit
  have huu : pullVelocity (pushVector uR) = uR := pullVelocity_pushVector uR
  have hDD : pullGradient (pushGradient DuR) = DuR := pullGradient_pushGradient DuR
  have hpp : pullScalar (pushScalar pR) = pR := pullScalar_pushScalar pR
  have hff : pullVelocity (pushVector fR) = fR := pullVelocity_pushVector fR
  refine ⟨{ isOpenSpace := isOpen_univ
            isOpenTime := isOpen_Ioi
            ordConnectedTime := ordConnected_Ioi
            u := pushVector uR
            Dxu := pushGradient DuR
            p := pushScalar pR
            f := pushVector fR
            weakDerivative := hweak
            energyRegularity := ?_
            equations := ?_
            energyInequality := ?_ }, rfl, rfl, rfl, rfl⟩
  · rintro U J ⟨hU, hUc, hJ, hJc⟩
    have hbox := rawBox_of_nativeBox hU hUc hJ hJc
    obtain ⟨hAu, hADu, -, -, hess, hfin, hMp, hMf, -⟩ := hreg _ _ hbox
    have hcls := (class_iff (rawSpace U) J (pushVector uR) (pushGradient DuR)).mpr (by
      rw [huu, hDD]
      refine ⟨hAu, hADu, ?_⟩
      unfold CKN.spaceTimeSet at hfin
      rw [volume_rawPoint_eq_product] at hfin
      exact hfin)
    rw [euclideanSpace_rawSpace] at hcls
    refine ⟨?_, hcls.1, hcls.2, ?_, ?_⟩
    · have hm : ∀ᵐ t ∂(volume.restrict J), AEStronglyMeasurable
          (fun x : ℝ³ => pushVector uR (x, t)) (volume.restrict (euclideanSpace (rawSpace U))) := by
        rw [euclideanSpace_rawSpace]
        have hmeas := hcls.1.aestronglyMeasurable
        have hprod : (volume : Measure (ℝ³ × ℝ)).restrict (U ×ˢ J) =
            (volume.restrict U).prod (volume.restrict J) := by
          rw [Measure.volume_eq_prod, Measure.prod_restrict]
        rw [hprod] at hmeas
        exact hmeas.prodMk_right
      have := timeBound_of_raw (rawSpace U) J (pushVector uR) (by rw [huu]; exact hess) hm
      rwa [euclideanSpace_rawSpace] at this
    · have h1 := (memLp_euclid_iff (rawSpace U) J (pushScalar pR) (3 / 2)).mpr (by
        have : (fun z : RawSpace × ℝ => pushScalar pR (rawSpaceTimeToEuclidean z)) = pR := by
          funext z
          simp
        rw [this]
        unfold CKN.spaceTimeSet at hMp
        rw [volume_rawPoint_eq_product, ofReal_three_halves] at hMp
        exact hMp)
      rwa [euclideanSpace_rawSpace] at h1
    · have h1 := (memLp_vec_iff (rawSpace U) J (pushVector fR) (q : ℝ≥0∞)).mpr (by
        rw [hff]
        unfold CKN.spaceTimeSet at hMf
        rw [volume_rawPoint_eq_product, ENNReal.ofReal_coe_nnreal] at hMf
        exact hMf)
      rwa [euclideanSpace_rawSpace] at h1
  · refine ⟨?_, ?_⟩
    · exact incompressible_native_of_raw (Ioi 0) (pushVector uR) (fun ψ hψ => by
        rw [huu]
        exact hdiv ψ hψ)
    · refine (momentum_all_iff (Ioi 0) (pushVector uR) (pushGradient DuR) (pushScalar pR)
        (pushVector fR)).mpr ?_
      intro φ hφ
      rw [huu, hDD, hpp, hff]
      have := hmom φ hφ
      simp only [volume_slab_eq] at this
      exact this
  · exact energy_native_of_raw (Ioi 0) (pushVector uR) (pushGradient DuR) (pushScalar pR)
      (pushVector fR) (fun ψ hψ hnn => by
        rw [huu, hDD, hpp, hff]
        exact hen ψ hψ hnn)

theorem ae_Ioi_of_Ioo {P : ℝ → Prop} (h : ∀ T : ℝ, 0 < T → ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), P s) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), P s := by
  have hU : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioo 0 ((n : ℝ) + 1) := by
    ext x
    simp only [mem_Ioi, mem_iUnion, mem_Ioo]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact ⟨n, hx, by linarith only [hn]⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  rw [hU, ae_restrict_iUnion_iff]
  intro n
  exact h _ (by positivity)

/-! ### The singular set and the theorems -/

theorem ofReal_five_thirds :
    ENNReal.ofReal (5 / 3 : ℝ) = (5 / 3 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem singularSet_null (uR : RawSpace × ℝ → RawSpace)
    (h : CKN.Foundation.Parabolic.parabolicHausdorffMeasure 1
      (CKN.SingularSet (Set.univ : Set RawSpace) (Ioi (0 : ℝ)) uR) = 0) :
    parabolicHausdorffMeasure 1
      (singularSet (Set.univ : Set ℝ³) (Ioi (0 : ℝ)) (pushVector uR)) = 0 := by
  let Sraw := CKN.SingularSet (Set.univ : Set RawSpace) (Ioi (0 : ℝ)) uR
  have hsubset : singularSet (Set.univ : Set ℝ³) (Ioi (0 : ℝ)) (pushVector uR) ⊆
      parabolicToEuclideanHomeomorph '' Sraw := by
    intro z hz
    let zRaw : RawPoint := (rawToEuclidean.symm z.1, z.2)
    have hzMap : parabolicToEuclideanHomeomorph zRaw = z := by
      change (rawToEuclidean (rawToEuclidean.symm z.1), z.2) = z
      rw [rawToEuclidean.apply_symm_apply]
    refine ⟨zRaw, ⟨⟨trivial, hz.1.2⟩, ?_⟩, hzMap⟩
    intro hregRaw
    have hreg : CKN.IsRegularPoint (rawSpace (Set.univ : Set ℝ³)) (Ioi (0 : ℝ))
        (pullVelocity (pushVector uR)) zRaw := by
      rw [rawSpace_univ, pullVelocity_pushVector]
      exact hregRaw
    have hregNew := isHolderRegularPoint_of_rawRegular hreg
    rw [hzMap] at hregNew
    exact hz.2 hregNew
  apply le_antisymm
  · calc
    parabolicHausdorffMeasure 1 (singularSet (Set.univ : Set ℝ³) (Ioi (0 : ℝ)) (pushVector uR))
        ≤ parabolicHausdorffMeasure 1 (parabolicToEuclideanHomeomorph '' Sraw) :=
      measure_mono hsubset
    _ = CKN.Foundation.Parabolic.parabolicHausdorffMeasure 1 Sraw :=
      parabolicHausdorffMeasure_one_image Sraw
    _ = 0 := h
  · exact bot_le

theorem globalLH_of_raw (a : ℝ³ → ℝ³) (uR : RawSpace × ℝ → RawSpace)
    (DuR : RawSpace × ℝ → Fin 3 → RawSpace)
    (h : CKN.IsGlobalLerayHopfSolution (pullSpatial a) uR DuR) :
    IsGlobalLerayHopfSolution a (pushVector uR) (pushGradient DuR) := by
  intro T hT
  rw [lh_iff, pullVelocity_pushVector, pullGradient_pushGradient]
  exact h T hT

theorem globalForced_of_raw (a : ℝ³ → ℝ³) (f : ℝ³ × ℝ → ℝ³) (uR : RawSpace × ℝ → RawSpace)
    (DuR : RawSpace × ℝ → Fin 3 → RawSpace)
    (h : CKN.IsGlobalForcedLerayHopfSolution (pullSpatial a) (pullVelocity f) uR DuR) :
    IsGlobalForcedLerayHopfSolution a f (pushVector uR) (pushGradient DuR) := by
  intro T hT
  rw [forced_iff, pullVelocity_pushVector, pullGradient_pushGradient]
  exact h T hT

/-! ## The theorems -/

/-- Leray's existence theorem `thm:leray`: every `a ∈ J` is the initial datum of
a global Leray--Hopf solution which, together with a pressure, is a suitable
weak solution (with zero force) on `ℝ³ × (0,∞)` for every `q > 5/2`. -/
theorem leray_existence :
    ∀ a : ℝ³ → ℝ³, IsInJ a →
      ∃ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (p : ℝ³ × ℝ → ℝ),
        IsGlobalLerayHopfSolution a u Du ∧
        ∀ q : ℝ≥0, 5 / 2 < q →
          ∃ sol : LocalWeakNSESolution (univ : Set ℝ³) (Ioi (0 : ℝ)) q,
            sol.u = u ∧ sol.Dxu = Du ∧ sol.p = p ∧ sol.f = 0 :=
  by
  intro a ha
  obtain ⟨uR, DuR, pR, hLH, hsuit⟩ :=
    CKN.leray_existence (pullSpatial a) ((isInJ_iff a).mp ha)
  have hLHn := globalLH_of_raw a uR DuR hLH
  refine ⟨pushVector uR, pushGradient DuR, pushScalar pR, hLHn, ?_⟩
  intro q hq
  have hweak : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      HasWeakDerivativeOn (Set.univ : Set ℝ³) (fun x => pushVector uR (x, t))
        (fun x => pushGradient DuR (x, t)) :=
    ae_Ioi_of_Ioo (fun T hT => (hLHn T hT).2.2.2.2.2.1)
  obtain ⟨sol, h1, h2, h3, h4⟩ := localWeakNSE_of_raw q uR DuR pR 0
    (hsuit q (by exact_mod_cast hq)) hweak
  refine ⟨sol, h1, h2, h3, ?_⟩
  rw [h4]
  funext z
  simp [pushVector]


/-- The Caffarelli--Kohn--Nirenberg conclusion `cor:ckn-headline` for the global
solution supplied by Leray's theorem: the singular set on `ℝ³ × (0,∞)` has zero
one-dimensional parabolic Hausdorff measure. -/
theorem leray_existence_singularSet :
    ∀ a : ℝ³ → ℝ³, IsInJ a →
      ∃ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsGlobalLerayHopfSolution a u Du ∧
        parabolicHausdorffMeasure 1
          (singularSet (univ : Set ℝ³) (Ioi (0 : ℝ)) u) = 0 :=
  by
  intro a ha
  obtain ⟨uR, DuR, hLH, hsing⟩ :=
    CKN.leray_existence_singularSet (pullSpatial a) ((isInJ_iff a).mp ha)
  exact ⟨pushVector uR, pushGradient DuR, globalLH_of_raw a uR DuR hLH,
    singularSet_null uR hsing⟩


/-- The forced existence theorem `thm:leray-forced`: for a force that is square
integrable on every finite slab and locally `L^{q₀}` for some `q₀ > 5/2`, one
forced global Leray--Hopf solution with one pressure is a suitable weak
solution for every admissible exponent `q > 5/2`. -/
theorem lerayExistenceForced :
    ∀ a : ℝ³ → ℝ³, IsInJ a →
    ∀ f : ℝ³ × ℝ → ℝ³,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ≥0, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (p : ℝ³ × ℝ → ℝ),
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        ∀ q : ℝ≥0, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          ∃ sol : LocalWeakNSESolution (univ : Set ℝ³) (Ioi (0 : ℝ)) q,
            sol.u = u ∧ sol.Dxu = Du ∧ sol.p = p ∧ sol.f = f :=
  by
  intro a ha f hsq hq₀
  obtain ⟨q₀, hq₀lt, hQ₀⟩ := hq₀
  obtain ⟨uR, DuR, pR, hLH, hsuit⟩ :=
    CKN.lerayExistenceForced (pullSpatial a) ((isInJ_iff a).mp ha) (pullVelocity f)
      ((locallySquare_iff f).mp hsq)
      ⟨q₀, by exact_mod_cast hq₀lt, locallyQ_iff_of_native q₀ f hQ₀⟩
  have hLHn := globalForced_of_raw a f uR DuR hLH
  refine ⟨pushVector uR, pushGradient DuR, pushScalar pR, hLHn, ?_⟩
  intro q hq hQ
  have hweak : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      HasWeakDerivativeOn (Set.univ : Set ℝ³) (fun x => pushVector uR (x, t))
        (fun x => pushGradient DuR (x, t)) :=
    ae_Ioi_of_Ioo (fun T hT => (hLHn T hT).2.2.2.2.2.2.1)
  obtain ⟨sol, h1, h2, h3, h4⟩ := localWeakNSE_of_raw q uR DuR pR (pullVelocity f)
    (hsuit q (by exact_mod_cast hq) (locallyQ_iff_of_native q f hQ)) hweak
  refine ⟨sol, h1, h2, h3, ?_⟩
  rw [h4, pushVector_pullVelocity]


/-- The same witness in `thm:leray-forced` has a singular set of zero
one-dimensional parabolic Hausdorff measure, as in
`thm:leray-forced-singularSet`. -/
theorem lerayExistenceForcedSingularSet :
    ∀ a : ℝ³ → ℝ³, IsInJ a →
    ∀ f : ℝ³ × ℝ → ℝ³,
      IsLocallySquareIntegrableForce f →
      (∃ q₀ : ℝ≥0, 5 / 2 < q₀ ∧ IsLocallyQIntegrableForce q₀ f) →
      ∃ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)) (p : ℝ³ × ℝ → ℝ),
        IsGlobalForcedLerayHopfSolution a f u Du ∧
        (∀ q : ℝ≥0, 5 / 2 < q → IsLocallyQIntegrableForce q f →
          ∃ sol : LocalWeakNSESolution (univ : Set ℝ³) (Ioi (0 : ℝ)) q,
            sol.u = u ∧ sol.Dxu = Du ∧ sol.p = p ∧ sol.f = f) ∧
        parabolicHausdorffMeasure 1
          (singularSet (univ : Set ℝ³) (Ioi (0 : ℝ)) u) = 0 :=
  by
  intro a ha f hsq hq₀
  obtain ⟨q₀, hq₀lt, hQ₀⟩ := hq₀
  obtain ⟨uR, DuR, pR, hLH, hsuit, hsing⟩ :=
    CKN.lerayExistenceForcedSingularSet (pullSpatial a) ((isInJ_iff a).mp ha) (pullVelocity f)
      ((locallySquare_iff f).mp hsq)
      ⟨q₀, by exact_mod_cast hq₀lt, locallyQ_iff_of_native q₀ f hQ₀⟩
  have hLHn := globalForced_of_raw a f uR DuR hLH
  refine ⟨pushVector uR, pushGradient DuR, pushScalar pR, hLHn, ?_, singularSet_null uR hsing⟩
  intro q hq hQ
  have hweak : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      HasWeakDerivativeOn (Set.univ : Set ℝ³) (fun x => pushVector uR (x, t))
        (fun x => pushGradient DuR (x, t)) :=
    ae_Ioi_of_Ioo (fun T hT => (hLHn T hT).2.2.2.2.2.2.1)
  obtain ⟨sol, h1, h2, h3, h4⟩ := localWeakNSE_of_raw q uR DuR pR (pullVelocity f)
    (hsuit q (by exact_mod_cast hq) (locallyQ_iff_of_native q f hQ)) hweak
  refine ⟨sol, h1, h2, h3, ?_⟩
  rw [h4, pushVector_pullVelocity]

theorem associatedPressure_aux (T : ℝ) (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³))
    (pR : RawSpace × ℝ → ℝ)
    (hp1 : MemLp pR (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (Set.univ ×ˢ Ioo 0 T)))
    (hp2 : ∀ φ ∈ CKN.spaceTimeTestFunction (V := RawSpace) (Set.univ : Set RawSpace) (Ioo 0 T),
      ∫ z in CKN.spaceTimeSet (Set.univ : Set RawSpace) (Ioo 0 T),
        (-(∑ i, pullVelocity u z i * CKN.timePartial (fun y => φ y i) z))
          - ∑ i, ∑ j, pullVelocity u z i * pullVelocity u z j *
              CKN.spatialPartial (fun y => φ y i) j z
          + ∑ i, ∑ j, pullGradient Du z i j * CKN.spatialPartial (fun y => φ y i) j z
          - pR z * ∑ i, CKN.spatialPartial (fun y => φ y i) i z
          - ∑ i, ((0 : RawSpace × ℝ → RawSpace) z i) * φ z i = 0)
    (hp3 : essSup
          (fun t : ℝ => ∫⁻ x : RawSpace, ENNReal.ofReal
            (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤ →
        essSup (fun t : ℝ => ∫⁻ x : RawSpace, ‖pR (x, t)‖ₑ ^ (3 / 2 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤) :
    ∃ p : ℝ³ × ℝ → ℝ,
        MemLp p (5 / 3) (volume.restrict (Set.univ ×ˢ Ioo 0 T)) ∧
        (∀ φ ∈ testFunctions ℝ³ (Set.univ ×ˢ Ioo 0 T),
          ∫ z in Set.univ ×ˢ Ioo 0 T, natMom u Du p 0 φ z = 0) ∧
        (essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
            (volume.restrict (Ioo 0 T)) < ∞ →
          essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
            (volume.restrict (Ioo 0 T)) < ∞) := by
  refine ⟨pushScalar pR, ?_, ?_, ?_⟩
  · have h1 := (memLp_euclid_iff Set.univ (Ioo 0 T) (pushScalar pR) (5 / 3)).mpr (by
      have : (fun z : RawSpace × ℝ => pushScalar pR (rawSpaceTimeToEuclidean z)) = pR := by
        funext z
        simp
      rw [this]
      rw [ofReal_five_thirds] at hp1
      exact hp1)
    rwa [euclideanSpace_univ] at h1
  · exact (momentum_all_iff (Ioo 0 T) u Du (pushScalar pR) 0).mpr (by
      intro φ' hφ'
      have := hp2 φ' hφ'
      simp only [volume_slab_eq] at this
      rw [pullScalar_pushScalar, pullVelocity_zero]
      exact this)
  · intro hfin
    have h1 : (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ)) =
        fun t : ℝ => ∫⁻ x : RawSpace, ENNReal.ofReal
          (CKN.Foundation.Parabolic.vec3EuclideanNorm (pullVelocity u (x, t))) ^ (3 : ℝ) := by
      funext t
      have := lintegral_norm_sq_euclid (fun x => u (x, t)) 3
      rwa [pullSpatial_slice] at this
    rw [h1] at hfin
    have h2 : (fun t : ℝ => ∫⁻ x : ℝ³, ‖pushScalar pR (x, t)‖ₑ ^ (3 / 2 : ℝ)) =
        fun t : ℝ => ∫⁻ x : RawSpace, ‖pR (x, t)‖ₑ ^ (3 / 2 : ℝ) := by
      funext t
      rw [lintegral_euclid_space]
      apply lintegral_congr
      intro x
      exact congrArg (fun y => ‖y‖ₑ ^ (3 / 2 : ℝ)) (pushScalar_rawCoordinates pR (x, t))
    rw [h2]
    exact hp3 hfin


/-- Every finite-time Leray--Hopf solution has an associated pressure in
`L^{5/3}(ℝ³ × (0,T))` solving the momentum equation against all test fields,
and it is in `L^∞_t L^{3/2}_x` when the velocity is in `L^∞_t L³_x`, as in
`thm:assoc-pressure`. -/
theorem associatedPressure :
    ∀ (T : ℝ) (a : ℝ³ → ℝ³) (u : ℝ³ × ℝ → ℝ³)
      (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
      IsLerayHopfSolution T a u Du →
      ∃ p : ℝ³ × ℝ → ℝ,
        MemLp p (5 / 3) (volume.restrict (univ ×ˢ Ioo 0 T)) ∧
        (∀ φ ∈ testFunctions ℝ³ (univ ×ˢ Ioo 0 T),
          ∫ z in univ ×ˢ Ioo 0 T,
            ⟪u z, ∂ₜ φ z⟫_ℝ
              + ⟪u z ⊗ᵣ u z, Dₓ φ z⟫ₕₛ
              - ⟪Du z, Dₓ φ z⟫ₕₛ
              + p z * divₓ φ z = 0) ∧
        (essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖u (x, t)‖ₑ ^ (3 : ℝ))
            (volume.restrict (Ioo 0 T)) < ∞ →
          essSup (fun t : ℝ => ∫⁻ x : ℝ³, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
            (volume.restrict (Ioo 0 T)) < ∞) :=
  by
  intro T a u Du h
  obtain ⟨pR, hp1, hp2, hp3⟩ :=
    CKN.associatedPressure T (pullSpatial a) (pullVelocity u) (pullGradient Du)
      ((lh_iff T a u Du).mp h)
  have hp1' : MemLp pR (ENNReal.ofReal (5 / 3 : ℝ)) (volume.restrict (Set.univ ×ˢ Ioo 0 T)) := by
    have := hp1
    simp only [volume_slab_eq] at this
    exact this
  obtain ⟨p, h1, h2, h3⟩ := associatedPressure_aux T u Du pR hp1' hp2 hp3
  refine ⟨p, h1, ?_, h3⟩
  intro φ hφ
  simpa only [natMom_pressure] using h2 φ hφ


end CKNLerayChallenge
