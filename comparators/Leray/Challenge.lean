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

/-!
# Leray's existence theorem, the pressure of a Leray--Hopf solution

A standalone, Mathlib-only statement of the existence theorems `thm:leray`,
`cor:ckn-headline`, `thm:leray-forced`, `thm:leray-forced-singularSet` and of
`thm:assoc-pressure`. Space-time has Euclidean coordinates `ℝ³ × ℝ`; the
parabolic metric enters only where it is mathematically relevant (the
Hausdorff measure of the singular set).
-/

@[expose] public section

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
  by sorry

/-- The Caffarelli--Kohn--Nirenberg conclusion `cor:ckn-headline` for the global
solution supplied by Leray's theorem: the singular set on `ℝ³ × (0,∞)` has zero
one-dimensional parabolic Hausdorff measure. -/
theorem leray_existence_singularSet :
    ∀ a : ℝ³ → ℝ³, IsInJ a →
      ∃ (u : ℝ³ × ℝ → ℝ³) (Du : ℝ³ × ℝ → (ℝ³ →L[ℝ] ℝ³)),
        IsGlobalLerayHopfSolution a u Du ∧
        parabolicHausdorffMeasure 1
          (singularSet (univ : Set ℝ³) (Ioi (0 : ℝ)) u) = 0 :=
  by sorry

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
  by sorry

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
  by sorry

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
  by sorry

end CKNLerayChallenge
