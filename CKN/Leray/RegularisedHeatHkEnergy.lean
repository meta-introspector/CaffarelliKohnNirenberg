-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.RegularisedOrderedDerivative
public import CKN.Leray.RegularisedOrderedDerivativeFrechet
public import CKN.Leray.RegularisedConvolutionSmooth
public import CKN.Leray.RegularisedTransportDivergence
public import CKN.Leray.RegularisedTransportCutoff
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import CKN.Leray.RegularisedInitialData
public import CKN.Foundation.Parabolic.Basic
public import CKN.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Diffusive Sobolev energy pairing

The whole-space integration-by-parts identity gives the dissipative term
for each ordered spatial derivative of the regularized equation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The classical spatial Laplacian on a scalar field, written as the sum
of its three coordinate second derivatives. -/
def regularisedScalarLaplacian (f : Vec3 → ℝ) : Vec3 → ℝ := fun x =>
  ∑ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ f y (CKN.basisVec i)) x
      (CKN.basisVec i)

end CKN.Leray

end
