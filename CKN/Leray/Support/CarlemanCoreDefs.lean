-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Statements.SpatialSecondPartial
public import CKN.Statements.TimePartial

/-!
# The conjugated heat operator and its commutator density

Scalar forms of the quantities used in the proofs of `prop:carleman-gauss` of the Escauriaza–Seregin–Šverák manuscript
and `prop:carleman-halfspace` of the Escauriaza–Seregin–Šverák manuscript. For a weight `φ` and a scalar field `v`,
`carlemanConj φ v` is `e^φ L (e^{-φ} v)` with `L = ∂ₜ + Δ`, written as
`∂ₜv + Δv - 2∇φ·∇v + (|∇φ|² - ∂ₜφ - Δφ) v`, and `carlemanCommutatorDensity φ v`
is the integrand of the commutator identity `eq:carleman-commutator` of the Escauriaza–Seregin–Šverák manuscript:
`4t²(φ_{ij} ∂ᵢv ∂ⱼv + φ_{ij} φᵢ φⱼ v²)
  + t² v² (∂ₜ²φ - 2∂ₜ|∇φ|² - Δ²φ) + t|∇v|² - t v² (|∇φ|² - ∂ₜφ)`.
Here `∂ₜ|∇φ|²` is written as `2 ∑ᵢ φᵢ ∂ₜφᵢ`.
-/

@[expose] public section

set_option autoImplicit false

open CKN
open CKN.Foundation.Parabolic

namespace CKN

/-- The squared spatial gradient `|∇f|²` of a scalar field. -/
noncomputable def scalarGradSq (f : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  ∑ i, spatialPartial f i z ^ 2

/-- The spatial Laplacian `Δf` of a scalar field. -/
noncomputable def scalarLaplacian (f : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  ∑ i, spatialSecondPartial f i i z

/-- The conjugated heat operator `e^φ (∂ₜ + Δ)(e^{-φ} v)` in expanded form. -/
noncomputable def carlemanConj (φ v : ParabolicPoint → ℝ) (z : ParabolicPoint) : ℝ :=
  timePartial v z + scalarLaplacian v z
    - 2 * ∑ i, spatialPartial φ i z * spatialPartial v i z
    + (scalarGradSq φ z - timePartial φ z - scalarLaplacian φ z) * v z

/-- The integrand of the commutator identity `eq:carleman-commutator` (ESS). -/
noncomputable def carlemanCommutatorDensity (φ v : ParabolicPoint → ℝ)
    (z : ParabolicPoint) : ℝ :=
  4 * z.2 ^ 2 *
      (∑ i, ∑ j, spatialSecondPartial φ i j z *
          (spatialPartial v i z * spatialPartial v j z +
            spatialPartial φ i z * spatialPartial φ j z * v z ^ 2))
    + z.2 ^ 2 * v z ^ 2 *
      (timePartial (fun y => timePartial φ y) z
        - 4 * ∑ i, spatialPartial φ i z * timePartial (fun y => spatialPartial φ i y) z
        - ∑ i, ∑ j, spatialSecondPartial
            (fun y => spatialSecondPartial φ i i y) j j z)
    + z.2 * scalarGradSq v z
    - z.2 * v z ^ 2 * (scalarGradSq φ z - timePartial φ z)

end CKN
