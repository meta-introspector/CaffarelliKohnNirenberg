-- Copyright (c) 2026 Scott Armstrong.
-- Released under Apache 2.0 license.

module

public import CKN.Leray.AssocPressureProviderEventual

/-!
# Pointwise convergence of Helmholtz cutoff tests

The spatial cutoffs equal one on every fixed ball once their radius is large.
-/

@[expose] public section

open MeasureTheory Set Filter
open Filter
open scoped ENNReal Convolution Topology
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

set_option autoImplicit false

noncomputable section

namespace CKN.Leray

/-- The compact Helmholtz approximation agrees eventually with the original
test at every fixed space-time point. -/
theorem associatedPressureHelmholtzTestCutoff_value_eventually_eq
    {T : ℝ} {φ : Vec3 × ℝ → Vec3}
    (hφ : φ ∈ CKN.spaceTimeTestFunction (V := Vec3) Set.univ (Ioo 0 T))
    (i : Fin 3) (z : Vec3 × ℝ) :
    ∀ᶠ n : ℕ in atTop,
      associatedPressureHelmholtzTestCutoff φ n z i = φ z i := by
  let A := associatedPressureHelmholtzVectorPotential φ
  let ψ := associatedPressureHelmholtzScalarPotential φ
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    associatedPressureHelmholtzVectorPotential_contDiff hφ
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    associatedPressureHelmholtzScalarPotential_contDiff hφ
  have hAcomp (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => A q k) := (contDiff_apply ℝ ℝ k).comp hA
  have hN (k l : Fin 3) : ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd
        (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z =
      CKN.spatialPartialProd (fun q => A q k) l z := by
    filter_upwards [associatedPressurePotentialCutoff_direction_eventually_eq
      (hAcomp k) l z] with n hn
    have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (rieszPressurePotentialCutoffTest (fun q => A q k) n) :=
      rieszPressurePotentialCutoffTest_contDiff (hAcomp k) n
    have hbase := rieszPressure_sliceSpatialDeriv_eq_joint (hAcomp k) l z
    have hcut := rieszPressure_sliceSpatialDeriv_eq_joint hcutSmooth l z
    have hdef : (fun q : Vec3 × ℝ =>
        associatedPressureHelmholtzCutoffVectorPotential φ n q k) =
        rieszPressurePotentialCutoffTest (fun q => A q k) n := by
      funext q
      simp [associatedPressureHelmholtzCutoffVectorPotential,
        rieszPressurePotentialCutoffTest, A]
    rw [hdef]
    calc
      CKN.spatialPartialProd
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z =
        rieszPressureJointDirection
          (rieszPressurePotentialCutoffTest (fun q => A q k) n) l z := by
            change CKN.spatialDeriv
              (fun x => rieszPressurePotentialCutoffTest
                (fun q => A q k) n (x, z.2)) l z.1 = _
            exact hcut
      _ = rieszPressureJointDirection (fun q => A q k) l z := hn
      _ = CKN.spatialPartialProd (fun q => A q k) l z := by
            change _ = CKN.spatialDeriv (fun x => A (x, z.2) k) l z.1
            exact hbase.symm
  have hNall : ∀ᶠ n : ℕ in atTop,
      ∀ k l : Fin 3,
        CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q k) l z =
        CKN.spatialPartialProd (fun q => A q k) l z := by
    filter_upwards [Filter.eventually_all.2
      (fun k => Filter.eventually_all.2 (fun l => hN k l))] with n hn
    intro k l
    exact hn k l
  have hψN (k : Fin 3) : ∀ᶠ n : ℕ in atTop,
      CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) k z =
      CKN.spatialPartialProd ψ k z := by
    filter_upwards [associatedPressurePotentialCutoff_direction_eventually_eq hψ k z]
      with n hn
    have hcutSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) :=
      (associatedPressureHelmholtzScalarPotentialCutoff_mem_spaceTimeTestFunction
        hφ n).1
    have hcut := rieszPressure_sliceSpatialDeriv_eq_joint hcutSmooth k z
    have hbase := rieszPressure_sliceSpatialDeriv_eq_joint hψ k z
    change rieszPressureJointDirection
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) k z = _ at hn
    rw [← hcut, ← hbase] at hn
    exact hn
  have hψNall : ∀ᶠ n : ℕ in atTop, ∀ k : Fin 3,
      CKN.spatialPartialProd
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) k z =
      CKN.spatialPartialProd ψ k z :=
    Filter.eventually_all.2 hψN
  have hcurl : ∀ᶠ n : ℕ in atTop,
      associatedPressureTestCurl
        (associatedPressureHelmholtzCutoffVectorPotential φ n) z =
      associatedPressureTestCurl A z := by
    filter_upwards [hNall] with n hn
    apply funext
    intro j
    fin_cases j
    · change CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 1 z -
        CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 2 z = _
      rw [hn 2 1, hn 1 2]
      exact (associatedPressureTestCurl_zero A z).symm
    · change CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 2 z -
        CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 2) 0 z = _
      rw [hn 0 2, hn 2 0]
      exact (associatedPressureTestCurl_one A z).symm
    · change CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 1) 0 z -
        CKN.spatialPartialProd
          (fun q => associatedPressureHelmholtzCutoffVectorPotential φ n q 0) 1 z = _
      rw [hn 1 0, hn 0 1]
      exact (associatedPressureTestCurl_two A z).symm
  have hgrad : ∀ᶠ n : ℕ in atTop,
      associatedPressureTestGradient
        (associatedPressureHelmholtzScalarPotentialCutoff φ n) z =
      associatedPressureTestGradient ψ z := by
    filter_upwards [hψNall] with n hn
    apply funext
    intro k
    exact hn k
  filter_upwards [hcurl, hgrad] with n hnCurl hnGrad
  have hvector := associatedPressureHelmholtz_identity hφ z
  have hvalue : associatedPressureHelmholtzTestCutoff φ n z = φ z := by
    calc
      associatedPressureHelmholtzTestCutoff φ n z =
          associatedPressureTestCurl
              (associatedPressureHelmholtzCutoffVectorPotential φ n) z +
            associatedPressureTestGradient
              (associatedPressureHelmholtzScalarPotentialCutoff φ n) z := rfl
      _ = associatedPressureTestCurl A z + associatedPressureTestGradient ψ z := by
        rw [hnCurl, hnGrad]
      _ = φ z := hvector.symm
  exact congrArg (fun v : Vec3 => v i) hvalue

end CKN.Leray

end
