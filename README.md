# Caffarelli–Kohn–Nirenberg partial regularity, formalized in Lean 4

[![Build and verify](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/build.yml)
[![Comparators](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/comparators.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/CaffarelliKohnNirenberg/actions/workflows/comparators.yml)

A complete, machine-checked proof of the Caffarelli–Kohn–Nirenberg theorem
and of the existence of Leray weak solutions that are suitable, for the
three-dimensional incompressible Navier–Stokes equations:

- **The Caffarelli–Kohn–Nirenberg theorem.** For suitable weak solutions,
  the set of singular space-time points has zero one-dimensional parabolic
  Hausdorff measure (Theorems A–C below).
- **Existence of suitable Leray weak solutions.** Every divergence-free
  initial velocity in $L^2(\mathbb{R}^3)$ has a global Leray–Hopf weak
  solution which, together with an associated pressure, is a suitable weak
  solution; by the first result its singular set has zero one-dimensional
  parabolic Hausdorff measure. The associated pressure and versions with a
  force are proved as well (see
  [Leray existence](#leray-existence-and-the-associated-pressure)).

The formalization is written in Lean 4 on top of Mathlib and covers both
arguments in full, from the definitions of suitable weak solutions and
Leray–Hopf solutions to the final covering argument and the passage to the
limit. The library uses no axioms beyond Lean's standard three and contains
no unfinished proofs.

The forcing term is allowed to lie in $L^q_{\mathrm{loc}}$ for any $q > 5/2$
and need not be divergence free. The proof keeps the direct scale iteration
of Caffarelli, Kohn and Nirenberg in the form organised by Kukavica, and
closes it with a Morrey-space bootstrap and potential estimates in the manner
of O'Leary and Lemarié-Rieusset; Lin's work supplies the pressure estimates.
It is written out in full in the accompanying [manuscript](paper/ckn.pdf).
The manuscript and the Lean development were produced together: Theorems A–C and the six Leray existence and pressure results are stated in Lean with the manuscript's hypotheses and conclusions.

## Results formalized

- **L. Caffarelli, R. Kohn and L. Nirenberg, "Partial regularity of suitable
  weak solutions of the Navier–Stokes equations", *Comm. Pure Appl. Math.* 35
  (1982), 771–831.** Formalized: the partial regularity theorem (Theorem C
  below) and its two ε-regularity criteria (Theorems A and B), for forces in
  $L^q_{\mathrm{loc}}$ with $q>5/2$. The proof keeps the direct scale
  iteration in the form of I. Kukavica, *Discrete Contin. Dyn. Syst.* 21
  (2008), 717–728, with pressure estimates from F. Lin, *Comm. Pure Appl.
  Math.* 51 (1998), 241–257, as described below.
- **J. Leray, "Sur le mouvement d'un liquide visqueux emplissant l'espace",
  *Acta Math.* 63 (1934), 193–248.** Formalized: global existence of a weak
  (Leray–Hopf) solution on $\mathbb{R}^3$ for every divergence-free initial
  velocity in $L^2$, in the suitable form, with its associated pressure and
  versions with a force. The construction follows the modern review of
  W. S. Ożański and B. C. Pooley, LMS Lecture Note Series 452 (2018),
  113–203; suitability follows T.-P. Tsai, *Lectures on Navier–Stokes
  Equations* (AMS, 2018), and J. C. Robinson, J. L. Rodrigo and W. Sadowski,
  *The Three-Dimensional Navier–Stokes Equations* (CUP, 2016). See
  [Leray existence](#leray-existence-and-the-associated-pressure).

## What is proved

Space is $\mathbb{R}^3$ and time is $\mathbb{R}$. A suitable weak solution
$(u,p)$ on an open product domain $\Omega\times I$ has locally finite energy, pressure locally in
$L^{3/2}$, satisfies the momentum equation and incompressibility weakly, and
satisfies the local energy inequality. $Q_r(x,t)$ is the past parabolic
cylinder $B_r(x)\times(t-r^2,t]$. A point is regular if $u$ agrees almost
everywhere with a parabolically Hölder-continuous function on a
neighbourhood. In every statement the constants are chosen after $q$ and
before the solution.

**Theorem A, small-data regularity** (Theorem 2.7 of the manuscript).
For each $q>5/2$ there are $\varepsilon_0>0$, an exponent
$0<\gamma_0\le 2/3$ and a constant $C_4$ such that every suitable weak
solution defined on a neighbourhood of the closed unit cylinder with

$$\iint_{Q_1}\bigl(|u|^3+|p|^{3/2}+|f|^q\bigr)\le\varepsilon_0$$

coincides almost everywhere on $Q_{1/2}$ with a function whose parabolic
Hölder norm of exponent $\gamma_0$ on the closed half-cylinder is at most
$C_4$, and every point of the open interior of $Q_{1/2}$ is regular.

**Theorem B, gradient regularity** (Theorem 2.9).
For each $q>5/2$ there is $\varepsilon_1>0$ such that an interior point
$z_0$ of a suitable weak solution is regular whenever

$$\limsup_{r\downarrow 0}\ \frac1r\iint_{Q_r(z_0)}|\nabla u|^2<\varepsilon_1^2 .$$

**Theorem C, partial regularity** (Theorem 2.10).
For every suitable weak solution with force in $L^q_{\mathrm{loc}}$,
$q>5/2$, the singular set has zero one-dimensional parabolic Hausdorff
measure.

Theorem C is a modern formulation of the Caffarelli–Kohn–Nirenberg theorem. The solution class uses the local pressure hypothesis $p\in L^{3/2}$ of
Lin and Ladyzhenskaya–Seregin. It is deduced from Theorem B by a covering argument. Theorems A and B are proved side by
side in the manuscript's $\varepsilon$-regularity section; B is not deduced
from A.

## Leray existence and the associated pressure

The library also contains a formalization of Leray's global existence theory,
so that the solution class of the three theorems above is shown to be
non-empty for every divergence-free $L^2$ datum. The proofs are in the new part
of the manuscript on global existence. The space $J$ of initial data is the
$L^2$ closure of smooth, compactly supported, divergence-free vector fields
(`CKN.IsInJ`); a Leray–Hopf solution on $[0,T]$ with datum $a\in J$ has finite
energy and dissipation, is weakly divergence free and weakly continuous in
time on the closed interval, satisfies the weak equation against
divergence-free tests and the energy inequality at every time, and attains $a$
in $L^2$ as $t\downarrow 0$ (`CKN.IsLerayHopfSolution`); a global solution is
one on every finite interval (`CKN.IsGlobalLerayHopfSolution`).

- **Leray existence in suitable form.** For every $a\in J$ there are $u$, $Du$
  and $p$ such that $(u,Du)$ is a global Leray–Hopf solution with datum $a$ and
  $(u,Du,p,0)$ is a suitable weak solution on $\mathbb{R}^3\times(0,\infty)$
  for every $q>5/2$.
- **Singular set.** Consequently, every $a\in J$ has a global Leray–Hopf
  solution whose singular set has zero one-dimensional parabolic Hausdorff
  measure (Theorem C).
- **Associated pressure.** Every Leray–Hopf solution on $[0,T]$ has a pressure
  $p\in L^{5/3}(\mathbb{R}^3\times(0,T))$, the double Riesz transform of
  $u\otimes u$, for which the momentum equation holds against all compactly
  supported vector tests; if moreover $u\in L^\infty(0,T;L^3)$ then
  $p\in L^\infty(0,T;L^{3/2})$.
- **Forced versions.** The same results hold for forces in
  $L^2_{\mathrm{loc}}([0,\infty);L^2)$ that are locally in $L^q$ for some
  $q>5/2$: one solution is suitable for every such $q$, its singular set is
  null, and its pressure splits into the quadratic Riesz pressure and a
  pressure determined by the force.

| Lean declaration | File |
|---|---|
| `CKN.leray_existence` | [CKN/Statements/LerayExistence.lean](CKN/Statements/LerayExistence.lean) |
| `CKN.leray_existence_singularSet` | [CKN/Statements/LerayExistenceSingularSet.lean](CKN/Statements/LerayExistenceSingularSet.lean) |
| `CKN.associatedPressure` | [CKN/Statements/AssociatedPressure.lean](CKN/Statements/AssociatedPressure.lean) |
| `CKN.lerayExistenceForced` | [CKN/Statements/LerayExistenceForced.lean](CKN/Statements/LerayExistenceForced.lean) |
| `CKN.lerayExistenceForcedSingularSet` | [CKN/Statements/LerayExistenceForcedSingularSet.lean](CKN/Statements/LerayExistenceForcedSingularSet.lean) |
| `CKN.associatedPressureForced` | [CKN/Statements/AssociatedPressureForced.lean](CKN/Statements/AssociatedPressureForced.lean) |

The definitions they use (`IsInJ`, `IsLerayHopfSolution`,
`IsGlobalLerayHopfSolution`, `IsForcedLerayHopfSolution`,
`IsGlobalForcedLerayHopfSolution`, `IsLocallySquareIntegrableForce`,
`IsLocallyQIntegrableForce`, `forcedQuadraticTensor`, `HasSpaceTimeWeakDerivs`)
are in the same directory, and the proofs are assembled in
[CKN/Main](CKN/Main). The construction (the associated pressure by Riesz
transforms, Leray-regularized equations, uniform bounds, compactness, the
passage to the limit and the forced versions) is in [CKN/Leray](CKN/Leray),
with generic helpers in [CKN/Leray/Support](CKN/Leray/Support).

Sources: J. Leray, *Acta Math.* 63 (1934), 193–248, in the modern exposition
of W. S. Ożański and B. C. Pooley (LMS Lecture Note Series 452, 2018,
113–203); suitability of the limit follows T.-P. Tsai, *Lectures on
Navier–Stokes Equations* (AMS, 2018), Theorem 3.9, and J. C. Robinson,
J. L. Rodrigo and W. Sadowski, *The Three-Dimensional Navier–Stokes
Equations: Classical Theory* (CUP, 2016). Two departures are worth naming: the
regularized solutions are built by a Fourier–$L^2$ construction in place of the
Oseen-kernel one, and the associated pressure is the whole-space double Riesz
transform of $u\otimes u$. See [docs/DEVIATIONS.md](docs/DEVIATIONS.md).

This material was developed in the formalization of the
Escauriaza–Seregin–Šverák theorem and moved into this library, which now
proves that its solution class is non-empty; that formalization imports it
from here. The moved files keep their own copyright line, "Scott Armstrong."

## The Lean statements

Theorems A–C are stated in [CKN/Statements](CKN/Statements) exactly as below.
`Vec3` is `Fin 3 → ℝ`, a `ParabolicPoint` is a pair of a point and a time,
and `IsSuitableWeakSolution Ω I q u Du p f` is the suitable-solution
predicate on the domain $\Omega\times I$, carrying an explicit weak
spatial gradient `Du` of `u`. It expresses the manuscript's definition, with the representation choices
described below:
the regularity conditions, the divergence-free and momentum identities and
the local energy inequality, with no integrability side condition on the
integrands they test. The library also carries a variant
`IsSuitableWeakSolutionIntegrable` that states those side conditions explicitly; the
two classes have the same inhabitants, and
`CKN.isSuitableWeakSolution_iff_integrable` proves it. The statements and their key definitions are in [CKN/Statements](CKN/Statements)
and [CKN/Foundation](CKN/Foundation). The
[design notes](docs/DESIGN_NOTES.md) explain the choices behind them.

Theorem A, [`CKN.epsilonRegularityL3`](CKN/Statements/TheoremA.lean):

```lean
theorem epsilonRegularityL3 (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₀ γ₀ C₄ : ℝ, 0 < ε₀ ∧ 0 < γ₀ ∧ γ₀ ≤ 2 / 3 ∧ 0 ≤ C₄ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution Ω I q u Du p f →
        closure (parabolicCylinder 0 0 1) ⊆ spaceTimeSet Ω I →
        (∫⁻ z in parabolicCylinder 0 0 1,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤ ENNReal.ofReal ε₀ →
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict (parabolicCylinder 0 0 (1 / 2))] u ∧
          ParabolicHolderVecNormLE (closure (parabolicCylinder 0 0 (1 / 2)))
            w γ₀ C₄ ∧
          ∀ z ∈ vec3Ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) 0,
            IsRegularPoint Ω I u z
```

Theorem B, [`CKN.epsilonRegularityGradient`](CKN/Statements/TheoremB.lean):

```lean
theorem epsilonRegularityGradient (q : ℝ) (hq : 5 / 2 < q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
        (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        (hsol : IsSuitableWeakSolution Ω I q u Du p f) →
        ∀ z₀ ∈ spaceTimeSet Ω I,
          Filter.limsup (fun r : ℝ =>
              (ENNReal.ofReal r)⁻¹ *
                ∫⁻ w in parabolicCylinder z₀.1 z₀.2 r,
                  ENNReal.ofReal (spatialGradientSq u Du w))
            (𝓝[>] (0 : ℝ)) < ENNReal.ofReal (ε₁ ^ (2 : ℕ)) →
          IsRegularPoint Ω I u z₀
```

Theorem C, [`CKN.caffarelliKohnNirenberg`](CKN/Statements/TheoremC.lean):

```lean
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0
```

The Hausdorff measure in Theorem C is defined with the parabolic diameter
gauge. The manuscript uses a radius gauge; the two have the same null sets,
which is all the theorem asserts.

Because a formal statement is only as good as the definitions inside it,
the repository also contains a standalone [Challenge](comparators/Challenge.lean)
that defines the objects using Mathlib alone and states all three theorems.
The separate [Solution](comparators/Solution.lean) proves the same named
declarations from the library. [Comparator](comparators/README.md) checks
their statement dependency closures and proofs, including an independent
NanoDa kernel replay. Reading the Challenge is the quickest way to inspect
the precise mathematical claims.

A second, independent pair, [comparators/Leray](comparators/Leray), restates
the Leray existence theorems in the same way, again from Mathlib alone: it
covers `leray_existence`, `leray_existence_singularSet`, `lerayExistenceForced`,
`lerayExistenceForcedSingularSet` and `associatedPressure`. The theorem
`CKN.associatedPressureForced` is proved but not restated there.

## How the formalization relates to the manuscript

The manuscript is the paper being formalized, not a description written
after the fact, and it was corrected as the formalization progressed. Theorems A–C and the six Leray existence and pressure results are proved as stated. Supporting results follow
the proof route described in the manuscript; unused alternative arguments
and auxiliary exposition without a Lean counterpart are identified in the documentation. Some auxiliary quantitative estimates are proved only in the special cases
used by the main proofs, including two fixed-centre parameter triples and
an affine rather than linear bound; entries
B58 to B62 of [docs/DEVIATIONS.md](docs/DEVIATIONS.md) list each one. Where the
formalization led us to change a statement or a proof, the
[deviations](docs/DEVIATIONS.md) document explains what changed and why, with the current scope stated explicitly.

Leray existence gives, for every divergence-free $L^2$ datum, a suitable
weak solution on $\mathbb{R}^3\times(0,\infty)$, so the solution class of
Theorems A–C is non-empty. The formalization also includes a concrete nonzero
suitable weak solution, the viscous shear flow $u(x,t)=(e^{-t}\sin x_2,0,0)$
with zero pressure and force, and the zero solutions of the Leray–Hopf and
forced Leray–Hopf classes ([CKN/Witnesses](CKN/Witnesses/LerayHopfZero.lean)).
The [witnesses](docs/WITNESSES.md) page lists what has been checked in this
direction.

## Building and checking it yourself

The project pins Lean 4 and Mathlib at v4.35.0-rc2. With `elan` and Python 3
installed:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
python3 scripts/build.py CKN
```

The whole library is written in Lean's module system. It contains about
400,000 lines of Lean in 1,815 files. Build time depends on the
machine and availability of the Mathlib cache. Keep the committed dependency
manifest; avoid `lake update` or `lake clean` when verifying this version.

To confirm the axioms used by the main theorems, or to run the
source and comparator checks, follow the
[verification guide](docs/VERIFICATION.md). Each main theorem, including
each of the six Leray existence and pressure theorems above, depends
exactly on `propext`, `Classical.choice` and `Quot.sound`.

## Repository layout

- [CKN/Statements](CKN/Statements): the main theorem statements and definitions of suitable weak solutions, regular and singular points, and scale-invariant quantities.
- [CKN/Foundation](CKN/Foundation): parabolic geometry, Sobolev spaces, weak derivatives, mollification, harmonic and heat-kernel estimates, Morrey and Campanato norms.
- [CKN/Setting](CKN/Setting): basic consequences of the suitable-solution definition (energy slices, cut-offs, interpolation on cylinders) and the shear-flow example.
- [CKN/Pressure](CKN/Pressure): the pressure theory: potentials, decompositions and the pressure-gradient estimates.
- [CKN/Core](CKN/Core): the proof itself, organised by the steps of the manuscript.
- [CKN/Covering](CKN/Covering): the parabolic Vitali covering and Hausdorff-measure argument of Theorem C.
- [CKN/Witnesses](CKN/Witnesses): explicit examples showing the definitions are inhabited.
- [CKN/ClassEquivalence](CKN/ClassEquivalence): the proof that the integrability conditions carried by the suitable-solution class follow from its energy conditions, so that the Lean class is the manuscript's.
- [CKN/Leray](CKN/Leray): Leray's global existence theory: the associated pressure, regularized equations, uniform bounds, compactness, the passage to the limit and the forced versions, with generic helpers in [CKN/Leray/Support](CKN/Leray/Support).
- [CKN/Main](CKN/Main): the assembly of the main theorems from the core results.
- [comparators](comparators): the two independent Mathlib-only pairs described above (Theorems A–C, and `comparators/Leray`).
- [paper](paper): the manuscript source and PDF.
- [docs](docs): design notes, deviations, witnesses, verification guide, and the [bibliography](docs/SOURCES.md).
- [scripts](scripts): the guarded build, checking, comparison, and release-verification tools.

## How this was made

The original CKN development was written in roughly 48 hours with AI coding tools under the authors' supervision. Claude Fable 5.1 coordinated work using GPT 5.6-Luna, GPT Astra, Deepseek 4.1 flash, Leanstral and Opus 5. The Leray existence development was written as part of the Escauriaza–Seregin–Šverák formalization from 2026-09-26 to 2026-09-29 (Claude Opus 5.5 coordinating GPT-6 Luna and GPT-6 Sol) and transferred here on 2026-09-29. The transfer and the port of the whole library to Lean's module system were done with Claude Sonnet 5.5 coordinated by Claude Opus 5.5, with independent reviews including a GPT-6 Sol audit. The authors
reviewed the theorem statements before proof development and decided the
mathematics and the corrections to the manuscript. Separate reviews checked
the statements and the use of intermediate results in the main proofs.
Lean checks the proofs; the comparator files make their mathematical
statements available for independent inspection.

## Contributing, authors and license

See [Contributing](CONTRIBUTING.md) for the source rules and checks, and
[CITATION.cff](CITATION.cff) for how to cite this work.

The Lean development is by:

- **Scott Armstrong**, CNRS and Laboratoire Jacques-Louis Lions, Sorbonne
  Université; Courant Institute School of Mathematics, Computing, and Data Science, New York University.
  Supported by the European Research Council under the European Union's
  Horizon Europe programme, grant agreement No. 101200828.
- **Vlad Vicol**, Courant Institute School of Mathematics, Computing, and Data Science, New York University. Partially supported by Collaborative NSF
  grant DMS-2307681 and a Simons Investigator Award.

The repository is by Scott Armstrong and Vlad Vicol. Individual files retain their authors' copyright notices, including Scott Armstrong's notice on the transferred Leray files. The Lean library, software, documentation and included manuscript are distributed under the
[Apache License 2.0](LICENSE). Cited third-party works and dependencies retain
their own licenses.
