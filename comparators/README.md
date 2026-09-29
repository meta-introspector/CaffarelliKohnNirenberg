# Independent statements and proof comparison

[Challenge.lean](Challenge.lean) states Theorems A, B and C using only Mathlib
imports. It includes the definitions of suitable weak solutions, parabolic
geometry, Hölder regularity and the singular set, followed by three intentional
proof placeholders. A mathematical reader can compare it with the manuscript
without reading the proof library.

[Solution.lean](Solution.lean) defines the same objects and proves the same
named theorems from the library's results. The public statement layer uses
Mathlib's Euclidean spaces, continuous-linear-map weak derivatives and
ordinary product coordinates; the proof supplies the exact coordinate and
measure transports to the library's older componentwise presentation. It does
not import the Challenge. These are separate Lean environments: importing both
modules into one file would introduce duplicate declarations.

| Declaration in both environments | Library theorem |
|---|---|
| `CKNChallenge.epsilonRegularityL3` | `CKN.epsilonRegularityL3` |
| `CKNChallenge.epsilonRegularityGradient` | `CKN.epsilonRegularityGradient` |
| `CKNChallenge.caffarelliKohnNirenberg` | `CKN.caffarelliKohnNirenberg` |

The [configuration](../comparator.json) selects all three declarations for one
Palomar submission. The Challenge is below the 1,000-line and 100-KiB limits.

## Second pair: Leray existence

[Leray/Challenge.lean](Leray/Challenge.lean) and
[Leray/Solution.lean](Leray/Solution.lean) form a second, independent pair
(modules `comparators.Leray.Challenge` and `comparators.Leray.Solution`, same
`CKNLerayChallenge` namespace, so that its definitions never share a name with the first pair's). The Challenge again imports only Mathlib. It defines
Leray--Hopf solutions (global, forced, and the force integrability classes),
the parabolic Hausdorff measure and the singular set, and states five existence
theorems. The Solution repeats those definitions and statements verbatim, adds
the transport lemmas to the library's coordinates, and proves them from the
library theorems in `CKN/Statements/`.

| Declaration in both environments | Library theorem |
|---|---|
| `CKNLerayChallenge.leray_existence` | `CKN.leray_existence` |
| `CKNLerayChallenge.leray_existence_singularSet` | `CKN.leray_existence_singularSet` |
| `CKNLerayChallenge.lerayExistenceForced` | `CKN.lerayExistenceForced` |
| `CKNLerayChallenge.lerayExistenceForcedSingularSet` | `CKN.lerayExistenceForcedSingularSet` |
| `CKNLerayChallenge.associatedPressure` | `CKN.associatedPressure` |

The library theorems live in `CKN/Statements/LerayExistence.lean`,
`LerayExistenceSingularSet.lean`, `LerayExistenceForced.lean`,
`LerayExistenceForcedSingularSet.lean` and `AssociatedPressure.lean`.
The library theorem `CKN.associatedPressureForced` is proved but not restated
here: its Riesz-type pressure split would have to be defined from Mathlib inside
the Challenge, and no concise restatement was attempted within the 1,000-line
limit.

The [configuration](Leray/comparator.json) selects the five declarations as one
Palomar entry. In general one `comparator.json` is one Palomar entry, and the
tooling below discovers every configuration: `comparator.json` (the pair above)
and `comparators/*/comparator.json`.

## Local checks

After building the library, run:

```sh
python3 scripts/check_comparators.py
```

This runs every pair, printing `Comparator sources PASS (<pair>)` for each;
`--pair PATH` (a `comparator.json`, its directory, or a name such as `Leray`)
checks one pair only. For each pair the checker also requires a `module` header,
Mathlib-only Challenge imports (in any qualified form) and the Challenge size
limits.

This compares the full public definition source, theorem types and instance
choices shared by the Challenge and Solution. The Solution additionally
contains the coordinate-transport lemmas used by its proofs. The checker
requires one intentional Challenge warning per selected theorem (three for Theorems A–C and five for the Leray pair), a clean Solution elaboration
with warnings treated as errors, and exactly
`[propext, Classical.choice, Quot.sound]` as the axiom set of each solution.
Temporary compiled Solution files take precedence over existing build
artifacts when inspecting those axioms.

`--no-build` performs source checks only. `--lake` additionally builds the
`Comparators` target. The ordinary `lake build` target builds the CKN library.

## Upstream Comparator and NanoDa

```sh
lake exe cache get
scripts/verify_comparator.sh
```

The script builds pinned revisions of
[Comparator](https://github.com/leanprover/comparator),
[lean4export](https://github.com/leanprover/lean4export),
[NanoDa](https://github.com/robsimmons/nanoda_lib) and
[Landrun](https://github.com/zouuup/landrun), then runs every configuration (`comparator.json` and `comparators/*/comparator.json`) in turn.
Their commit pins are recorded in the script. This requires Linux with
Landlock support, Go 1.24 or later, Rust/Cargo, Git, Python 3 and the project's
Lean toolchain. Tools are stored under `${XDG_CACHE_HOME:-$HOME/.cache}/ckn-comparator`;
set `CKN_COMPARATOR_CACHE` to use a different directory.

Comparator checks the exported statement dependency closures, allowed axioms
and proofs. NanoDa independently replays the exported Solution in a second
kernel. The local source checker complements this by checking that the cleaned
public layer is literally shared between Challenge and Solution. Neither check
establishes that the definitions express the intended mathematics; that
requires review against the manuscript.

A local run does not reproduce Palomar's entire hosted intake process, which
also checks the pinned public snapshot, dependency provenance, metadata,
licensing and editorial criteria. See the current
[submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md).
