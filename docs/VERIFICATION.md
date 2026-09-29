# Verification

Run these commands from the repository root. The toolchain and dependencies
are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

## Install and build

With `elan` and Python 3 installed:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
python3 scripts/build.py CKN
python3 scripts/build_all.py
```

The whole library is written in Lean's module system. The first build
follows the imports of `CKN.lean`, including Theorems A–C and the six Leray existence and pressure theorems. The second builds every tracked module under `CKN/`, including
auxiliary results and examples. Library warnings are treated as errors.

The build wrapper checks the toolchain, the Mathlib revision and cache, and
that the Mathlib package is unchanged. Keep the committed manifest and avoid
`lake update` or `lake clean` during verification.

A normal successful build ends with:

```text
guarded local build: PASS (Mathlib package tree unchanged)
```

For a disposable checkout, CI sets `CKN_MAIN_CHECKOUT` to a different path and
uses `python3 scripts/build.py --fresh CKN`. This records cache-generated
package metadata changes instead of rejecting them. Ordinary development
builds use the stricter command above.

## Independent theorem statements

```sh
python3 scripts/build.py Comparators
python3 scripts/check_comparators.py
```

The root Challenge states Theorems A–C using Mathlib alone, with three
intentional proof placeholders. The separate Solution proves the same named
statements from the library. A second pair, `comparators/Leray/Challenge.lean`
and `comparators/Leray/Solution.lean`, does the same for five of the Leray
existence and pressure theorems (`leray_existence`,
`leray_existence_singularSet`, `lerayExistenceForced`,
`lerayExistenceForcedSingularSet` and `associatedPressure`); the checker runs
every pair, and `--pair Leray` selects this one. The local checker compares all shared source
definitions and theorem types and verifies the solutions' exact standard axiom
sets. `--no-build` performs source checks only; `--lake` also builds the target.

Run the upstream verification, including the independent NanoDa kernel:

```sh
scripts/verify_comparator.sh
```

This builds pinned verification tools in a user cache and runs them with
[comparator.json](../comparator.json) and
[comparators/Leray/comparator.json](../comparators/Leray/comparator.json),
one Palomar entry each. It requires Linux with Landlock support,
Go 1.24 or later, Rust/Cargo, Python 3, Git and Lean. See the
[comparator guide](../comparators/README.md) for the verification boundaries.

## Source checks and axioms

```sh
python3 scripts/check_rules.py
python3 scripts/dup_decls.py
python3 scripts/check_public.py
python3 scripts/check_axioms.py
```

The source checks enforce repository conventions and reject proof placeholders
in the library. The public-file check verifies the allowed file types, local
documentation links and library imports.

The axiom checker imports every tracked CKN module and checks every named
public declaration found by its source lexer. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted. In particular, `sorryAx`
and custom axioms are rejected. A failed Lean probe or a nonzero checker exit
status is a verification failure. File and declaration counts are reported
at run time.

## Inspect Theorems A–C directly

After building the library:

```sh
probe_dir=$(mktemp -d)
cat > "$probe_dir/MainAxioms.lean" <<'LEAN'
import CKN.Statements.TheoremA
import CKN.Statements.TheoremB
import CKN.Statements.TheoremC

#print axioms CKN.epsilonRegularityL3
#print axioms CKN.epsilonRegularityGradient
#print axioms CKN.caffarelliKohnNirenberg
LEAN
scripts/lean_direct.sh "$probe_dir/MainAxioms.lean" \
  -DautoImplicit=false -DwarningAsError=true
rm -rf -- "$probe_dir"
```

Each result should list exactly `[propext, Classical.choice, Quot.sound]`.
These are the standard logical axioms used by this formalization.

The six theorems of Leray's global existence theory (in
`CKN/Statements`: `LerayExistence`, `LerayExistenceSingularSet`,
`AssociatedPressure`, `LerayExistenceForced`,
`LerayExistenceForcedSingularSet` and `AssociatedPressureForced`) can be
inspected in the same way:

```lean
import CKN.Statements.LerayExistence
import CKN.Statements.LerayExistenceSingularSet
import CKN.Statements.AssociatedPressure
import CKN.Statements.LerayExistenceForced
import CKN.Statements.LerayExistenceForcedSingularSet
import CKN.Statements.AssociatedPressureForced

#print axioms CKN.leray_existence
#print axioms CKN.leray_existence_singularSet
#print axioms CKN.associatedPressure
#print axioms CKN.lerayExistenceForced
#print axioms CKN.lerayExistenceForcedSingularSet
#print axioms CKN.associatedPressureForced
```

Each again lists exactly `[propext, Classical.choice, Quot.sound]`.
`CKN.associatedPressureForced` is proved but not restated in a comparator.

## Verify a fresh clone

`scripts/verify_fresh_clone.sh` creates a temporary clone, obtains the dependency
cache and runs the builds, local comparator checks, source checks and axiom checks above.
Run the upstream Comparator separately as described above.
It uses `CKN_REPO_URL` when set, or the configured `origin` remote. Use
`--expected-sha SHA` to require a particular commit, `--plan` to print the
commands, or `--keep-on-failure` to retain a failed checkout for inspection.

Compilation establishes that the proofs are accepted by Lean. Mathematical
review remains necessary to check that the formal statements and definitions
express the intended results.
