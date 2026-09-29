#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
"""Check the Challenge/Solution source agreement and Lean axiom dependencies.

For upstream Comparator and independent NanoDa replay, also run
scripts/verify_comparator.sh. This local check does not replace that replay.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import check_axioms
from check_axioms import strip_comments

ROOT = Path(__file__).resolve().parents[1]
NAMES = ('epsilonRegularityL3', 'epsilonRegularityGradient', 'caffarelliKohnNirenberg')
AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def normalized(text: str) -> str:
    return ' '.join(strip_comments(text).split())


def statement(text: str, name: str) -> str:
    start = text.index(f'theorem {name} ')
    return text[start:text.index(':=', start)].strip()


def between(text: str, start: str, end: str) -> str:
    left = text.index(start)
    return text[left:text.index(end, left)]


def has_module_header(text: str) -> bool:
    return check_axioms.strip_comments(text).split()[:1] == ['module']


def challenge_imports_only_mathlib(text: str) -> bool:
    """True if every import (in any qualified form) is Mathlib and there is one."""
    imports = check_axioms.imported_modules(text)
    stray = re.findall(r'^[ \t]*(?:public[ \t]+|meta[ \t]+)*import\b', check_axioms.strip_comments(text), re.M)
    return bool(imports) and len(imports) == len(stray) and all(
        name == 'Mathlib' or name.startswith('Mathlib.') for name in imports)


def discover(root: Path = ROOT) -> list[Path]:
    """Every comparator configuration: the root pair, then comparators/*/comparator.json."""
    found = [p for p in [root / 'comparator.json'] if p.is_file()]
    found += sorted(root.glob('comparators/*/comparator.json'))
    return found


def pair_label(config_path: Path, root: Path = ROOT) -> str:
    return 'root' if config_path.parent == root else config_path.parent.name


def check_pair(config_path: Path, root: Path = ROOT) -> tuple[str, int]:
    """Source checks of one pair; returns (label, Challenge line count)."""
    if config_path.parent == root:
        return 'root', check_root_pair(root)
    return pair_label(config_path, root), check_topic_pair(config_path, root)


def check_topic_pair(config_path: Path, root: Path) -> int:
    topic = config_path.parent.name
    config = json.loads(config_path.read_text())
    require(isinstance(config, dict) and set(config) == {
        'challenge_module', 'solution_module', 'theorem_names', 'definition_names',
        'permitted_axioms', 'enable_nanoda'}, f'{topic}: comparator.json has missing or unknown fields')
    require(config['challenge_module'] == f'comparators.{topic}.Challenge'
            and config['solution_module'] == f'comparators.{topic}.Solution',
            f'{topic}: comparator.json must select comparators.{topic}.Challenge and .Solution')
    names = config['theorem_names']
    require(isinstance(names, list) and names and all(isinstance(n, str) for n in names)
            and all(n.startswith(namespace_for(topic) + '.') and n.count('.') == 1 for n in names)
            and len(set(names)) == len(names),
            f'{topic}: theorem_names must be distinct {namespace_for(topic)}.<name> strings')
    require(config['definition_names'] == [] and config['permitted_axioms'] == AXIOMS
            and config['enable_nanoda'] is True,
            f'{topic}: comparator.json must select only theorems, the standard axioms and NanoDa')
    local = [n.split('.', 1)[1] for n in names]
    challenge = (root / 'comparators' / topic / 'Challenge.lean').read_text()
    solution = (root / 'comparators' / topic / 'Solution.lean').read_text()
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            f'{topic}: Challenge exceeds the 1000-line or 100-KiB limit')
    require(len(re.findall(r'\bsorry\b', strip_comments(challenge))) == len(local),
            f'{topic}: Challenge must have exactly {len(local)} intentional proof placeholders')
    require(not re.search(r'\b(?:sorry|admit|axiom|constant)\b', strip_comments(solution)),
            f'{topic}: Solution contains a placeholder or axiom declaration')
    check_common(topic, challenge, solution)
    imports = check_axioms.imported_modules(challenge)
    solution_imports = check_axioms.imported_modules(solution)
    extra = solution_imports[len(imports):]
    require(solution_imports[:len(imports)] == imports and extra
            and all(m.startswith('CKN.') for m in extra),
            f'{topic}: Solution must import the Challenge Mathlib modules, then CKN modules only')

    def body(text: str) -> str:
        text = re.sub(r'^[ \t]*(?:public[ \t]+|meta[ \t]+)*import\b.*$', '', text, flags=re.M)
        return normalized(re.sub(r'^open CKN[ \t]*$', '', text, flags=re.M))

    def first_docstring(text: str) -> int:
        cut = min(text.index(f'theorem {n} ') for n in local)
        return text.rindex('/--', 0, cut)
    cbody = body(challenge[:first_docstring(challenge)])
    sbody = body(solution)
    require(sbody.startswith(cbody),
            f'{topic}: Solution does not repeat the Challenge definitions verbatim')
    for name in local:
        require(statement(challenge, name) == statement(solution, name),
                f'{topic}: Challenge/Solution statement of {name} differs')
    return len(challenge.splitlines())


def namespace_for(topic: str) -> str:
    """The root pair uses CKNChallenge; the pair in comparators/<Topic>/ uses CKN<Topic>Challenge,
    so that the pairs' Mathlib-native definitions never share a name."""
    return 'CKNChallenge' if topic in ('root', '') else f'CKN{topic}Challenge'


def check_common(label: str, challenge: str, solution: str) -> None:
    expected = namespace_for(label)
    for text, what in [(challenge, 'Challenge'), (solution, 'Solution')]:
        require(re.findall(r'^namespace (\S+)', text, re.M) == [expected],
                f'{label}: {what} must use the {expected} namespace')
        require(not re.search(r'^\s*private\b', strip_comments(text), re.M),
                f'{label}: {what} has private declaration names')
        require(all(option == 'autoImplicit false' for option in
                    re.findall(r'^set_option (.+)$', text, re.M)),
                f'{label}: {what} sets an unexpected Lean option')
        require(has_module_header(text), f'{label}: {what} must start with a `module` header')
    require(challenge_imports_only_mathlib(challenge), f'{label}: Challenge must import only Mathlib')


def check_root_pair(root: Path) -> int:
    ROOT_ = root
    config = json.loads((ROOT_ / 'comparator.json').read_text())
    require(config == {
        'challenge_module': 'comparators.Challenge',
        'solution_module': 'comparators.Solution',
        'theorem_names': ['CKNChallenge.' + name for name in NAMES],
        'definition_names': [], 'permitted_axioms': AXIOMS, 'enable_nanoda': True,
    }, 'Comparator configuration does not select the three main theorems')
    challenge = (ROOT_ / 'comparators/Challenge.lean').read_text()
    solution = (ROOT_ / 'comparators/Solution.lean').read_text()
    require(len(challenge.splitlines()) <= 1000 and len(challenge.encode()) <= 100 * 1024,
            'Challenge exceeds the 1000-line or 100-KiB limit')
    require(len(re.findall(r'\bsorry\b', strip_comments(challenge))) == 3,
            'Challenge must have exactly three intentional proof placeholders')
    require(not re.search(r'\b(?:sorry|admit|axiom|constant)\b', strip_comments(solution)),
            'Solution contains a placeholder or axiom declaration')
    check_common('root', challenge, solution)
    imports = check_axioms.imported_modules(challenge)
    extra_imports = check_axioms.imported_modules(solution)
    require(extra_imports == [f'CKN.Statements.Theorem{x}' for x in 'ABC'] + imports,
            'Solution must import the library theorems and Mathlib, never the Challenge')
    # The public comparator layer is deliberately cleaner than the historical
    # library API.  Check that Challenge and Solution nevertheless duplicate
    # that layer exactly.  Solution may then add only the coordinate-transport
    # machinery needed to derive it from the library theorems.
    prelude_start = '/-!\n# The Caffarelli–Kohn–Nirenberg theorems'
    challenge_prelude = between(
        challenge, prelude_start, '/-! ## The three theorems -/')
    solution_prelude = between(
        solution, prelude_start, '/-- The squared scale-invariant Dirichlet energy')
    require(normalized(challenge_prelude) == normalized(solution_prelude),
            'Challenge/Solution public definitions or instance choices differ')
    beta_start = '/-- The squared scale-invariant Dirichlet energy'
    challenge_beta = between(challenge, beta_start, '/-- Theorem B:')
    solution_beta = between(solution, beta_start, 'abbrev RawSpace :=')
    require(normalized(challenge_beta) == normalized(solution_beta),
            'Challenge/Solution betaSq definitions differ')
    for letter, name in zip('ABC', NAMES):
        require(statement(challenge, name) == statement(solution, name),
                f'Challenge/Solution theorem {letter} types differ')
    return len(challenge.splitlines())


def lean(path: Path, *args: str) -> str:
    proc = subprocess.run([str(ROOT / 'scripts/lean_direct.sh'), str(path),
                           '-DautoImplicit=false', *args], cwd=ROOT,
                          capture_output=True, text=True)
    output = proc.stdout + proc.stderr
    require(proc.returncode == 0, output or f'Lean failed for {path}')
    return output


def check_proofs(config_path: Path, root: Path = ROOT) -> None:
    config = json.loads(config_path.read_text())
    names = config['theorem_names']
    challenge_module, solution_module = config['challenge_module'], config['solution_module']
    solution_rel = Path(*solution_module.split('.')).with_suffix('.lean')
    challenge = root / Path(*challenge_module.split('.')).with_suffix('.lean')
    solution = root / solution_rel
    with tempfile.TemporaryDirectory(prefix='ckn-comparator-') as tmp:
        staging = Path(tmp)
        olean = (staging / solution_rel).with_suffix('.olean')
        olean.parent.mkdir(parents=True)
        diagnostics = lean(challenge).splitlines()
        require(len(diagnostics) == len(names) and all(
            'warning: declaration uses `sorry`' in line for line in diagnostics),
            f'Unexpected Challenge diagnostics: {diagnostics}')
        diagnostics = lean(solution, '-DwarningAsError=true', '-o', str(olean))
        require(not diagnostics.strip(), f'Unexpected Solution diagnostics: {diagnostics}')
        probe = staging / 'Axioms.lean'
        probe.write_text(f'import {solution_module}\n' + ''.join(
            f'#print axioms {name}\n' for name in names))
        old = os.environ.get('CKN_EXTRA_LEAN_PATH')
        os.environ['CKN_EXTRA_LEAN_PATH'] = str(staging)
        try:
            output = lean(probe, '-DwarningAsError=true').splitlines()
        finally:
            if old is None:
                del os.environ['CKN_EXTRA_LEAN_PATH']
            else:
                os.environ['CKN_EXTRA_LEAN_PATH'] = old
        expected = [f"'{name}' depends on axioms: "
                    '[propext, Classical.choice, Quot.sound]' for name in names]
        require(output == expected, f'Unexpected solution axioms: {output}')
        print(f'All {len(names)} Solution declarations have exactly the standard axioms.')


def select(pair: str | None, root: Path = ROOT) -> list[Path]:
    configs = discover(root)
    if pair is None:
        require(configs, 'no comparator.json found')
        return configs
    wanted = Path(pair)
    wanted = (wanted if wanted.is_absolute() else Path.cwd() / wanted).resolve()
    if wanted.is_dir():
        wanted = wanted / 'comparator.json'
    chosen = [c for c in configs if c.resolve() == wanted]
    if not chosen:
        by_name = [c for c in configs if pair_label(c, root) == pair]
        chosen = by_name
    require(chosen, f'no comparator pair matches {pair}')
    return chosen


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-build', action='store_true', help='source checks only')
    parser.add_argument('--lake', action='store_true', help='also build the Comparators target')
    parser.add_argument('--pair', metavar='PATH',
                        help='check one pair: its comparator.json, its directory, or its name (root, Leray)')
    args = parser.parse_args()
    try:
        configs = select(args.pair)
        checked = []
        for config in configs:
            label, lines = check_pair(config)
            print(f'Comparator sources PASS ({label}): {lines} Challenge lines.')
            checked.append(config)
        if not args.no_build:
            if args.lake:
                subprocess.run(['python3', 'scripts/build.py', 'Comparators'], cwd=ROOT, check=True)
            for config in checked:
                print(f'Building and checking pair {pair_label(config)}.')
                check_proofs(config)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print(f'Comparator check failed: {error}')
        return 1
    print('All local comparator checks passed.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
