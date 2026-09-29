#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import check_comparators as cc  # noqa: E402

CONFIG = {
    'challenge_module': 'comparators.T.Challenge', 'solution_module': 'comparators.T.Solution',
    'theorem_names': ['CKNTChallenge.foo'], 'definition_names': [],
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'enable_nanoda': True,
}
HEAD = 'module\n\npublic import Mathlib.Data.Nat.Defs\n'
BODY = ('@[expose] public section\n\nset_option autoImplicit false\n\nnamespace CKNTChallenge\n\n'
        '/-- A definition. -/\ndef D : Nat := 0\n\n')
THM = '/-- Foo. -/\ntheorem foo : D = 0 :=\n  '


def make(root: Path, config=CONFIG, challenge=None, solution=None) -> Path:
    directory = root / 'comparators' / 'T'
    directory.mkdir(parents=True)
    (directory / 'comparator.json').write_text(json.dumps(config))
    (directory / 'Challenge.lean').write_text(
        challenge or HEAD + BODY + THM + 'by sorry\n\nend CKNTChallenge\n')
    (directory / 'Solution.lean').write_text(
        solution or HEAD + 'public import CKN.Foo\n' + BODY.replace(
            'public section\n', 'public section\n\nopen CKN\n')
        + 'theorem aux : True := trivial\n\n' + THM + 'rfl\n\nend CKNTChallenge\n')
    return directory / 'comparator.json'


class DiscoveryTests(unittest.TestCase):
    def test_discover_and_select(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / 'comparator.json').write_text('{}')
            config = make(root)
            self.assertEqual(cc.discover(root), [root / 'comparator.json', config])
            self.assertEqual([cc.pair_label(c, root) for c in cc.discover(root)], ['root', 'T'])
            self.assertEqual(cc.select('T', root), [config])
            self.assertEqual(cc.select(str(config), root), [config])
            self.assertEqual(cc.select(str(config.parent), root), [config])
            with self.assertRaises(ValueError):
                cc.select('Nope', root)

    def test_no_root_pair(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            config = make(root)
            self.assertEqual(cc.discover(root), [config])


class PairTests(unittest.TestCase):
    def check(self, **kw):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            return cc.check_pair(make(root, **kw), root)

    def fails(self, message, **kw):
        with self.assertRaisesRegex(ValueError, message):
            self.check(**kw)

    def test_pass(self):
        label, lines = self.check()
        self.assertEqual(label, 'T')
        self.assertGreater(lines, 0)

    def test_challenge_not_mathlib_only(self):
        self.fails('only Mathlib', challenge=HEAD.replace('Mathlib.Data.Nat.Defs', 'CKN.Foo')
                   + BODY + THM + 'by sorry\n\nend CKNTChallenge\n',
                   solution=HEAD.replace('Mathlib.Data.Nat.Defs', 'CKN.Foo') + BODY + THM + 'rfl\n\nend CKNTChallenge\n')

    def test_challenge_stray_import(self):
        self.fails('only Mathlib', challenge=HEAD + 'import Other\n' + BODY + THM + 'by sorry\n\nend CKNTChallenge\n')

    def test_module_header(self):
        self.fails('module', challenge=HEAD.replace('module\n', '') + BODY + THM + 'by sorry\n\nend CKNTChallenge\n')

    def test_statement_differs(self):
        good = HEAD + 'public import CKN.Foo\n' + BODY + '/-- Foo. -/\ntheorem foo : D = 1 :=\n  rfl\n\nend CKNTChallenge\n'
        self.fails('statement of foo differs', solution=good)

    def test_definition_differs(self):
        sol = (HEAD + 'public import CKN.Foo\n' + BODY.replace('Nat := 0', 'Nat := 1')
               + THM + 'rfl\n\nend CKNTChallenge\n')
        self.fails('verbatim', solution=sol)

    def test_solution_sorry(self):
        sol = HEAD + 'public import CKN.Foo\n' + BODY + THM + 'by sorry\n\nend CKNTChallenge\n'
        self.fails('placeholder', solution=sol)

    def test_bad_config(self):
        self.fails('theorem_names', config={**CONFIG, 'theorem_names': ['Other.foo']})
        self.fails('fields', config={**CONFIG, 'extra': 1})
        self.fails('NanoDa', config={**CONFIG, 'enable_nanoda': False})

    def test_wrong_module(self):
        self.fails('must select', config={**CONFIG, 'challenge_module': 'comparators.Challenge'})


class RepositoryTests(unittest.TestCase):
    def test_real_pairs_pass(self):
        configs = cc.discover()
        self.assertGreaterEqual(len(configs), 2)
        for config in configs:
            cc.check_pair(config)


if __name__ == '__main__':
    unittest.main()
