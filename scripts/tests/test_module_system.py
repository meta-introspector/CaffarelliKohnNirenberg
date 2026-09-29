#!/usr/bin/env python3
# Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
# Released under Apache 2.0 license.
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import check_axioms  # noqa: E402
import check_comparators  # noqa: E402
import check_rules  # noqa: E402
import dup_decls  # noqa: E402
import tempfile  # noqa: E402

HEAD = "-- c\n\nmodule\n\n"


class ImportTests(unittest.TestCase):
    def test_qualified_imports(self):
        text = HEAD + ("public import A.B\nimport C\npublic meta import D\n"
                       "import all E.F\n  -- import Fake\n/- import Nope -/\n")
        self.assertEqual(check_axioms.imported_modules(text), ["A.B", "C", "D", "E.F"])


class DeclTests(unittest.TestCase):
    def decls(self, body):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "M.lean").write_text(HEAD + body)
            return check_axioms.public_declarations(root, root / "M.lean")

    def test_expose_public_section_and_namespace(self):
        body = ("@[expose] public section\nnamespace CKN\n"
                "public theorem foo : True := trivial\n"
                "private noncomputable def bar : Nat := 0\n"
                "public noncomputable def baz : Nat := 0\n"
                "end CKN\n")
        self.assertEqual(self.decls(body), ["CKN.foo", "CKN.baz"])

    def test_section_left_open_and_public_noncomputable_section(self):
        body = "public noncomputable section\nnamespace A\ntheorem t : True := trivial\nend A\ndef u := 0\n"
        self.assertEqual(self.decls(body), ["A.t", "u"])

    def test_decl_regex_modifiers(self):
        for line in ["public theorem x", "private noncomputable def x", "public noncomputable def x",
                     "noncomputable public def x", "@[simp] public lemma x", "public meta def x"]:
            self.assertIsNotNone(check_axioms.DECL.match(line), line)
        self.assertEqual(check_axioms.DECL.match("private noncomputable def x").group(1), "private")

    def test_dup_decls_lexer_sees_public(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "M.lean").write_text(HEAD + "public section\nnamespace N\npublic def a := 0\nend N\n")
            names = [x.name for x in dup_decls.top_level_declarations(root, root / "M.lean")]
            self.assertEqual(names, ["N.a"])


class ModuleRuleTests(unittest.TestCase):
    def test_rule(self):
        f = check_rules.module_rule_errors
        self.assertEqual(f("CKN/A.lean", "-- c\n/-- d -/\n\nmodule\n"), [])
        self.assertTrue(f("CKN/A.lean", "-- c\nimport Mathlib\n"))
        self.assertTrue(f("CKN/A.lean", "-- module\nnamespace X\n"))
        self.assertEqual(f("lakefile.lean", "import Lake\n"), [])
        self.assertTrue(f("CKN/A.lean", "module\n" + "\n" * 10000))
        self.assertEqual(f("CKN/A.lean", "module\n" + "\n" * 9990), [])


class ComparatorTests(unittest.TestCase):
    def test_imports(self):
        ok = check_comparators.challenge_imports_only_mathlib
        self.assertTrue(ok(HEAD + "public import Mathlib.Foo\nimport Mathlib\n"))
        self.assertFalse(ok(HEAD + "public import Mathlib.Foo\npublic import CKN.X\n"))
        self.assertFalse(ok(HEAD + "import all CKN.X\n"))
        self.assertFalse(ok(HEAD + "public meta import CKN.X\n"))
        self.assertFalse(ok(HEAD + "import MathlibFoo\n"))
        self.assertFalse(ok(HEAD))

    def test_module_header(self):
        h = check_comparators.has_module_header
        self.assertTrue(h(HEAD + "import Mathlib\n"))
        self.assertFalse(h("import Mathlib\n"))


class CharLiteralMaskTest(unittest.TestCase):
    def test_tsum_prime_is_not_a_char_literal(self):
        import check_axioms
        text = "theorem a : (∑' k : ℕ, f k) = 0 := by\n  simp\ntheorem b : True := trivial\n"
        self.assertIn("theorem b", check_axioms.strip_comments(text))

    def test_char_literals_are_masked(self):
        import check_axioms
        masked = check_axioms.strip_comments("def c : Char := 'a'\ndef d : Char := '\\n'\n")
        self.assertNotIn("'a'", masked)
        self.assertIn("def d", masked)


if __name__ == "__main__":
    unittest.main()
