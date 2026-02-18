#!/usr/bin/env python3
"""Tests for the Lean name demangler."""

import unittest
import json
import gzip
import tempfile
import os

from lean_demangle import (
    mangle_string, mangle_name, demangle_body, format_name,
    demangle_lean_name, demangle_lean_name_raw, postprocess_name,
    _parse_hex, _check_disambiguation,
)


class TestStringMangle(unittest.TestCase):
    """Test String.mangle (character-level escaping)."""

    def test_alphanumeric(self):
        self.assertEqual(mangle_string("hello"), "hello")
        self.assertEqual(mangle_string("abc123"), "abc123")

    def test_underscore(self):
        self.assertEqual(mangle_string("a_b"), "a__b")
        self.assertEqual(mangle_string("_"), "__")
        self.assertEqual(mangle_string("__"), "____")

    def test_special_chars(self):
        self.assertEqual(mangle_string("."), "_x2e")
        self.assertEqual(mangle_string("a.b"), "a_x2eb")

    def test_unicode(self):
        self.assertEqual(mangle_string("\u03bb"), "_u03bb")
        self.assertEqual(mangle_string("\U0001d55c"), "_U0001d55c")

    def test_empty(self):
        self.assertEqual(mangle_string(""), "")


class TestNameMangle(unittest.TestCase):
    """Test Name.mangle (hierarchical name mangling)."""

    def test_simple(self):
        self.assertEqual(mangle_name(["Lean", "Meta", "Sym", "main"]),
                         "l_Lean_Meta_Sym_main")

    def test_single_component(self):
        self.assertEqual(mangle_name(["main"]), "l_main")

    def test_numeric_component(self):
        self.assertEqual(
            mangle_name(["_private", "Lean", "Meta", "Basic", 0,
                         "Lean", "Meta", "withMVarContextImp"]),
            "l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp")

    def test_component_with_underscore(self):
        self.assertEqual(mangle_name(["a_b"]), "l_a__b")
        self.assertEqual(mangle_name(["a_b", "c"]), "l_a__b_c")

    def test_disambiguation_digit_start(self):
        self.assertEqual(mangle_name(["0foo"]), "l_000foo")

    def test_disambiguation_escape_start(self):
        self.assertEqual(mangle_name(["a", "x27"]), "l_a_00x27")

    def test_numeric_root(self):
        self.assertEqual(mangle_name([42]), "l_42_")
        self.assertEqual(mangle_name([42, "foo"]), "l_42__foo")

    def test_component_ending_with_underscore(self):
        self.assertEqual(mangle_name(["a_", "b"]), "l_a___00b")

    def test_custom_prefix(self):
        self.assertEqual(mangle_name(["foo"], prefix="lp_pkg_"),
                         "lp_pkg_foo")


class TestDemangleBody(unittest.TestCase):
    """Test demangle_body (the core Name.demangleAux algorithm)."""

    def test_simple(self):
        self.assertEqual(demangle_body("Lean_Meta_Sym_main"),
                         ["Lean", "Meta", "Sym", "main"])

    def test_single(self):
        self.assertEqual(demangle_body("main"), ["main"])

    def test_empty(self):
        self.assertEqual(demangle_body(""), [])

    def test_underscore_in_component(self):
        self.assertEqual(demangle_body("a__b"), ["a_b"])
        self.assertEqual(demangle_body("a__b_c"), ["a_b", "c"])

    def test_numeric_component(self):
        self.assertEqual(demangle_body("foo_42__bar"), ["foo", 42, "bar"])

    def test_numeric_root(self):
        self.assertEqual(demangle_body("42_"), [42])

    def test_numeric_at_end(self):
        self.assertEqual(demangle_body("foo_42_"), ["foo", 42])

    def test_disambiguation_00(self):
        self.assertEqual(demangle_body("a_00x27"), ["a", "x27"])

    def test_disambiguation_00_at_root(self):
        self.assertEqual(demangle_body("000foo"), ["0foo"])

    def test_hex_escape_x(self):
        self.assertEqual(demangle_body("a_x2eb"), ["a.b"])

    def test_hex_escape_u(self):
        self.assertEqual(demangle_body("_u03bb"), ["\u03bb"])

    def test_hex_escape_U(self):
        self.assertEqual(demangle_body("_U0001d55c"), ["\U0001d55c"])

    def test_private_name(self):
        body = "__private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp"
        self.assertEqual(demangle_body(body),
                         ["_private", "Lean", "Meta", "Basic", 0,
                          "Lean", "Meta", "withMVarContextImp"])

    def test_boxed_suffix(self):
        body = "foo___boxed"
        self.assertEqual(demangle_body(body), ["foo", "_boxed"])

    def test_redArg_suffix(self):
        body = "foo_bar___redArg"
        self.assertEqual(demangle_body(body), ["foo", "bar", "_redArg"])

    def test_component_ending_underscore_disambiguation(self):
        self.assertEqual(demangle_body("a___00b"), ["a_", "b"])


class TestRoundTrip(unittest.TestCase):
    """Test that mangle(demangle(x)) == x for various names."""

    def _check_roundtrip(self, components):
        mangled = mangle_name(components, prefix="")
        demangled = demangle_body(mangled)
        self.assertEqual(demangled, components,
                         f"Round-trip failed: {components} -> '{mangled}' -> {demangled}")
        mangled_with_prefix = mangle_name(components, prefix="l_")
        self.assertTrue(mangled_with_prefix.startswith("l_"))
        body = mangled_with_prefix[2:]
        demangled2 = demangle_body(body)
        self.assertEqual(demangled2, components)

    def test_simple_names(self):
        self._check_roundtrip(["Lean", "Meta", "main"])
        self._check_roundtrip(["a"])
        self._check_roundtrip(["Foo", "Bar", "baz"])

    def test_numeric(self):
        self._check_roundtrip(["foo", 0, "bar"])
        self._check_roundtrip([42])
        self._check_roundtrip(["a", 1, "b", 2, "c"])

    def test_underscores(self):
        self._check_roundtrip(["_private"])
        self._check_roundtrip(["a_b", "c_d"])
        self._check_roundtrip(["_at_", "_spec"])

    def test_private_name(self):
        self._check_roundtrip(["_private", "Lean", "Meta", "Basic", 0,
                                "Lean", "Meta", "withMVarContextImp"])

    def test_boxed(self):
        self._check_roundtrip(["Lean", "Meta", "foo", "_boxed"])

    def test_redArg(self):
        self._check_roundtrip(["Lean", "Meta", "foo", "_redArg"])

    def test_specialization(self):
        self._check_roundtrip(["List", "map", "_at_", "Foo", "bar", "_spec", 3])

    def test_lambda(self):
        self._check_roundtrip(["Foo", "bar", "_lambda", 0])
        self._check_roundtrip(["Foo", "bar", "_lambda", 2])

    def test_closed(self):
        self._check_roundtrip(["myConst", "_closed", 0])

    def test_special_chars(self):
        self._check_roundtrip(["a.b"])
        self._check_roundtrip(["\u03bb"])
        self._check_roundtrip(["a", "b\u2192c"])

    def test_disambiguation_cases(self):
        self._check_roundtrip(["a", "x27"])
        self._check_roundtrip(["0foo"])
        self._check_roundtrip(["a_", "b"])

    def test_complex_real_names(self):
        """Names modeled after real Lean compiler output."""
        self._check_roundtrip(
            ["Lean", "MVarId", "withContext", "_at_",
             "_private", "Lean", "Meta", "Sym", 0,
             "Lean", "Meta", "Sym", "BackwardRule", "apply",
             "_spec", 2, "_redArg", "_lambda", 0, "_boxed"])


class TestDemangleRaw(unittest.TestCase):
    """Test demangle_lean_name_raw (exact demangling, no postprocessing)."""

    def test_l_prefix(self):
        self.assertEqual(
            demangle_lean_name_raw("l_Lean_Meta_Sym_main"),
            "Lean.Meta.Sym.main")

    def test_l_prefix_private(self):
        result = demangle_lean_name_raw(
            "l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp")
        self.assertEqual(result,
                         "_private.Lean.Meta.Basic.0.Lean.Meta.withMVarContextImp")

    def test_l_prefix_boxed(self):
        result = demangle_lean_name_raw("l_foo___boxed")
        self.assertEqual(result, "foo._boxed")

    def test_l_prefix_redArg(self):
        result = demangle_lean_name_raw(
            "l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg")
        self.assertEqual(
            result,
            "_private.Lean.Meta.Basic.0.Lean.Meta.withMVarContextImp._redArg")

    def test_lean_main(self):
        self.assertEqual(demangle_lean_name_raw("_lean_main"), "[lean] main")

    def test_non_lean_names(self):
        self.assertEqual(demangle_lean_name_raw("printf"), "printf")
        self.assertEqual(demangle_lean_name_raw("malloc"), "malloc")
        self.assertEqual(demangle_lean_name_raw("lean_apply_5"), "lean_apply_5")
        self.assertEqual(demangle_lean_name_raw(""), "")

    def test_init_prefix(self):
        result = demangle_lean_name_raw("_init_l_Lean_Meta_foo")
        self.assertEqual(result, "[init] Lean.Meta.foo")

    def test_lp_prefix_simple(self):
        mangled = mangle_name(["Lean", "Meta", "foo"], prefix="lp_std_")
        self.assertEqual(mangled, "lp_std_Lean_Meta_foo")
        result = demangle_lean_name_raw(mangled)
        self.assertEqual(result, "Lean.Meta.foo (std)")

    def test_lp_prefix_underscore_pkg(self):
        pkg_mangled = mangle_string("my_pkg")
        self.assertEqual(pkg_mangled, "my__pkg")
        mangled = mangle_name(["Lean", "Meta", "foo"],
                              prefix=f"lp_{pkg_mangled}_")
        self.assertEqual(mangled, "lp_my__pkg_Lean_Meta_foo")
        result = demangle_lean_name_raw(mangled)
        self.assertEqual(result, "Lean.Meta.foo (my_pkg)")

    def test_lp_prefix_private_decl(self):
        mangled = mangle_name(
            ["_private", "X", 0, "Y", "foo"], prefix="lp_pkg_")
        self.assertEqual(mangled, "lp_pkg___private_X_0__Y_foo")
        result = demangle_lean_name_raw(mangled)
        self.assertEqual(result, "_private.X.0.Y.foo (pkg)")

    def test_complex_specialization(self):
        components = [
            "Lean", "MVarId", "withContext", "_at_",
            "_private", "Lean", "Meta", "Sym", 0,
            "Lean", "Meta", "Sym", "BackwardRule", "apply",
            "_spec", 2, "_redArg", "_lambda", 0, "_boxed"
        ]
        mangled = mangle_name(components)
        result = demangle_lean_name_raw(mangled)
        expected = format_name(components)
        self.assertEqual(result, expected)

    def test_cold_suffix(self):
        result = demangle_lean_name_raw("l_Lean_Meta_foo___redArg.cold.1")
        self.assertEqual(result, "Lean.Meta.foo._redArg .cold.1")

    def test_cold_suffix_plain(self):
        result = demangle_lean_name_raw("l_Lean_Meta_foo.cold")
        self.assertEqual(result, "Lean.Meta.foo .cold")

    def test_initialize_no_pkg(self):
        result = demangle_lean_name_raw("initialize_Init_Control_Basic")
        self.assertEqual(result, "[module_init] Init.Control.Basic")

    def test_initialize_with_l_prefix(self):
        result = demangle_lean_name_raw("initialize_l_Lean_Meta_foo")
        self.assertEqual(result, "[module_init] Lean.Meta.foo")

    def test_never_crashes(self):
        """Demangling should never raise, just return the original."""
        weird_inputs = [
            "", "l_", "lp_", "lp_x", "_init_", "initialize_",
            "l_____", "lp____", "l_00", "l_0",
            "some random string", "l_ space",
        ]
        for inp in weird_inputs:
            result = demangle_lean_name_raw(inp)
            self.assertIsInstance(result, str)


class TestPostprocess(unittest.TestCase):
    """Test postprocess_name (human-friendly suffix folding, etc.)."""

    def test_no_change(self):
        self.assertEqual(postprocess_name(["Lean", "Meta", "main"]),
                         "Lean.Meta.main")

    def test_boxed(self):
        self.assertEqual(postprocess_name(["foo", "_boxed"]),
                         "foo [boxed]")

    def test_redArg(self):
        self.assertEqual(postprocess_name(["foo", "bar", "_redArg"]),
                         "foo.bar [arity\u2193]")

    def test_lambda_separate(self):
        # _lam as separate component + numeric index
        self.assertEqual(postprocess_name(["foo", "_lam", 0]),
                         "foo [\u03bb]")

    def test_lambda_indexed(self):
        # _lam_0 as single string (appendIndexAfter)
        self.assertEqual(postprocess_name(["foo", "_lam_0"]),
                         "foo [\u03bb]")
        self.assertEqual(postprocess_name(["foo", "_lambda_2"]),
                         "foo [\u03bb]")

    def test_lambda_boxed(self):
        # _lam_0 followed by _boxed
        self.assertEqual(
            postprocess_name(["Lean", "Meta", "Simp", "simpLambda",
                              "_lam_0", "_boxed"]),
            "Lean.Meta.Simp.simpLambda [boxed, \u03bb]")

    def test_closed(self):
        self.assertEqual(postprocess_name(["myConst", "_closed", 3]),
                         "myConst [closed]")

    def test_closed_indexed(self):
        self.assertEqual(postprocess_name(["myConst", "_closed_0"]),
                         "myConst [closed]")

    def test_multiple_suffixes(self):
        self.assertEqual(postprocess_name(["foo", "_redArg", "_boxed"]),
                         "foo [boxed, arity\u2193]")

    def test_redArg_lam(self):
        # _redArg followed by _lam_0 (issue #4)
        self.assertEqual(
            postprocess_name(["Lean", "profileitIOUnsafe",
                              "_redArg", "_lam_0"]),
            "Lean.profileitIOUnsafe [\u03bb, arity\u2193]")

    def test_private_name(self):
        self.assertEqual(
            postprocess_name(["_private", "Lean", "Meta", "Basic", 0,
                              "Lean", "Meta", "withMVarContextImp"]),
            "Lean.Meta.withMVarContextImp [private]")

    def test_private_with_suffix(self):
        self.assertEqual(
            postprocess_name(["_private", "Lean", "Meta", "Basic", 0,
                              "Lean", "Meta", "foo", "_redArg"]),
            "Lean.Meta.foo [arity\u2193, private]")

    def test_hygienic_strip(self):
        self.assertEqual(
            postprocess_name(["Lean", "Meta", "foo", "_@", "Lean", "Meta",
                              "_hyg", 42]),
            "Lean.Meta.foo")

    def test_specialization(self):
        self.assertEqual(
            postprocess_name(["List", "map", "_at_", "Foo", "bar",
                              "_spec", 3]),
            "List.map spec at Foo.bar")

    def test_specialization_with_suffix(self):
        # Base suffix _boxed appears in [flags] before spec at
        self.assertEqual(
            postprocess_name(["Lean", "MVarId", "withContext", "_at_",
                              "Foo", "bar", "_spec", 2, "_boxed"]),
            "Lean.MVarId.withContext [boxed] spec at Foo.bar")

    def test_spec_context_with_flags(self):
        # Compiler suffixes in spec context become context flags
        self.assertEqual(
            postprocess_name(["Lean", "Meta", "foo", "_at_",
                              "Lean", "Meta", "bar", "_elam_1", "_redArg",
                              "_spec", 2]),
            "Lean.Meta.foo spec at Lean.Meta.bar[\u03bb, arity\u2193]")

    def test_spec_context_flags_dedup(self):
        # Duplicate flag labels are deduplicated
        self.assertEqual(
            postprocess_name(["f", "_at_",
                              "g", "_lam_0", "_elam_1", "_redArg",
                              "_spec", 1]),
            "f spec at g[\u03bb, arity\u2193]")

    def test_multiple_at(self):
        # Multiple _at_ entries become separate spec at clauses
        self.assertEqual(
            postprocess_name(["f", "_at_", "g", "_spec", 1,
                              "_at_", "h", "_spec", 2]),
            "f spec at g spec at h")

    def test_multiple_at_with_flags(self):
        # Multiple spec at with flags on base and contexts
        self.assertEqual(
            postprocess_name(["f", "_at_", "g", "_redArg", "_spec", 1,
                              "_at_", "h", "_lam_0", "_spec", 2,
                              "_boxed"]),
            "f [boxed] spec at g[arity\u2193] spec at h[\u03bb]")

    def test_base_flags_before_spec(self):
        # Base trailing suffixes appear in [flags] before spec at
        self.assertEqual(
            postprocess_name(["f", "_at_", "g", "_spec", 1, "_lam_0"]),
            "f [\u03bb] spec at g")

    def test_spec_context_strip_spec_suffixes(self):
        # spec_0 in context should be stripped
        self.assertEqual(
            postprocess_name(["Lean", "Meta", "transformWithCache", "visit",
                              "_at_",
                              "_private", "Lean", "Meta", "Transform", 0,
                              "Lean", "Meta", "transform",
                              "Lean", "Meta", "Sym", "unfoldReducible",
                              "spec_0", "spec_0",
                              "_spec", 1]),
            "Lean.Meta.transformWithCache.visit "
            "spec at Lean.Meta.transform.Lean.Meta.Sym.unfoldReducible")

    def test_spec_context_strip_private(self):
        # _private in spec context should be stripped
        self.assertEqual(
            postprocess_name(["Array", "mapMUnsafe", "map", "_at_",
                              "_private", "Lean", "Meta", "Transform", 0,
                              "Lean", "Meta", "transformWithCache", "visit",
                              "_spec", 1]),
            "Array.mapMUnsafe.map "
            "spec at Lean.Meta.transformWithCache.visit")

    def test_empty(self):
        self.assertEqual(postprocess_name([]), "")


class TestDemangleHumanFriendly(unittest.TestCase):
    """Test demangle_lean_name (human-friendly output)."""

    def test_simple(self):
        self.assertEqual(demangle_lean_name("l_Lean_Meta_main"),
                         "Lean.Meta.main")

    def test_boxed(self):
        self.assertEqual(demangle_lean_name("l_foo___boxed"),
                         "foo [boxed]")

    def test_redArg(self):
        self.assertEqual(demangle_lean_name("l_foo___redArg"),
                         "foo [arity\u2193]")

    def test_private(self):
        self.assertEqual(
            demangle_lean_name(
                "l___private_Lean_Meta_Basic_0__Lean_Meta_foo"),
            "Lean.Meta.foo [private]")

    def test_private_with_redArg(self):
        self.assertEqual(
            demangle_lean_name(
                "l___private_Lean_Meta_Basic_0__Lean_Meta_foo___redArg"),
            "Lean.Meta.foo [arity\u2193, private]")

    def test_cold_with_suffix(self):
        self.assertEqual(
            demangle_lean_name("l_Lean_Meta_foo___redArg.cold.1"),
            "Lean.Meta.foo [arity\u2193] .cold.1")

    def test_lean_apply(self):
        self.assertEqual(demangle_lean_name("lean_apply_5"), "<apply/5>")
        self.assertEqual(demangle_lean_name("lean_apply_12"), "<apply/12>")

    def test_lean_apply_raw_unchanged(self):
        self.assertEqual(demangle_lean_name_raw("lean_apply_5"),
                         "lean_apply_5")

    def test_init_private(self):
        self.assertEqual(
            demangle_lean_name(
                "_init_l___private_X_0__Y_foo"),
            "[init] Y.foo [private]")

    def test_complex_specialization(self):
        components = [
            "Lean", "MVarId", "withContext", "_at_",
            "_private", "Lean", "Meta", "Sym", 0,
            "Lean", "Meta", "Sym", "BackwardRule", "apply",
            "_spec", 2, "_redArg", "_lambda", 0, "_boxed"
        ]
        mangled = mangle_name(components)
        result = demangle_lean_name(mangled)
        # Base: Lean.MVarId.withContext with trailing _redArg, _lambda 0, _boxed
        # Spec context: Lean.Meta.Sym.BackwardRule.apply (private stripped)
        self.assertEqual(
            result,
            "Lean.MVarId.withContext [boxed, \u03bb, arity\u2193] "
            "spec at Lean.Meta.Sym.BackwardRule.apply")

    def test_non_lean_unchanged(self):
        self.assertEqual(demangle_lean_name("printf"), "printf")
        self.assertEqual(demangle_lean_name("malloc"), "malloc")
        self.assertEqual(demangle_lean_name(""), "")


class TestDemangleProfile(unittest.TestCase):
    """Test the profile rewriter."""

    def _make_profile_shared(self, strings):
        """Create a profile with shared.stringArray (newer format)."""
        return {
            "meta": {"version": 28},
            "libs": [],
            "shared": {
                "stringArray": list(strings),
            },
            "threads": [{
                "name": "main",
                "pid": "1",
                "tid": 1,
                "funcTable": {
                    "name": list(range(len(strings))),
                    "isJS": [False] * len(strings),
                    "relevantForJS": [False] * len(strings),
                    "resource": [-1] * len(strings),
                    "fileName": [None] * len(strings),
                    "lineNumber": [None] * len(strings),
                    "columnNumber": [None] * len(strings),
                    "length": len(strings),
                },
                "frameTable": {"length": 0},
                "stackTable": {"length": 0},
                "samples": {"length": 0},
                "markers": {"length": 0},
                "resourceTable": {"length": 0},
                "nativeSymbols": {"length": 0},
            }],
            "pages": [],
            "counters": [],
        }

    def _make_profile_per_thread(self, strings):
        """Create a profile with per-thread stringArray (samply format)."""
        return {
            "meta": {"version": 28},
            "libs": [],
            "threads": [{
                "name": "main",
                "pid": "1",
                "tid": 1,
                "stringArray": list(strings),
                "funcTable": {
                    "name": list(range(len(strings))),
                    "isJS": [False] * len(strings),
                    "relevantForJS": [False] * len(strings),
                    "resource": [-1] * len(strings),
                    "fileName": [None] * len(strings),
                    "lineNumber": [None] * len(strings),
                    "columnNumber": [None] * len(strings),
                    "length": len(strings),
                },
                "frameTable": {"length": 0},
                "stackTable": {"length": 0},
                "samples": {"length": 0},
                "markers": {"length": 0},
                "resourceTable": {"length": 0},
                "nativeSymbols": {"length": 0},
            }],
            "pages": [],
            "counters": [],
        }

    def test_profile_rewrite_shared(self):
        from lean_demangle_profile import rewrite_profile
        strings = [
            "l_Lean_Meta_Sym_main",
            "printf",
            "lean_apply_5",
            "l___private_Lean_Meta_Basic_0__Lean_Meta_foo",
        ]
        profile = self._make_profile_shared(strings)
        rewrite_profile(profile)
        sa = profile["shared"]["stringArray"]
        self.assertEqual(sa[0], "Lean.Meta.Sym.main")
        self.assertEqual(sa[1], "printf")
        self.assertEqual(sa[2], "<apply/5>")
        self.assertEqual(sa[3], "Lean.Meta.foo [private]")

    def test_profile_rewrite_per_thread(self):
        from lean_demangle_profile import rewrite_profile
        strings = [
            "l_Lean_Meta_Sym_main",
            "printf",
            "lean_apply_5",
            "l___private_Lean_Meta_Basic_0__Lean_Meta_foo",
        ]
        profile = self._make_profile_per_thread(strings)
        count = rewrite_profile(profile)
        sa = profile["threads"][0]["stringArray"]
        self.assertEqual(sa[0], "Lean.Meta.Sym.main")
        self.assertEqual(sa[1], "printf")
        self.assertEqual(sa[2], "<apply/5>")
        self.assertEqual(sa[3], "Lean.Meta.foo [private]")
        self.assertEqual(count, 3)

    def test_profile_json_roundtrip(self):
        from lean_demangle_profile import process_profile_file
        strings = ["l_Lean_Meta_main", "malloc"]
        profile = self._make_profile_shared(strings)

        with tempfile.NamedTemporaryFile(mode='w', suffix='.json',
                                         delete=False) as f:
            json.dump(profile, f)
            inpath = f.name

        outpath = inpath.replace('.json', '-demangled.json')
        try:
            process_profile_file(inpath, outpath)
            with open(outpath) as f:
                result = json.load(f)
            self.assertEqual(result["shared"]["stringArray"][0],
                             "Lean.Meta.main")
            self.assertEqual(result["shared"]["stringArray"][1], "malloc")
        finally:
            os.unlink(inpath)
            if os.path.exists(outpath):
                os.unlink(outpath)

    def test_profile_gzip_roundtrip(self):
        from lean_demangle_profile import process_profile_file
        strings = ["l_Lean_Meta_main", "malloc"]
        profile = self._make_profile_shared(strings)

        with tempfile.NamedTemporaryFile(suffix='.json.gz',
                                         delete=False) as f:
            with gzip.open(f, 'wt') as gz:
                json.dump(profile, gz)
            inpath = f.name

        outpath = inpath.replace('.json.gz', '-demangled.json.gz')
        try:
            process_profile_file(inpath, outpath)
            with gzip.open(outpath, 'rt') as f:
                result = json.load(f)
            self.assertEqual(result["shared"]["stringArray"][0],
                             "Lean.Meta.main")
        finally:
            os.unlink(inpath)
            if os.path.exists(outpath):
                os.unlink(outpath)


if __name__ == '__main__':
    unittest.main()
