set_option doc.verso true

/-!
This test checks that the error produced for a docstring without a corresponding declaration is a parser error instead of an internal error or panic from elaborating partial syntax.
-/

/--
foo
-/
