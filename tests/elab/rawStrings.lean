/-!
# Testing raw string literals

Implemented in PR #2929 for issue #1422.
-/

/-!
Empty raw string
-/
example : r"" = "" := rfl

/-!
Empty raw string with at least one `#`
-/
example : r#""# = "" := rfl

/-!
A nonempty raw string
-/
example : r"hi" = "hi" := rfl

/-!
A nonempty raw string with at least one `#`
-/
example : r#"hi"# = "hi" := rfl

/-!
A nonempty raw string with `#`, testing embedded `"`'s
-/
example : r#""hello""# = "\"hello\"" := rfl

/-!
A nonempty raw string with `#`, testing embedded `"`'s, one not at the end of the string
-/
example : r#""hello" said the world"# = "\"hello\" said the world" := rfl

/-!
A nonempty raw string for just `"`
-/
example : r#"""# = "\"" := rfl

/-!
A raw string with a `\`, which does not get interpreted as an escape
-/
example : r"\n" = "\\n" := rfl

/-!
A raw string for just `\`, and it doesn't escape the final `"`
-/
example : r"\" = "\\" := rfl

/-!
A raw string with `#` inside, testing that the first `"` doesn't get double-interpreted
as both the start and end.
-/
example : r#"#"# = "#" := rfl

/-!
Testing using `##` raw strings to allow `"#` inside the string.
-/
example : r##"need two #'s in "# to close"## = "need two #'s in \"# to close" := rfl

/-!
From Rust reference
-/
example : r##"foo #"# bar"## = "foo #\"# bar" := rfl

/-!
Testing that we are conservative when counting closing `#`s.
-/
infix:100 " # " => Prod.mk
example : r#"a"##"b" = ("a", "b") := rfl
