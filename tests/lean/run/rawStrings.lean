example : r"" = "" := rfl
example : r#""# = "" := rfl
example : r"hi" = "hi" := rfl
example : r#"hi"# = "hi" := rfl
example : r#""hello""# = "\"hello\"" := rfl
example : r#""hello" said the world"# = "\"hello\" said the world" := rfl
example : r#"""# = "\"" := rfl
example : r"\n" = "\\n" := rfl
example : r"\" = "\\" := rfl
example : r#"#"# = "#" := rfl
example : r##"need two #'s in "# to close"## = "need two #'s in \"# to close" := rfl
example : r##"foo #"# bar"## = "foo #\"# bar" := rfl

infix:100 " # " => Prod.mk

example : r#"a"##"b" = ("a", "b") := rfl
