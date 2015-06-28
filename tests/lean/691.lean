theorem foo : Type₁ := unit

example : foo = unit :=
by unfold foo

example : foo = unit :=
by unfold [foo]

example : foo = unit :=
by rewrite [↑foo]

example : foo = unit :=
by rewrite [↑[foo] ]
