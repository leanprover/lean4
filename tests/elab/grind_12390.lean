variable {α β : Type}

axiom foo (f : α → β) : β

axiom fooProp : β → Prop

axiom fooProp_foo {f : α → β} : fooProp (foo (fun x ↦ f x))
axiom fooProp_foo' {f : α → β} : fooProp (foo f)

attribute [grind ←] fooProp_foo -- should work

example {f : α → β} : fooProp (foo f) := by grind -- succeeds, using `fooProp_foo`

/--
info: Try these:
  [apply] grind only [← fooProp_foo]
  [apply] grind => instantiate only [← fooProp_foo]
-/
#guard_msgs in
example {f : α → β} : fooProp (foo f) := by grind? -- succeeds, using `fooProp_foo`

attribute [grind ←] fooProp_foo' -- succeeds

example {f : α → β} : fooProp (foo f) := by grind
