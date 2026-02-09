inductive Foo (f: Fin n): Nat → Prop
| mk: Foo f f.val
theorem foo {f: Fin n}: Foo f (no_index f.val) := .mk
example (hf: f < n): Foo ⟨f, hf⟩ f := by simp only [foo]
example  (f: Fin n): Foo  f f.val  := by simp only [foo]
