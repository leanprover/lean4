import Lean
/-!
Tests that Verso docstrings on `class` declarations can use the class as a type class.
See https://github.com/leanprover/lean4/issues/11651
-/
set_option doc.verso true



/--
{name}`Foo` is a type class.

```lean
instance : Foo := ⟨0, 1⟩
example [Foo] : Unit := ()
example : Nat := Foo.x
```
-/
class Foo where
  /--
  Docs!
  ```lean

  def x [Foo] : String := "abc"
  /--
  error: failed to synthesize instance of type class
    Foo

  Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
  -/
  #guard_msgs (whitespace := lax) in
  #eval x
  /-- info: "abc" -/
  #guard_msgs in
  #eval have : Foo := .mk 0 1; x
  ```
  -/
  mk ::
  x : Nat
  /--
  Uses {name}`Foo` as a class:

  ```lean
  example [Foo] : Nat := Foo.y
  ```
  -/
  y : Nat


open Lean Elab Command in
def printVersoDocstring (name : Name) : CommandElabM Unit := do
  match (← findInternalDocString? (← getEnv) name) with
  | none => IO.println s!"No docstring for {name}"
  | some (.inl md) => IO.println s!"Markdown:\n{md}"
  | some (.inr v) => IO.println (repr v.text); IO.println (repr v.subsections)

/--
info: #[Lean.Doc.Block.para
    #[Lean.Doc.Inline.other
        { name := `Lean.Doc.Data.Const val := Dynamic.mk `Lean.Doc.Data.Const _ }
        #[Lean.Doc.Inline.code "Foo"],
      Lean.Doc.Inline.text " is a type class."],
  Lean.Doc.Block.other
    { name := `Lean.Doc.Data.LeanBlock val := Dynamic.mk `Lean.Doc.Data.LeanBlock _ }
    #[Lean.Doc.Block.code "instance : Foo := ⟨0, 1⟩\nexample [Foo] : Unit := ()\nexample : Nat := Foo.x\n"]]
#[]
-/
#guard_msgs in
#eval printVersoDocstring ``Foo

/-- info: No docstring for Foo.x -/
#guard_msgs in
#eval printVersoDocstring ``Foo.x

/--
info: #[Lean.Doc.Block.para
    #[Lean.Doc.Inline.text "Uses ",
      Lean.Doc.Inline.other
        { name := `Lean.Doc.Data.Const val := Dynamic.mk `Lean.Doc.Data.Const _ }
        #[Lean.Doc.Inline.code "Foo"],
      Lean.Doc.Inline.text " as a class:"],
  Lean.Doc.Block.other
    { name := `Lean.Doc.Data.LeanBlock val := Dynamic.mk `Lean.Doc.Data.LeanBlock _ }
    #[Lean.Doc.Block.code "example [Foo] : Nat := Foo.y\n"]]
#[]
-/
#guard_msgs in
#eval printVersoDocstring ``Foo.y
