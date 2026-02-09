import Lean
/-!
# Verso Docstrings on `where`-clause declarations

This test checks that Verso docstrings work correctly on declarations in a `where` clause.

-/

section

open Lean Elab Command

deriving instance Repr for VersoDocString

def printVersoDocstring (x : Name) : CommandElabM Unit := do
  let docs? ← findInternalDocString? (← getEnv) x
  match docs? with
  | none => throwError m!"No docstring for {.ofConstName x}"
  | some (.inl md) => throwError m!"Only a Markdown docstring for {.ofConstName x}:\n{md}"
  | some (.inr v) => IO.println (repr v)

end

set_option doc.verso true

/-- This docstring works. -/
def foo := bar
  where
  /-- This docstring should also work. -/
  bar := 37

-- Verify the docstrings are present
/--
info: { text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "This docstring works. "]], subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``foo

/--
info: { text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "This docstring should also work. "]], subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``foo.bar


-- Test with multiple where declarations
/-- Outer function. -/
def outer := inner1 + inner2
  where
  /-- First inner function. -/
  inner1 := 10
  /-- Second inner function is {lean}`outer.inner2`. -/
  inner2 := 20

/--
info: { text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "First inner function. "]], subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``outer.inner1

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Second inner function is ",
                Lean.Doc.Inline.other
                  { name := `Lean.Doc.Data.LeanTerm val := Dynamic.mk `Lean.Doc.Data.LeanTerm _ }
                  #[Lean.Doc.Inline.code "outer.inner2"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``outer.inner2


/-- Function with type annotation. -/
def withType := helper
  where
  /-- What is the type of {name (full := withType.helper)}`helper`?. -/
  helper : Nat := 42

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "What is the type of ",
                Lean.Doc.Inline.other
                  { name := `Lean.Doc.Data.Const val := Dynamic.mk `Lean.Doc.Data.Const _ }
                  #[Lean.Doc.Inline.code "helper"],
                Lean.Doc.Inline.text "?. "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withType.helper
