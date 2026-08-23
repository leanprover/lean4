import Lean
/-!
# Verso docstrings on local declarations with parameters

This test checks that Verso docstrings work correctly on declarations in a `where` clause or
`let rec`, including ones whose parameters are written as unbracketed identifiers or `_` rather
than parenthesized binders.

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
                  ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _)
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
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.Const _) #[Lean.Doc.Inline.code "helper"],
                Lean.Doc.Inline.text "?. "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withType.helper


-- Inner definitions whose parameters are written as bare identifiers rather
-- than parenthesized binders must also accept Verso docstrings.

-- Bare parameter with a return-type annotation
/-- Outer 1. -/
def withParam := go 1
  where
  /-- Returns {lean}`n`. -/
  go n : Nat := n

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withParam.go


-- Bare parameter with no return-type annotation
/-- Outer 2. -/
def withParamNoType := go 1
  where
  /-- Returns {lean}`n`. -/
  go n := n

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withParamNoType.go


-- Multiple bare parameters
/-- Outer 3. -/
def withParams := go 1 2
  where
  /-- Sums {lean}`n` and {lean}`m`. -/
  go n m := n + m

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Sums ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n"],
                Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "m"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withParams.go


-- Mix of parenthesized and bare parameters
/-- Outer 4. -/
def withMixedParams := go 1 2
  where
  /-- Sums {lean}`n` and {lean}`m`. -/
  go (n : Nat) m := n + m

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Sums ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n"],
                Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "m"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withMixedParams.go


-- `let rec` with a bare parameter
/-- Outer 5. -/
def withLetRec : Nat :=
  let rec /-- Returns {lean}`n`. -/ go n := n
  go 1

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withLetRec.go


-- Bare parameters on a top-level definition, with the parameter type inferred
-- from the body.

/-- Returns {lean}`x`. -/
def bareOne x := x + 5

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``bareOne


/-- Sums {lean}`x` and {lean}`y`. -/
def bareMany x y := x + y + (0 : Nat)

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Sums ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "y"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``bareMany


/-- Sums {lean}`x` and {lean}`y`. -/
def bareMixed (x : Nat) y := x + y

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Sums ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "y"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``bareMixed


-- A bare parameter may also be a hole `_`.

/-- Outer 6. -/
def withHole := go 1
  where
  /-- Hole parameter. -/
  go _ := 5

/--
info: { text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "Hole parameter. "]], subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withHole.go


/-- Outer 7. -/
def withIdentHole := go 1 2
  where
  /-- Returns {lean}`x`. -/
  go x _ := x

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``withIdentHole.go


-- Bracketed binders: default values, tactic defaults, named instance binders, and strict implicits.

/-- Returns {lean}`x`. -/
def binderDefault (x : Nat := 0) := x

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``binderDefault


/-- Returns {lean}`x`. -/
def binderTacticDefault (x : Nat := by exact 0) := x

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``binderTacticDefault


/-- Uses {lean}`inst`. -/
def namedInstBinder [inst : Inhabited Nat] := (default : Nat)

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Uses ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "inst"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``namedInstBinder


/-- Ignores {lean}`x`. -/
def strictImplicit ⦃x : Nat⦄ := (0 : Nat)

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Ignores ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "x"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``strictImplicit


-- Holes interspersed among named parameters of distinct types. The references are
-- type-sensitive (`String.length`, `Nat` addition), so a parameter associated with the
-- wrong position would fail to elaborate.

-- A hole between a `String` and a `Nat` parameter.
/-- Outer 8. -/
def orderMid := go "x" true 0
  where
  /-- {lean}`s.length` then {lean}`n + 1`. -/
  go (s : String) _ (n : Nat) := (s, n)

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.other
                  ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _)
                  #[Lean.Doc.Inline.code "s.length"],
                Lean.Doc.Inline.text " then ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "n + 1"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``orderMid.go


-- Holes at both ends, around a `String` parameter.
/-- Outer 9. -/
def orderEnds := go 0 "y" false
  where
  /-- Just {lean}`t.length`. -/
  go _ (t : String) _ := t

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Just ",
                Lean.Doc.Inline.other
                  ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _)
                  #[Lean.Doc.Inline.code "t.length"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``orderEnds.go


-- A `where` helper with a leading `_` parameter that also captures an outer variable. The
-- captured variable stays in scope under its own name, and the named parameter resolves.
/-- Outer 10. -/
def captureLeadHole (c : Nat) := go 1 2
  where
  /-- Captures {lean}`c`, returns {lean}`y`. -/
  go _ y := y + c

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Captures ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "c"],
                Lean.Doc.Inline.text ", returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "y"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``captureLeadHole.go


-- A `_` in a bracketed binder followed by a named explicit parameter; the named one resolves.
/-- Returns {lean}`m`. -/
def implicitHoleThenNamed {_ : Nat} (m : Nat) := m

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "m"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``implicitHoleThenNamed


/-- Returns {lean}`y`. -/
def strictImplicitHoleThenNamed ⦃_ : Nat⦄ (y : Nat) := y

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other ElabInline.custom (.mk `Lean.Doc.Data.LeanTerm _) #[Lean.Doc.Inline.code "y"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``strictImplicitHoleThenNamed


-- A `_` parameter binds under an inaccessible name even when the surrounding type ascribes
-- a name to that position. Resolution stays limited to the typed binders, so the reference
-- to `n` reports an unknown identifier.
/--
error: Unknown identifier `n`
-/
#guard_msgs in
def holeNotInScope : (n : Nat) → Nat := go
  where
  /-- ref {lean}`n` -/
  go _ := 2
