import Lean
set_option doc.verso true
set_option doc.verso.suggestions false

/-!
Inline code and math that continue onto another line lose the docstring's indentation from each
continuation line. An indented docstring therefore decodes to the same content as an unindented
one, and a role that reparses its content, such as the lean role, sees the same term.
-/

open Lean Elab Command

/-- The code, math, and role contents in `inl`, in order. -/
partial def codeContents : Doc.Inline ElabInline → Array String
  | .code s => #[s]
  | .math _ s => #[s]
  | .emph xs | .bold xs | .link xs _ | .footnote _ xs | .concat xs | .other _ xs =>
    xs.flatMap codeContents
  | .text .. | .linebreak .. | .image .. => #[]

/-- Prints the code contents of every paragraph in the docstring of `name`. -/
def printCodeContents (name : Name) : CommandElabM Unit := do
  match (← findInternalDocString? (← getEnv) name) with
  | some (.inr v) =>
    for b in v.text do
      if let .para xs := b then
        IO.println (repr (xs.flatMap codeContents))
  | _ => throwError m!"No Verso docstring for {.ofConstName name}"

/--
Code {lit}`one
two`, math $`x
y`, and a term {lean}`Nat.add 1
2`.
-/
def unindented := 1

def indented := helper where
  /--
  Code {lit}`one
  two`, math $`x
  y`, and a term {lean}`Nat.add 1
  2`.
  -/
  helper := 1

/-- info: #["one\ntwo", "x\ny", "Nat.add 1\n2"] -/
#guard_msgs in
#eval printCodeContents ``unindented

/-- info: #["one\ntwo", "x\ny", "Nat.add 1\n2"] -/
#guard_msgs in
#eval printCodeContents ``indented.helper

/-!
Only the docstring's own indentation comes off a continuation line. Indentation that a block adds,
such as a blockquote's, stays in the content.
-/

def quoted := helper where
  /--
  > This is `code
    x`
  -/
  helper := 1

/-- info: #["code\n  x"] -/
#guard_msgs in
#eval show CommandElabM Unit from do
  match (← findInternalDocString? (← getEnv) ``quoted.helper) with
  | some (.inr v) =>
    for b in v.text do
      if let .blockquote #[.para xs] := b then
        IO.println (repr (xs.flatMap codeContents))
  | _ => throwError "No Verso docstring"

/-!
Only the indentation of a continuation line is whitespace. Spaces on the line the code element
opens on are content, and the boundary spaces that escape them come off as usual.
-/

/-- Code `  a  ` here. -/
def spacedUnindented := 1

def spacedIndented := helper where
  /-- Code `  a  ` here. -/
  helper := 1

/-- info: #[" a "] -/
#guard_msgs in
#eval printCodeContents ``spacedUnindented

/-- info: #[" a "] -/
#guard_msgs in
#eval printCodeContents ``spacedIndented.helper
