import Lean
/-!
# Verso docstrings on macro-generated declarations

This test ensures that Verso docstrings in macro-generated definitions respect hygiene for role names.
-/

section

open Lean Elab Command

deriving instance Repr for VersoDocString

def printVersoDocstring (x : Name) : CommandElabM Unit := do
  match ← findInternalDocString? (← getEnv) x with
  | none => throwError m!"No docstring for {.ofConstName x}"
  | some (.inl md) => throwError m!"Only a Markdown docstring for {.ofConstName x}:\n{md}"
  | some (.inr v) => IO.println (repr v)

end

set_option doc.verso true

-- A macro-generated declaration with a Verso docstring referencing a global constant.
macro "defWithDoc" nm:ident : command => `(
  /-- Built on {lean}`Nat.succ`. -/
  def $nm := 0)
defWithDoc macroGenerated

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Built on ",
                Lean.Doc.Inline.other
                  { val := Dynamic.mk `Lean.Doc.Data.LeanTerm _ }
                  #[Lean.Doc.Inline.code "Nat.succ"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``macroGenerated

-- A macro-generated declaration whose parameter is written as a bare identifier.
macro "defBare" nm:ident : command => `(
  /-- Returns {lean}`Nat.succ`. -/
  def $nm x := x + 1)
defBare macroBare

/--
info: { text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Returns ",
                Lean.Doc.Inline.other
                  { val := Dynamic.mk `Lean.Doc.Data.LeanTerm _ }
                  #[Lean.Doc.Inline.code "Nat.succ"],
                Lean.Doc.Inline.text ". "]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``macroBare

-- A macro-generated docstring containing a `lean` code block whose commands are elaborated.
macro "defCodeBlock" nm:ident : command => `(
/--
A code block:
```lean
#check Nat.succ
```
-/
def $nm := 0)
defCodeBlock macroCodeBlock

/--
info: { text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "A code block:"],
            Lean.Doc.Block.other
              { val := Dynamic.mk `Lean.Doc.Data.LeanBlock _ }
              #[Lean.Doc.Block.code "#check Nat.succ\n"]],
  subsections := #[] }
-/
#guard_msgs in
#eval printVersoDocstring ``macroCodeBlock
