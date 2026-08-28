/-
Tests that `doc.verso.module` can independently enable Verso syntax for module docs
while keeping declaration docs as Markdown.
-/
import Lean

-- Module docs use Verso, declaration docs use Markdown
set_option doc.verso.module true
set_option doc.verso false

/-!
Module docs should parse as Verso here.

*Bold* and _italic_ and [link](example.com)
-/

open Lean Elab Term in
/--
info: Markdown:
Verso:
{ text := #[Lean.Doc.Block.para #[Lean.Doc.Inline.text "Module docs should parse as Verso here."],
            Lean.Doc.Block.para
              #[Lean.Doc.Inline.bold #[Lean.Doc.Inline.text "Bold"], Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.emph #[Lean.Doc.Inline.text "italic"], Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.link #[Lean.Doc.Inline.text "link"] "example.com", Lean.Doc.Inline.linebreak "\n"]],
  sections := #[],
  declarationRange := { pos := { line := 11, column := 0 },
                        charUtf16 := 0,
                        endPos := { line := 15, column := 2 },
                        endCharUtf16 := 2 } }
-/
#guard_msgs in
#eval show TermElabM Unit from do
  IO.println "Markdown:"
  for modDoc in (Lean.getMainModuleDoc (← getEnv)).toArray do
    IO.println modDoc.doc
  IO.println "Verso:"
  for modDoc in (Lean.getMainVersoModuleDocs (← getEnv)).snippets do
    IO.println <| repr modDoc


/-- This is a plain Markdown docstring with {nonVerso}`code` and **bold**. -/
def plainMarkdown := "hello"

open Lean Elab Command Term in
/-- info: "This is a plain Markdown docstring with {nonVerso}`code` and **bold**. " -/
#guard_msgs in
#eval show TermElabM Unit from do
  (← findDocString? (← getEnv) ``plainMarkdown).forM (IO.println ·.quote)
