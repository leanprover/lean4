/-
Tests that when `doc.verso.module` is not explicitly set,
module docs fall back to the value of `doc.verso`.
-/
import Lean

-- Only set doc.verso, do not set doc.verso.module
set_option doc.verso true

/-!
Module docs should parse as Verso here (fallback from {option}`doc.verso`).

*Bold* and _italic_ and [link](example.com)
-/

open Lean Elab Term in
/--
info: Markdown:
Verso:
{ text := #[Lean.Doc.Block.para
              #[Lean.Doc.Inline.text "Module docs should parse as Verso here (fallback from ",
                Lean.Doc.Inline.other
                  { name := `Lean.Doc.Data.Option val := Dynamic.mk `Lean.Doc.Data.Option _ }
                  #[Lean.Doc.Inline.code "doc.verso"],
                Lean.Doc.Inline.text ")."],
            Lean.Doc.Block.para
              #[Lean.Doc.Inline.bold #[Lean.Doc.Inline.text "Bold"], Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.emph #[Lean.Doc.Inline.text "italic"], Lean.Doc.Inline.text " and ",
                Lean.Doc.Inline.link #[Lean.Doc.Inline.text "link"] "example.com", Lean.Doc.Inline.linebreak "\n"]],
  sections := #[],
  declarationRange := { pos := { line := 10, column := 0 },
                        charUtf16 := 0,
                        endPos := { line := 14, column := 2 },
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


/--
{name}`fallbackDecl`
-/
def fallbackDecl := "hello"

open Lean Elab Command Term in
/-- info: `fallbackDecl` -/
#guard_msgs in
#eval show TermElabM Unit from do
  (← findDocString? (← getEnv) ``fallbackDecl).forM (IO.println ·)
