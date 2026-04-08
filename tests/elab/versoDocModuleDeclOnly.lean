/-
Tests that `doc.verso.module false` disables Verso for module docs
while `doc.verso true` keeps declaration docs as Verso.
-/
import Lean

-- Module docs use Markdown, declaration docs use Verso
set_option doc.verso true
set_option doc.verso.module false

/-!
This is a plain Markdown module doc with `code` and **bold**.

Verso syntax is {here}**visible**.
-/

open Lean Elab Term in
/--
info: Markdown:
This is a plain Markdown module doc with `code` and **bold**.

Verso syntax is {here}**visible**.

Verso:
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
{name}`versoDecl`
-/
def versoDecl := "hello"

-- This would show the Verso syntax if it were interpreted as Markdown
open Lean Elab Term in
/-- info: `versoDecl` -/
#guard_msgs in
#eval show TermElabM Unit from do
  (← findDocString? (← getEnv) ``versoDecl).forM (IO.println ·)
