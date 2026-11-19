import Lean.Elab.Command

/-!
Tests that `set_option doc.verso true in <command>` results in `<command>` being parsed with
docstrings in Verso format, just as `open X in <command>` enables scoped parsers from X.
-/

open Lean Elab Command

/-- Reports whether `name`'s docstring was parsed as Verso markup or as plain Markdown. -/
elab "#doc_kind " name:ident : command => do
  let env ← getEnv
  runTermElabM fun _ => do
    let declName ← realizeGlobalConstNoOverloadWithInfo name
    match (← findInternalDocString? env declName (includeBuiltin := true)) with
    | some (.inl _) => logInfo "markdown"
    | some (.inr _) => logInfo "verso"
    | none          => logInfo "none"

set_option doc.verso true in
/--
# Verso header

Some *emphasis*.
-/
def withVerso := 1

/-- Plain `markdown` docstring. -/
def withoutVerso := 2

set_option doc.verso true
set_option doc.verso false in
set_option doc.verso true in
set_option doc.verso false in
/-- Plain `markdown` docstring. -/
def withoutVersoMore := 2
set_option doc.verso false

set_option pp.all true in set_option doc.verso true in
/--
# Nested
-/
def nested := 3

/-- info: verso -/
#guard_msgs in #doc_kind withVerso

/-- info: markdown -/
#guard_msgs in #doc_kind withoutVerso

/-- info: markdown -/
#guard_msgs in #doc_kind withoutVersoMore

/-- info: verso -/
#guard_msgs in #doc_kind nested

/--
error: Can't add Verso-format module docs because there is already Markdown-format content present.
-/
#guard_msgs in
set_option doc.verso true in
/-!
Not allowed - wrong format for module.
-/
