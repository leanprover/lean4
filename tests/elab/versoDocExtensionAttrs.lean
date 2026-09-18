import Lean

/-!
This file tests that several documentation extension attributes may be applied to one declaration.
Each generates the same wrapper, so the first application generates it and the rest use it.
-/

set_option doc.verso true

open Lean Doc Elab Term

def alpha := ()
def beta := ()

@[doc_role alpha, doc_role beta]
meta def bothRoles (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .text "!"

/-- Uses {alpha}`one` and {beta}`two`. -/
def usesBothRoles := ()

open Lean Elab Command in
/-- info: Uses ! and !. -/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.print (← findDocString? (← getEnv) ``usesBothRoles).get!

@[doc_code_suggestions, builtin_doc_code_suggestions]
meta def bothSuggesters (_ : VersoCode) : DocM (Array CodeSuggestion) := do
  return #[]

-- The wrapper shows the documentation of the declaration it wraps. The generated wrapper is shared,
-- so it inherits that documentation once.

def gamma := ()
def delta := ()

/-- Documentation of the role. -/
@[doc_role gamma, doc_role delta]
meta def documentedRole (_ : TSyntaxArray `inline) : DocM (Inline ElabInline) := do
  return .text "?"

/-- Uses {gamma}`one` and {delta}`two`. -/
def usesDocumentedRole := ()

open Lean Elab Command in
/--
info: Uses ? and ?.
Documentation of the role.
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  IO.println (← findDocString? (← getEnv) ``usesDocumentedRole).get!.trimAscii
  IO.println (← findDocString? (← getEnv) ``documentedRole.getArgs).get!.trimAscii
