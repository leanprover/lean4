import Lean
/-!
# Formatter: preserve hard newlines around comments (#3791)

This is a regression test for https://github.com/leanprover/lean4/issues/3791

The issue was that the formatter was not preserving whether there were hard newlines
around comments in Syntax.

Note: one should turn off the sanitizer when pretty printing user syntax,
since the sanitizer clears comments from all identifiers.
-/

open Lean

deriving instance Repr for Std.Format.FlattenBehavior, Format

elab "#parse_cmd " update?:("!")? dbg?:("?")? s:str : command => Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set pp.sanitizeNames.name false) do
    let s := s.getString
    let mut cmd ← ofExcept <| Parser.runParserCategory (← getEnv) `command s
    if update?.isSome then
      cmd := cmd.updateLeading
    let fmt ← PrettyPrinter.ppCommand ⟨cmd⟩
    if dbg?.isSome then
      dbg_trace "{repr cmd}"; dbg_trace "{repr fmt}"
    logInfo (toString f!"‹{fmt}›")

elab "#parse_term " update?:("!")? dbg?:("?")? s:str : command => Elab.Command.liftTermElabM do
  withOptions (fun opts => opts.set pp.sanitizeNames.name false) do
    let s := s.getString
    let mut term ← ofExcept <| Parser.runParserCategory (← getEnv) `term s
    if update?.isSome then
      term := term.updateLeading
    let fmt ← PrettyPrinter.ppTerm ⟨term⟩
    if dbg?.isSome then
      dbg_trace "{repr term}"; dbg_trace "{repr fmt}"
    logInfo (toString f!"‹{fmt}›")

/-!
Newline before and after comment, puts hard newlines before and after.
("commented out" comes from #3791; formerly `1 = 1` was being commented out by the comment
in the output.)
-/
/--
info: ‹theorem ohno :
    -- commented out:
    1 = 1 :=
  trivial›
-/
#guard_msgs in #parse_cmd "theorem ohno : \n\
    -- commented out:\n\
    1 = 1 := trivial"

/-!
No newline before but a newline after, puts hard newline after.
-/
/--
info: ‹theorem ohno : /- commented out: -/
    1 = 1 :=
  trivial›
-/
#guard_msgs in #parse_cmd "theorem ohno :   /- commented out: -/\n\
    1 = 1 := trivial"

/-!
Now newlines before or after, puts no newlines.
-/
/--
info: ‹theorem ohno : /- commented out: -/ 1 = 1 :=
  trivial›
-/
#guard_msgs in #parse_cmd "theorem ohno :  /- commented out: -/  1 = 1 := trivial"

/-!
Inserts whitespace before comment, but not a hard newline.
There's a hard newline after the comment.
-/
/--
info: ‹∀ x : ℕ, -- commented out:
  x = x›
-/
#guard_msgs in #parse_term "∀ x : ℕ,-- commented out:\n\
    x = x"

/-!
When it's wide enough, gets a discretionary newline after.
-/
/--
info: ‹∀ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx, /- commented out: -/
  x = x›
-/
#guard_msgs in
#parse_term "∀ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx,/- commented out: -/x = x"

/-!
When it's wide enough, gets a discretionary newline before.
-/
/--
info: ‹∀ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx,
  /- commented out: -/ x = x›
-/
#guard_msgs in
#parse_term "∀ xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx,/- commented out: -/x = x"

/-!
Hard newlines before and after in terms.
-/
/--
info: ‹∀ x : ℕ,
  -- commented out:
  x = x›
-/
#guard_msgs in #parse_term "∀ x : ℕ, \n\
    -- commented out:\n\
    x = x"

/-!
No newlines before or after, but discretionary whitespace.
-/
/-- info: ‹∀ x : ℕ, /- commented out: -/ x = x› -/
#guard_msgs in #parse_term "∀ x : ℕ, \
    /- commented out: -/\
    x = x"

/-!
Inline comments
-/
/-- info: ‹[1, 2, 3 /- last comment -/ ]› -/
#guard_msgs in #parse_term "[\n1,2,3 /- last comment -/]"
/--
info: ‹[1, 2,
  3 -- last comment
    ]›
-/
#guard_msgs in #parse_term "[\n1,2,3 -- last comment\n]"
/-- info: ‹(f /- c -/ x)› -/
#guard_msgs in #parse_term "(f /- c -/ x)"

/-!
Comments after a term.
-/
/-- info: ‹(x /-comment-/ )› -/
#guard_msgs in #parse_term "(x /-comment-/)"
/--
info: ‹(x --comment
  )›
-/
#guard_msgs in #parse_term "(x --comment\n)"

/-!
Comments before a term. The `!` mode applies `updateLeading`, and the newline causes the comment
to be applied to the succeeding term.
-/
/--
info: ‹(
/-comment-/ 1)›
-/
#guard_msgs in #parse_term ! "(\n/-comment-/ 1)"
/--
info: ‹(
-- comment
1)›
-/
#guard_msgs in #parse_term ! "(\n-- comment\n 1)"
