import Lean

/-!
Test the `recommended_spelling` command.

TODO: once we use this command in Init, we can test that recommended spellings from imported
modules are reported correctly.
-/

/--
Conjuction

Second line
-/
inductive MyAnd (P Q : Prop) : Prop where
  | intro : P → Q → MyAnd P Q

@[inherit_doc] infixr:35 " ☃ " => MyAnd
@[inherit_doc] infixr:35 " ☋ " => MyAnd

recommended_spelling "snowmand" for "☃" in [MyAnd, «term_☃_»]
/-- the preferred notation is `∧`.

more stuff

even more stuff

hello

-/
recommended_spelling "orbitalAnd" for "☋" in [MyAnd, «term_☋_»]
/--      Docstring      -/
recommended_spelling "and" for "something" in [«term_☃_», «term_☋_»]

def findDocString? (n : Lean.Name) : Lean.MetaM (Option String) := do
  Lean.findDocString? (← Lean.getEnv) n

/--
info: some
  "Conjuction\n\nSecond line\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☃` in identifiers is `snowmand`.\n\n * The recommended spelling of `☋` in identifiers is `orbitalAnd`.\n\n   the preferred notation is `∧`.\n\n   more stuff\n\n   even more stuff\n\n   hello"
-/
#guard_msgs in
#eval findDocString? `MyAnd

/--
info: some
  "Conjuction\n\nSecond line\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☃` in identifiers is `snowmand`.\n\n * The recommended spelling of `something` in identifiers is `and` (Docstring)."
-/
#guard_msgs in
#eval findDocString? `«term_☃_»

/--
info: some
  "Conjuction\n\nSecond line\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☋` in identifiers is `orbitalAnd`.\n\n   the preferred notation is `∧`.\n\n   more stuff\n\n   even more stuff\n\n   hello\n\n\n\n\n * The recommended spelling of `something` in identifiers is `and` (Docstring)."
-/
#guard_msgs in
#eval findDocString? `«term_☋_»

/-- info: 1 -/
#guard_msgs in
#eval do
  return (← Lean.Elab.Term.Doc.allRecommendedSpellings)
    |>.map Lean.Parser.Term.Doc.RecommendedSpelling.«notation»
    |>.count "☋"
