import Lean

/-!
Test the `recommended_spelling` command.
-/

recommended_spelling "bland" for "🥤" in [And]

/--
Conjunction

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
  "Conjunction\n\nSecond line\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☃` in identifiers is `snowmand`.\n\n * The recommended spelling of `☋` in identifiers is `orbitalAnd`.\n\n   the preferred notation is `∧`.\n\n   more stuff\n\n   even more stuff\n\n   hello"
-/
#guard_msgs in
#eval findDocString? `MyAnd

/--
info: some
  "Conjunction\n\nSecond line\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☃` in identifiers is `snowmand`.\n\n * The recommended spelling of `something` in identifiers is `and` (Docstring)."
-/
#guard_msgs in
#eval findDocString? `«term_☃_»

/--
info: some
  "Conjunction\n\nSecond line\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `☋` in identifiers is `orbitalAnd`.\n\n   the preferred notation is `∧`.\n\n   more stuff\n\n   even more stuff\n\n   hello\n\n\n * The recommended spelling of `something` in identifiers is `and` (Docstring)."
-/
#guard_msgs in
#eval findDocString? `«term_☋_»

/--
info: some
  "`And a b`, or `a ∧ b`, is the conjunction of propositions. It can be\nconstructed and destructed like a pair: if `ha : a` and `hb : b` then\n`⟨ha, hb⟩ : a ∧ b`, and if `h : a ∧ b` then `h.left : a` and `h.right : b`.\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `∧` in identifiers is `and`.\n\n * The recommended spelling of `🥤` in identifiers is `bland`."
-/
#guard_msgs in
#eval findDocString? `And

/-- info: 1 -/
#guard_msgs in
#eval do
  return (← Lean.Elab.Term.Doc.allRecommendedSpellings)
    |>.map Lean.Parser.Term.Doc.RecommendedSpelling.«notation»
    |>.count "☋"
