import Lean
/-!
# Pretty printing of `<|>`, `<*>`, `>>`, `<*`, and `*>`

https://github.com/leanprover/lean4/issues/5668
-/

/-- info: none <|> some false : Option Bool -/
#guard_msgs in #check none <|> some false

variable [Monad m] (a : m α) (b : m β) (f : m (α → β))

/-- info: f <*> a : m β -/
#guard_msgs in #check f <*> a

/-- info: a <* b : m α -/
#guard_msgs in #check a <* b

/-- info: a *> b : m β -/
#guard_msgs in #check a *> b

/-- info: Lean.Parser.ident >> Lean.Parser.symbol "hi" : Lean.Parser.Parser -/
#guard_msgs in #check Lean.Parser.ident >> "hi"


/-!
Dependent, substitutes in `()`.
-/
/-- info: some true <|> some (() == ()) : Option Bool -/
#guard_msgs in #check HOrElse.hOrElse (some true) (fun h => some <| h == ())

/-!
Not a lambda, applies `()`.
-/
/-- info: some true <|> Function.const Unit (some true) () : Option Bool -/
#guard_msgs in #check HOrElse.hOrElse (some true) (Function.const _ (some true))
