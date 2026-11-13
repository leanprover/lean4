import Lean
open Lean Elab Command

/-! Regression test: We don't have to enforce ctor limits on propositional inductive types  -/

-- inductive P : Nat → Nat → Prop
--   | c0 (xs : List Nat) : P xs.length 0
--   ...
--   | c244 (xs : List Nat) : P xs.length 244
run_cmd do
  let ctors ← (List.range 245).toArray.mapM fun i =>
    `(Parser.Command.ctor| | $(mkIdent s!"c{i}".toName):ident (xs : List Nat) : $(mkIdent `P) xs.length $(quote i))
  elabCommand (← `(inductive $(mkIdent `P) : Nat → Nat → Prop where $ctors:ctor*))

-- inductive Q : Prop
--   | mk (f0 : UInt64) ... (f199 : UInt64)
run_cmd do
  let fields ← (List.range 200).toArray.mapM fun i =>
    `(Parser.Term.bracketedBinderF| ($(mkIdent s!"f{i}".toName) : UInt64))
  elabCommand (← `(inductive $(mkIdent `Q) : Prop where | $(mkIdent `mk):ident $fields* : $(mkIdent `Q)))
