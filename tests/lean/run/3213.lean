import Lean
open Lean

inductive Foo : Prop where
  | foo : Foo

run_cmd do
  let recVal ← getConstInfoRec `True.rec
  logInfo m!"{recVal.isSortPoly}"

run_cmd do
  let env ← getEnv
  let mut n := 0
  let mut res := []
  for (constName, constInfo) in env.constants.map₁ do
    if let .recInfo rec_val := constInfo then
      n := n+1
      if rec_val.isSortPoly then
        res := constName::res
  logInfo m!"({n}) {res}"

set_option pp.proofs true
variable (P Q : Prop) (A : Type) (f : P → Q → A) (x : P ∧ Q)

example : And.rec f ⟨x.1,x.2⟩ = f (And.left x) (And.right x) := rfl
example : (And.rec f ⟨x.1,x.2⟩ : A) = And.rec f x  := rfl
