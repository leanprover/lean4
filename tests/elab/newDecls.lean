import Lean.Linter
import Lean.Environment
import Init.Data.Array.QSort

open Lean

def newDeclLinter : Lean.Linter where
  run prevEnv stx := do
    let names := Environment.newConstNamesSince prevEnv (← getEnv)
    unless names.isEmpty do
      logInfoAt stx m!"new declarations: {names.qsort Name.lt}"

run_cmd addLinter newDeclLinter

/-- info: new declarations: [hello] -/
#guard_msgs in
def hello : String := "world"

/--
info: new declarations: [Hello,
 Hello.Hi,
 Hello._sizeOf_1,
 Hello._sizeOf_inst,
 Hello.casesOn,
 Hello.ctorIdx,
 Hello.noConfusion,
 Hello.noConfusionType,
 Hello.rec,
 Hello.recOn,
 Hello.toCtorIdx,
 Hello.Hi.sizeOf_spec]
-/
#guard_msgs in
inductive Hello : Type where
  | Hi : Hello

/--
info: new declarations: [test,
 test._functor,
 test._proof_1,
 test._unsafe_rec,
 test.casesOn,
 test.eq_1,
 test.eq_def,
 test.functor_unfold,
 test._functor.casesOn,
 test._functor.existential,
 test._functor.existential_equiv,
 test._functor.rec,
 test._functor.recOn]
-/
#guard_msgs in
coinductive test : Prop where

/--
info: new declarations: [isEven,
 isOdd,
 isEven._f,
 isEven._sunfold,
 isEven._unsafe_rec,
 isOdd._f,
 isOdd._sunfold,
 isOdd._unsafe_rec,
 isOdd.match_1]
-/
#guard_msgs in
mutual

  def isOdd (n : Nat) := match n with
  | 0 => false
  | n + 1 => isEven n

  def isEven (n : Nat) := match n with
  | 0 => true
  | n + 1 => isOdd n
end
