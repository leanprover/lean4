import Lean

/-!
Tests that `DoOps` callbacks can take apart and reconstruct an indexed monad
application like `Measure Nat`, where `Measure : (α : Type) → [MeasureSpace α] → Type`
has an instance argument the default extractor cannot peel off.

`splitMonadApp?` lets the caller decompose the expected type into the
`Measure` constant plus the result type, and `mkMonadApp` lets it rebuild
`Measure α` with the instance argument synthesised.
-/

open Lean Lean.Parser Lean.Meta Lean.Elab Lean.Elab.Do Lean.Elab.Term

set_option backward.do.legacy false

class MeasureSpace (α : Type u) where

structure Measure (α : Type u) [MeasureSpace α] where
  value : α

def Measure.pure {α} [MeasureSpace α] (x : α) : Measure α := ⟨x⟩
def Measure.bind {α β} [MeasureSpace α] [MeasureSpace β]
    (mx : Measure α) (f : α → Measure β) : Measure β := f mx.value

def randOps : DoOps := { DoOps.default with
  mkPureApp _ e := do
    let eStx ← Term.exprToSyntax e
    Term.elabTermEnsuringType (← `(Measure.pure $eStx)) none
  mkBindApp _ _ e k := do
    let eStx ← Term.exprToSyntax e
    let kStx ← Term.exprToSyntax k
    Term.elabTermEnsuringType (← `(Measure.bind $eStx $kStx)) none
  isPureApp? e :=
    if e.isAppOfArity ``Measure.pure 3 then some e.appArg! else none
  splitMonadApp? type := do
    let type := type.consumeMData
    unless type.isAppOfArity ``Measure 2 do return none
    let resultType := type.getAppArgs[0]!
    let u ← getDecLevel resultType
    return some ({ m := type.getAppFn, u := u.normalize, v := u.normalize }, resultType)
  mkMonadApp α := do
    let m ← Term.exprToSyntax (← read).monadInfo.m
    Term.elabTermEnsuringType (← `($m $(← Term.exprToSyntax α))) none
}

syntax (name := randKind) "do_rand " doSeq : term

@[term_elab randKind] def elabRand : Term.TermElab := fun stx et? => do
  let `(do_rand $doSeq) := stx | throwUnsupportedSyntax
  elabDoWith randOps doSeq et?

instance : MeasureSpace Nat := ⟨⟩

def uniform (n : Nat) : Measure Nat := ⟨n/2⟩

/-- info: Measure.pure 42 : Measure Nat -/
#guard_msgs in
#check (do_rand return 42 : Measure Nat)

/-- info: uniform 10 : Measure Nat -/
#guard_msgs in
#check (do_rand do
    let a : Nat ← uniform 10
    return a : Measure Nat)

/--
info: (uniform 10).bind fun a => Measure.pure (a + 1) : Measure Nat
-/
#guard_msgs in
#check (do_rand do
    let a : Nat ← uniform 10
    return a + 1 : Measure Nat)
