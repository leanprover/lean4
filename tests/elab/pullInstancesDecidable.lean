/-!
`pullInstances` must not hoist a `Decidable` value out of the branch or thunk it occurs in: the
value is the result of running a decision procedure, so hoisting it runs the procedure where the
source does not. Since #8309 turned `if` into a `cases` on `Bool`, `if` branches are affected too.
-/

inductive T where
  | leaf (n : Nat)
  | node (l r : T)
deriving DecidableEq

/-- `instDecidableEqT`, announcing each run of the decision procedure. -/
def noisy (a b : T) : Decidable (a = b) :=
  dbg_trace "decided"; instDecidableEqT a b

/--
info: decided
---
info: false
-/
#guard_msgs in
#eval (noisy (.leaf 1) (.leaf 2)).decide

@[inline] def withAddr {β : Type} [Subsingleton β] (a : T) (k : USize → β) : β :=
  withPtrAddr a k (fun _ _ => Subsingleton.elim _ _)

@[inline] def ptrDec (a b : T) : Decidable (a = b) :=
  withPtrEqDecEq a b (fun _ => noisy a b)

/-- The shape of a hash-consing equality test: decide by pointer first. -/
def viaAddr (a b : @& T) : Decidable (a = b) :=
  withAddr a fun pa => withAddr b fun pb =>
    if pa == pb then ptrDec a b else instDecidableEqT a b

/-- info: false -/
#guard_msgs in
#eval (viaAddr (.leaf 1) (.leaf 2)).decide

@[noinline] def ignore (_ : Unit → Bool) : Bool := true

def viaThunk (a b : T) : Bool :=
  ignore fun _ => (noisy a b).decide

/-- info: true -/
#guard_msgs in
#eval viaThunk (.leaf 1) (.leaf 2)
