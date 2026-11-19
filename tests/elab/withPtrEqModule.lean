module

/-!
Tests that the safe `withPtrEq` can be used in a module, where `rfl` proofs about it rely on its
definition being exposed, and that the compiler's check of its type applies there as well.
-/

public structure Point where
  x : Nat
  y : Nat
  deriving DecidableEq

public def decEqPoint (a b : Point) : Decidable (a = b) :=
  withPtrEqDecEq withPtrEq (fun _ _ _ _ => rfl) a b fun _ => inferInstance

public theorem withPtrEq_point (a b : Point) (k : Unit → Bool) (h : a = b → k () = true) :
    withPtrEq a b k h = k () :=
  rfl

/--
error: failed to compile definition, `withPtrEq` cannot be used at type
  List α
because it contains values of type
  α
which cannot be checked since `α` is a type variable (in field `head` of constructor `List.cons`).
-/
#guard_msgs (substring := true) in
public def poly {α : Type} (a b : List α) : Bool := withPtrEq a b (fun _ => true) (fun _ => rfl)
