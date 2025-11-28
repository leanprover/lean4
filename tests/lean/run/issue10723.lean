import Lean.Syntax

open Lean

private partial def onlyIdent' : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty ·)
    if h : nonEmpty.size = 1 then onlyIdent' nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Syntax → Bool
  | .node _ _ xs =>
    xs.all isEmpty
  | _ => false

partial def onlyIdent'' : Syntax → Bool
  | .node _ _ args =>
    let nonEmpty := args.filter (!isEmpty () ·)
    if h : nonEmpty.size = 1 then onlyIdent'' nonEmpty[0]
    else false
  | .ident .. => true
  | _ => false
where
  isEmpty : Unit → Syntax → Bool
  | _, .node _ _ xs =>
    xs.all (isEmpty ())
  | _, _ => false

axiom mySorry : α

-- In the following we check whether

def f : (n m : Nat) → (n < m) → Nat
  | 0, _, _ => 0
  | n+1, 0, _ => by contradiction
  | n+1, m+1, _ => (f n (f n m mySorry) (Nat.lt_of_lt_of_le mySorry (Nat.le_refl _))) + 1
termination_by n => n

-- This shows an interesting effect: abstractNestedProofs infers the type, runs itself
-- on the type (so `f._proof_2` in the type), and then abstracts the unchanged body
-- (so `mySorry` in the body).
-- This would be type-incorrect if the two expressions were abstracted separately.
-- Why does this not happen here? Why does this not abstract over the auxDecl `f`?

set_option pp.proofs true
/--
info: theorem f._proof_3 : ∀ (n m : Nat), n < f n m (f._proof_2 n m) :=
fun n m => Nat.lt_of_lt_of_le mySorry (Nat.le_refl (f n m mySorry))
-/
#guard_msgs in
#print f._proof_3
