namespace Demo

@[extern "lean_ptr_addr"]
unsafe def ptrAddrUnsafe {α : Type} (a : @& α) : USize := 0

@[inline] unsafe def withPtrEqUnsafe {α : Type} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
if ptrAddrUnsafe a == ptrAddrUnsafe b then true else k ()

@[implemented_by withPtrEqUnsafe]
def withPtrEq {α : Type} (a b : α) (k : Unit → Bool) (h : a = b → k () = true) : Bool :=
k ()

/-
class inductive Decidable (p : Prop)
| isFalse (h : ¬p) : Decidable
| isTrue  (h : p) : Decidable
-/

/-- `withPtrEq` for `DecidableEq` -/
@[inline] def withPtrEqDecEq {α : Type} (a b : α) (k : Unit → Decidable (a = b)) : Decidable (a = b) :=
let b := withPtrEq a b (fun _ => toBoolUsing (k ())) (toBoolUsingEqTrue (k ()));
condEq b
  (fun h => isTrue (ofBoolUsingEqTrue h))
  (fun h => isFalse (ofBoolUsingEqFalse h))

end Demo

/-
abbrev DecidableEq (α : Sort u) :=
∀ (a b : α), Decidable (a = b)
-/

def List.decEqAux {α} [s : DecidableEq α] : DecidableEq (List α)
| [], []       => isTrue rfl
| a::as, b::bs =>
  match s a b with
  | isFalse n => isFalse fun h => List.noConfusion h fun h₁ _ => absurd h₁ n
  | isTrue h₁ =>
    match List.decEqAux as bs with
    -- match withPtrEqDecEq as bs (fun _ => List.decEqAux as bs with)
    | isFalse n => isFalse fun h => List.noConfusion h fun _ h₁ => absurd h₁ n
    | isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
| (_::_), [] => isFalse fun h => List.noConfusion h
| [], (_::_) => isFalse fun h => List.noConfusion h

def List.decEq {α} [DecidableEq α] : DecidableEq (List α) :=
fun a b => withPtrEqDecEq a b (fun _ => List.decEqAux a b)
