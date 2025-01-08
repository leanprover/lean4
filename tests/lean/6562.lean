/-! Patterns with metavariables should still satisfy defeqs -/

example : (x : Nat) → (Eq.refl x).symm.ndrec (motive := fun _ => Bool) false = false → Unit
  | _, rfl => ()

inductive Mem (a : α) : List α → Type
  | head (as : List α) : Mem a (a::as)
  | tail (b : α) {as : List α} : Mem a as → Mem a (b::as)

def del : @Mem α a as → List α
  | .head as => as
  | .tail b mem => b :: del mem

def memOfDel : (mem : Mem c as) → Mem a (del mem) → Mem a as
  | .head _, mem => .tail _ mem
  | .tail _ mem, .head _ => .head _
  | .tail _ mem, .tail _ mem' => .tail _ (memOfDel mem mem')

def memOfDel' : (mem : Mem c as) → Mem a (del mem) → Mem a as
  | .head _, mem => .tail _ mem
  | .tail b mem, (mem' : Mem a (b :: del mem)) =>
    match mem' with
    | .head _ => .head _
    | .tail _ mem' => .tail _ (memOfDel' mem mem')
