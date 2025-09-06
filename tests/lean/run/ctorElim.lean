inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n + 1)

/--
info: @[reducible] protected def Vec.nil.elim.{u} : {α : Type} →
  {motive : (a : Nat) → Vec α a → Sort u} → {a : Nat} → (t : Vec α a) → t.ctorIdx = 0 → motive 0 Vec.nil → motive a t
-/
#guard_msgs in
#print sig Vec.nil.elim

/--
info: @[reducible] protected def Vec.cons.elim.{u} : {α : Type} →
  {motive : (a : Nat) → Vec α a → Sort u} →
    {a : Nat} →
      (t : Vec α a) →
        t.ctorIdx = 1 → ({n : Nat} → (a : α) → (a_1 : Vec α n) → motive (n + 1) (Vec.cons a a_1)) → motive a t
-/
#guard_msgs in
#print sig Vec.cons.elim


structure JustOneConstructor where
  (x : Nat)
  (y : Bool)

/-- error: Unknown constant `JustOneConstructor.mk.elim` -/
#guard_msgs in #print sig JustOneConstructor.mk.elim
