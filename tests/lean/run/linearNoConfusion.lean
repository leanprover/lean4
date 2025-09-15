/-!
This test tests and also explains the noConfusionType construction.

It contains copies of the definitions of the constructions, for manual experimentation with
the code, and uses `#guard_msgs` and `rfl` to compare them to the generated ones.

This also serves as documentation to the `NoConfusionLinear` module, so do not delete or remove
from this file without updating that module's docstring.
-/

-- set_option debug.skipKernelTC true

inductive Vec.{u} (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons1 {n} : α → Vec α n → Vec α (n + 1)
  | cons2 {n} : α → Vec α n → Vec α (n + 1)

@[reducible] protected def Vec.noConfusionType'.{u_1, u} : {α : Type} →
  {a : Nat} → Sort u_1 → Vec.{u} α a → Vec α a → Sort u_1 :=
fun P x1 x2 =>
  Vec.casesOn x1
    (if h : x2.ctorIdx = 0 then
      Vec.nil.elim (motive := fun _ _ => Sort u_1) x2 h (P → P)
    else P)
    (fun {n} a_1 a_2 => if h : x2.ctorIdx = 1 then
      Vec.cons1.elim (motive := fun _ _ => Sort u_1) x2 h fun {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P
     else P)
    (fun {n} a_1 a_2 => if h : x2.ctorIdx = 2 then
      Vec.cons2.elim (motive := fun _ _ => Sort u_1) x2 h fun {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P
     else P)

/--
info: @[reducible] protected def Vec.noConfusionType.{u_1, u} : {α : Type} →
  {a : Nat} → Sort u_1 → Vec α a → Vec α a → Sort u_1 :=
fun {α} {a} P x1 x2 =>
  Vec.casesOn x1 (if h : x2.ctorIdx = 0 then Vec.nil.elim x2 h (P → P) else P)
    (fun {n} a_1 a_2 =>
      if h : x2.ctorIdx = 1 then Vec.cons1.elim x2 h fun {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P else P)
    fun {n} a_1 a_2 =>
    if h : x2.ctorIdx = 2 then Vec.cons2.elim x2 h fun {n_1} a a_3 => (n = n_1 → a_1 = a → a_2 ≍ a_3 → P) → P else P
-/
#guard_msgs in
#print Vec.noConfusionType

example : @Vec.noConfusionType.{u_1,u} = @Vec.noConfusionType'.{u_1,u} := rfl


-- A possibly tricky universes case (resulting universe cannot be decremented)

inductive UnivTest.{u,v} (α : Sort v): Sort (max u v 1) where
  | mk1 : UnivTest α
  | mk2 : (x : α) → UnivTest α
  | mk3 : (x : α) → UnivTest α
