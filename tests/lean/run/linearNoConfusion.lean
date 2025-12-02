/-!
This test tests and also explains the noConfusionType construction.

It contains copies of the definitions of the constructions, for manual experimentation with
the code, and uses `#guard_msgs` and `rfl` to compare them to the generated ones.

This also serves as documentation to the `NoConfusionLinear` module, so do not delete or remove
from this file without updating that module's docstring.
-/

-- set_option debug.skipKernelTC true
-- set_option trace.Meta.mkNoConfusion true
-- set_option trace.Kernel true
-- set_option genInjectivity false
-- set_option trace.Meta.injective true
-- set_option trace.Meta.Tactic.injection true

inductive Vec.{u} (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons1 {n} : α → Vec α n → Vec α (n + 1)
  | cons2 {n} : α → Vec α n → Vec α (n + 1)

#check Vec.cons1.noConfusion
#check Vec.cons1.inj
#check Vec.cons1.injEq

@[reducible] protected def Vec.noConfusionType'.{u_1, u} : {α : Type} →
  Sort u_1 → {a : Nat} → Vec.{u} α a → {a : Nat} → Vec α a → Sort u_1 :=
fun P _ x1 _ x2 =>
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
  Sort u_1 → {a : Nat} → Vec α a → {a : Nat} → Vec α a → Sort u_1 :=
fun {α} P {a} t {a_1} t_1 =>
  Vec.casesOn t (if h : t_1.ctorIdx = 0 then Vec.nil.elim t_1 h (P → P) else P)
    (fun {n} a a_2 =>
      if h : t_1.ctorIdx = 1 then Vec.cons1.elim t_1 h fun {n_1} a_3 a_4 => (n = n_1 → a = a_3 → a_2 ≍ a_4 → P) → P
      else P)
    fun {n} a a_2 =>
    if h : t_1.ctorIdx = 2 then Vec.cons2.elim t_1 h fun {n_1} a_3 a_4 => (n = n_1 → a = a_3 → a_2 ≍ a_4 → P) → P else P
-/
#guard_msgs in
#print Vec.noConfusionType

example : @Vec.noConfusionType.{u_1,u} = @Vec.noConfusionType'.{u_1,u} := rfl


-- A possibly tricky universes case (resulting universe cannot be decremented)

inductive UnivTest.{u,v} (α : Sort v): Sort (max u v 1) where
  | mk1 : UnivTest α
  | mk2 : (x : α) → UnivTest α
  | mk3 : (x : α) → UnivTest α
