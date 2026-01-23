prelude -- stand-alone, its useful to run these tests even if the prelude does not work

inductive Eq {α : Type} (a : α) : α → Prop
| refl : Eq a a

inductive N where
| zero : N
| succ : N → N

def N.two := N.zero.succ.succ

#print N.rec

inductive Vec (α : Type) : N → Type
| nil  : Vec α .zero
| cons : α → Vec α n → Vec α (.succ n)

#print Vec.rec

def foo := Vec.cons N.zero (Vec.cons N.zero Vec.nil)

noncomputable def Vec.id {α : Type} : {n : N} → (v : Vec α n) → Vec α n :=
  @Vec.rec _ (motive := fun n _ => Vec α n) Vec.nil (fun x _xs ih => Vec.cons x ih)

theorem Vec.id_nil {α : Type} : @Eq (Vec α .zero) (Vec.id Vec.nil) Vec.nil := Eq.refl

theorem Vec.id_cons {α : Type} (x : α) (xs : Vec α n) : Eq (Vec.id (Vec.cons x xs)) (Vec.cons x (Vec.id xs)) := Eq.refl

theorem test : Eq (Vec.id foo) foo := Eq.refl

def Vec.pair (x1 x2 : α) : Vec α N.two :=
  Vec.cons x1 (Vec.cons x2 Vec.nil)

mutual
inductive MutualA (α : Type) : N → Type
| nil  : MutualA α .zero
| cons : α → MutualB α n → MutualA α (.succ n)

inductive MutualB (α : Type) : N → Type
| nil  : MutualB α .zero
| cons : α → MutualA α n → MutualB α (.succ n)
end

def mutual_foo := MutualA.cons N.zero (MutualB.cons N.zero MutualA.nil)

noncomputable def MutualA.swap {α : Type} {n : N} : MutualA α n → MutualB α n :=
  MutualA.rec
    (motive_1 := fun n _ => MutualB α n)
    (motive_2 := fun n _ => MutualA α n)
    MutualB.nil (fun x _xs ih => .cons x ih)
    MutualA.nil (fun x _xs ih => .cons x ih)

noncomputable def MutualB.swap {α : Type} {n : N} : MutualB α n → MutualA α n :=
  MutualB.rec
    (motive_1 := fun n _ => MutualB α n)
    (motive_2 := fun n _ => MutualA α n)
    MutualB.nil (fun x _xs ih => .cons x ih)
    MutualA.nil (fun x _xs ih => .cons x ih)

#print MutualA.rec

theorem mutual_test : Eq (MutualB.swap (MutualA.swap mutual_foo)) mutual_foo := @Eq.refl _ mutual_foo

inductive Nested (α : Type) : Type
  | leaf : α → Nested α
  | branch : Vec (Nested α) N.zero.succ.succ → Nested α

#print Nested.rec

noncomputable def Nested.id {α : Type} : Nested α → Nested α :=
  Nested.rec (motive_1 := fun _ => Nested α)
      (motive_2 := fun i _ => Vec (Nested α) i)
    (leaf := fun x => .leaf x)
    (branch := fun _xs ih => .branch ih)
    (nil := .nil)
    (cons := fun _x _xs ih1 ih2 => .cons ih1 ih2)

#print Nested.id

def nested_foo : Nested N :=
  .branch (Vec.pair (.leaf N.zero) (.leaf N.zero))

theorem nested_test : Eq (Nested.id nested_foo) nested_foo := @Eq.refl _ nested_foo
