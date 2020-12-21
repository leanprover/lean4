def f (xs : List Nat) : List Bool :=
xs.map fun
  | 0 => true
  | _ => false

#eval f [1, 2, 0, 2]

theorem ex1 : f [1, 0, 2] = [false, true, false] :=
rfl

#check f

set_option pp.raw true
set_option pp.raw.maxDepth 10
set_option trace.Elab.step true in
def g (xs : List Nat) : List Bool :=
xs.map <| by {
  intro
    | 0 => exact true
    | _ => exact false
}

theorem ex2 : g [1, 0, 2] = [false, true, false] :=
rfl

theorem ex3 {p q r : Prop} : p ∨ q → r → (q ∧ r) ∨ (p ∧ r) :=
by intro
 | Or.inl hp, h => { apply Or.inr; apply And.intro; assumption; assumption }
 | Or.inr hq, h => { apply Or.inl; exact ⟨hq, h⟩ }

inductive C
| mk₁ : Nat → C
| mk₂ : Nat → Nat → C

def C.x : C → Nat
| C.mk₁ x   => x
| C.mk₂ x _ => x

def head : {α : Type} → List α → Option α
| _, a::as => some a
| _, _     => none

theorem ex4 : head [1, 2] = some 1 :=
rfl

def head2 : {α : Type} → List α → Option α :=
@fun
  | _, a::as => some a
  | _, _     => none

theorem ex5 : head2 [1, 2] = some 1 :=
rfl

def head3 {α : Type} (xs : List α) : Option α :=
let rec aux : {α : Type} → List α → Option α
  | _, a::as => some a
  | _, _     => none;
aux xs

theorem ex6 : head3 [1, 2] = some 1 :=
rfl

inductive Vec.{u} (α : Type u) : Nat → Type u
| nil : Vec α 0
| cons {n} (head : α) (tail : Vec α n) : Vec α (n+1)

def Vec.mapHead1 {α β δ} : {n : Nat} → Vec α n → Vec β n → (α → β → δ) → Option δ
| _,   nil,       nil,       f => none
| _, cons a as, cons b bs,   f => some (f a b)

def Vec.mapHead2 {α β δ} : {n : Nat} → Vec α n → Vec β n → (α → β → δ) → Option δ
| _, nil,            nil,         f => none
| _, @cons _ n a as, cons b bs,   f => some (f a b)

def Vec.mapHead3 {α β δ} : {n : Nat} → Vec α n → Vec β n → (α → β → δ) → Option δ
| _, nil,            nil,         f => none
| _, cons (tail := as) (head := a), cons b bs,   f => some (f a b)

inductive Foo
| mk₁ (x y z w : Nat)
| mk₂ (x y z w : Nat)

def Foo.z : Foo → Nat
| mk₁ (z := z) .. => z
| mk₂ (z := z) .. => z

#eval (Foo.mk₁ 10 20 30 40).z

theorem ex7 : (Foo.mk₁ 10 20 30 40).z = 30 :=
rfl

def Foo.addY? : Foo × Foo → Option Nat
| (mk₁ (y := y₁) .., mk₁ (y := y₂) ..) => some (y₁ + y₂)
| _ => none

#eval Foo.addY? (Foo.mk₁ 1 2 3 4, Foo.mk₁ 10 20 30 40)

theorem ex8 : Foo.addY? (Foo.mk₁ 1 2 3 4, Foo.mk₁ 10 20 30 40) = some 22 :=
rfl

instance {α} : Inhabited (Sigma fun m => Vec α m) :=
⟨⟨0, Vec.nil⟩⟩

partial def filter {α} (p : α → Bool) : {n : Nat} → Vec α n → Sigma fun m => Vec α m
| _, Vec.nil        => ⟨0, Vec.nil⟩
| _, Vec.cons x xs  => match p x, filter p xs with
  | true,  ⟨_, ys⟩ => ⟨_, Vec.cons x ys⟩
  | false, ys      => ys

inductive Bla
| ofNat  (x : Nat)
| ofBool (x : Bool)

def Bla.optional? : Bla → Option Nat
| ofNat x  => some x
| ofBool _ => none

def Bla.isNat? (b : Bla) : Option { x : Nat // optional? b = some x } :=
match b.optional? with
| some y => some ⟨y, rfl⟩
| none   => none

def foo (b : Bla) : Option Nat := b.optional?
theorem fooEq (b : Bla) : foo b = b.optional? :=
rfl

def Bla.isNat2? (b : Bla) : Option { x : Nat // optional? b = some x } :=
match h:foo b with
| some y => some ⟨y, Eq.trans (fooEq b).symm h⟩
| none   => none

def foo2 (x : Nat) : Nat :=
match x, rfl : (y : Nat) → x = y → Nat with
| 0,   h => 0
| x+1, h => 1
