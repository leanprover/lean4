universes u v

inductive Foo (α : Type u)
| leaf (a : α) : Foo
| node (left : Foo) (right : Foo) : Foo
| cons (head : α) (tail : Foo) : Foo

def Foo.elim {α : Type u} (C : Foo α → Foo α → Sort v) (x y : Foo α)
  (h₁ : forall (a₁ a₂ : α), C (Foo.leaf a₁) (Foo.leaf a₂))
  (h₂ : forall (l₁ r₁ l₂ r₂ : Foo α), C (Foo.node l₁ r₁) (Foo.node l₂ r₂))
  (h₃ : forall (h₁ t₁ h₂ t₂), C (Foo.cons h₁ t₁) (Foo.cons h₂ t₂))
  (h₄ : forall (x y), C x y)
  : C x y :=
Foo.casesOn x
  (fun a₁ => Foo.casesOn y
    (fun a₂ => h₁ a₁ a₂)
    (fun l₂ r₂ => h₄ (Foo.leaf a₁) (Foo.node l₂ r₂))
    (fun h₂ t₂ => h₄ (Foo.leaf a₁) (Foo.cons h₂ t₂)))
  (fun l₁ r₁ => Foo.casesOn y
    (fun a₂    => h₄ (Foo.node l₁ r₁) (Foo.leaf a₂))
    (fun l₂ r₂ => h₂ l₁ r₁ l₂ r₂)
    (fun h₂ t₂ => h₄ (Foo.node l₁ r₁) (Foo.cons h₂ t₂)))
  (fun h₁ t₁ => Foo.casesOn y
    (fun a₂    => h₄ (Foo.cons h₁ t₁) (Foo.leaf a₂))
    (fun l₂ r₂ => h₄ (Foo.cons h₁ t₁) (Foo.node l₂ r₂))
    (fun h₂ t₂ => h₃ h₁ t₁ h₂ t₂))

def f : List Nat → List Nat → List Nat
| x::xs, _   => []
| _,     []  => []
| xs,    ys  => xs ++ ys

def List.elim (C : List Nat → List Nat → Sort v) (xs ys : List Nat)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,      C xs [])
  (h₃ : forall xs ys,   C xs ys)
  : C xs ys :=
List.casesOn xs
  (List.casesOn ys
     (h₂ [])
     (fun y ys => h₃ [] (y::ys)))
  (fun x xs => h₁ x xs ys)

theorem List.elim.eq1 (C : List Nat → List Nat → Sort v)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,      C xs [])
  (h₃ : forall xs ys,   C xs ys)
  (x : Nat) (xs ys : List Nat)
  : List.elim C (x::xs) ys h₁ h₂ h₃ = h₁ x xs ys :=
rfl

theorem List.elim.eq2 (C : List Nat → List Nat → Sort v)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,      C xs [])
  (h₃ : forall xs ys,   C xs ys)
  (xs : List Nat)
  : (forall x' xs', xs = x'::xs' → False) → List.elim C xs [] h₁ h₂ h₃ = h₂ xs :=
List.casesOn xs
  (fun _      => rfl)
  (fun x xs h => False.elim (h x xs rfl))

theorem List.elim.eq3 (C : List Nat → List Nat → Sort v)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,      C xs [])
  (h₃ : forall xs ys,   C xs ys)
  (xs : List Nat) (ys : List Nat)
  : (forall x' xs', xs = x'::xs' → False) → (ys = [] → False) → List.elim C xs ys h₁ h₂ h₃ = h₃ xs ys :=
List.casesOn xs
  (List.casesOn ys
     (fun _ h => False.elim (h rfl))
     (fun y ys _ _ => rfl))
  (fun x xs h _ => False.elim (h x xs rfl))

theorem List.elim.eq3.a (C : List Nat → List Nat → Sort v)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,      C xs [])
  (h₃ : forall xs ys,   C xs ys)
  (y : Nat) (ys : List Nat)
  : List.elim C [] (y::ys) h₁ h₂ h₃ = h₃ [] (y::ys) :=
rfl

def List.elim2 (C : List Nat → List Nat → Sort v) (xs ys : List Nat)
  (h₁ : forall x xs ys, C (x::xs) ys)
  (h₂ : forall xs,    (forall (x' : Nat) (xs' : List Nat), xs = x' :: xs' → False) → C xs [])
  (h₃ : forall xs ys, (forall (x' : Nat) (xs' : List Nat), xs = x' :: xs' → False) → (ys = [] → False) → C xs ys)
  : C xs ys :=
List.casesOn xs
  (List.casesOn ys
     (h₂ [] (fun _ _ h => List.noConfusion h))
     (fun y ys => h₃ [] (y::ys) (fun _ _ h => List.noConfusion h) (fun h => List.noConfusion h)))
  (fun x xs => h₁ x xs ys)

def List.elim3 (C : List Nat → List Nat → List Nat → Sort v) (xs ys zs : List Nat)
  (h₁ : forall zs,       C [] [] zs)
  (h₂ : forall xs ys,    C xs ys [])
  (h₃ : forall xs ys zs, C xs ys zs)
  : C xs ys zs :=
List.casesOn xs
  (List.casesOn ys
     (h₁ zs)
     (fun y ys => List.casesOn zs
        (h₃ [] (y::ys) [])
        (fun z zs => h₃ [] (y::ys) (z::zs))))
  (fun x xs =>
    (List.casesOn zs
      (h₂ (x::xs) ys)
      (fun z zs => h₃ (x::xs) ys (z::zs))))

theorem List.elim3.eq (C : List Nat → List Nat → List Nat → Sort v)
  (h₁ : forall zs,       C [] [] zs)
  (h₂ : forall xs ys,    C xs ys [])
  (h₃ : forall xs ys zs, C xs ys zs)
  (xs ys zs : List Nat)
  : (xs = [] → ys = [] → False) → (zs = [] → False) → List.elim3 C xs ys zs h₁ h₂ h₃ = h₃ xs ys zs :=
List.casesOn xs
  (List.casesOn ys
    (fun h _  => False.elim (h rfl rfl))
    (fun y ys => List.casesOn zs
      (fun _ h => False.elim (h rfl))
      (fun z zs _ _ => rfl)))
  (fun x xs =>
    List.casesOn zs
      (fun _ h => False.elim (h rfl))
      (fun z zs _ _ => rfl))

theorem List.elim3.eq.a (C : List Nat → List Nat → List Nat → Sort v)
  (h₁ : forall zs,       C [] [] zs)
  (h₂ : forall xs ys,    C xs ys [])
  (h₃ : forall xs ys zs, C xs ys zs)
  (y : Nat) (ys : List Nat) (z : Nat) (zs : List Nat)
  : List.elim3 C [] (y::ys) (z::zs) h₁ h₂ h₃ = h₃ [] (y::ys) (z::zs) :=
rfl

theorem List.elim3.eq.b (C : List Nat → List Nat → List Nat → Sort v)
  (h₁ : forall zs,       C [] [] zs)
  (h₂ : forall xs ys,    C xs ys [])
  (h₃ : forall xs ys zs, C xs ys zs)
  (x : Nat) (xs : List Nat) (y : Nat) (ys : List Nat) (z : Nat) (zs : List Nat)
  : List.elim3 C (x::xs) (y::ys) (z::zs) h₁ h₂ h₃ = h₃ (x::xs) (y::ys) (z::zs) :=
rfl
