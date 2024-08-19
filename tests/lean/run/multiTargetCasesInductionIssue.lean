def Vec (α : Type u) (n : Nat) : Type u := { a : List α // a.length = n }
def Vec.nil : Vec α 0 := ⟨[], rfl⟩
def Vec.cons (a : α) (as : Vec α n) : Vec α (n+1) := ⟨a :: as.val, by simp [as.property]⟩

set_option pp.analyze false
set_option linter.unusedVariables false
set_option pp.mvars false

def Vec.casesOn
     (motive : (n : Nat) → Vec α n → Sort v)
     (n  : Nat)
     (as : Vec α n)
     (nil : motive 0 Vec.nil)
     (cons : (n : Nat) → (a : α) → (as : Vec α n) → (ih : motive n as) → motive (n+1) (Vec.cons a as))
     : motive n as :=
  let rec go (n : Nat) (as : List α) (h : as.length = n) : motive n ⟨as, h⟩ :=
    match n, as, h with
    | 0,   [],    _ => nil
    | n+1, a::as, h =>
      have : as.length = n := by injection h
      have ih : motive n ⟨as, this⟩ := go n as this
      cons n a ⟨as, this⟩ ih
  match as with
  | ⟨as, h⟩ => go n as h

/--
info: α : Type u_1
n✝ : Nat
a✝ : α
as✝ : Vec α n✝
x✝ n : Nat
a : α
as : Vec α n
ih : as = as
⊢ Vec.cons a as = Vec.cons a as
-/
#guard_msgs in
example (n : Nat) (a : α) (as : Vec α n) : Vec.cons a (Vec.cons a as) = Vec.cons a (Vec.cons a as) := by
  induction n+2, Vec.cons a (Vec.cons a as) using Vec.casesOn
  case nil => constructor
  case cons n a as ih =>
    trace_state
    constructor

/--
info: α : Type u_1
n✝ : Nat
a✝ : α
as✝ : Vec α n✝
n : Nat
a : α
as : Vec α n
ih : n + 1 = n → HEq (Vec.cons a as) as → Vec.cons a as = Vec.cons a as
⊢ Vec.cons a as = Vec.cons a as
-/
#guard_msgs in
example (n : Nat) (a : α) (as : Vec α n) : Vec.cons a (Vec.cons a as) = Vec.cons a (Vec.cons a as) := by
  cases n+2, Vec.cons a (Vec.cons a as) using Vec.casesOn
  case nil => constructor
  case cons n a as ih =>
    trace_state
    constructor

/--
info: α : Type u_1
n : Nat
a : α
as : Vec α n
n' : Nat
a' : α
as' : Vec α n'
h₁ : n + 2 = n' + 1
h₂ : HEq (Vec.cons a (Vec.cons a as)) (Vec.cons a' as')
ih : n' + 1 = n' → HEq (Vec.cons a' as') as' → Vec.cons a' as' = Vec.cons a' as'
⊢ Vec.cons a' as' = Vec.cons a' as'
-/
#guard_msgs in
example (n : Nat) (a : α) (as : Vec α n) : Vec.cons a (Vec.cons a as) = Vec.cons a (Vec.cons a as) := by
  cases h₁ : n+2, h₂ : Vec.cons a (Vec.cons a as) using Vec.casesOn
  case nil => constructor
  case cons n' a' as' ih =>
    trace_state
    constructor
