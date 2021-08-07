example : Prop := ∀ n, (n:Nat) + n = n.succ
example : Prop := ∀ n, n.succ = (n:Nat) + n
example : Prop := ∀ n, (n:Nat) + n.succ = n
example : Prop := ∀ n, n.succ + (n:Nat) = n
example : Prop := ∀ n, (n.succ:Nat) + n = n
example : Prop := ∀ n, (n:Nat).succ + n = n

def fib: Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib n + fib (n + 1)

theorem fib50Eq : fib 50 = 12586269025 :=
  rfl

inductive type : Type
  | A : type
  | B  : type

inductive val : type → Type
  | cA : val type.A
  | cB : val type.B

inductive wrap : Type
  | val : ∀ {t : type}, (val t) → wrap

def f : wrap → Nat
  | wrap.val val.cA => 1
  | _ => 1

example (a : Nat) : True := by
  have : ∀ n, n ≥ 0 → a ≤ a := fun _ _ => Nat.le_refl ..
  exact True.intro

example (ᾰ : Nat) : True := by
  have : ∀ n, n ≥ 0 → ᾰ ≤ ᾰ := fun _ _ => Nat.le_refl ..
  exact True.intro

inductive Vec.{u} (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (Nat.succ n) -- TODO: investigate why +1 doesn't work here

constant Vars : Type

structure Lang :=
  (funcs : Nat → Type)
  (consts : Type)

inductive Term (L : Lang) : Type
  | const_term : L.consts → Term L
  | var_term   : Vars → Term L
  | func_term  (n : Nat) (f : L.funcs n) (v : Vec (Term L) n) : Term L
