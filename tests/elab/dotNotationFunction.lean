/-!
# Generalized field notation for functions

Functions use the `Function` namespace, and they always take the first explicit argument that's a function.
-/

/-!
Motivating example for why it should only match explicit arguments. This `swap` function
is unusable using field notation in the intended way if it matched implicit arguments too.
https://github.com/leanprover/lean4/issues/1629
-/
def Function.swap {α β} {γ : α → β → Sort _} (f : (a : α) → (b : β) → γ a b)
  (b : β) (a : α) : γ a b := f a b

def mul : Nat → Nat → Nat := (· * ·)
/-- info: Function.swap mul : Nat → Nat → Nat -/
#guard_msgs in #check Function.swap mul -- works
/-- info: Function.swap mul : Nat → Nat → Nat -/
#guard_msgs in #check mul.swap

example : mul.swap = Function.swap mul := rfl

/-!
Function field notation can be `open`ed into other namespaces.
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/generalized.20field.20notation.20vs.20namespaces/near/582689850
-/
def MyNS.Function.apply {α} (a : α) {β : α → Sort _} (f : (x : α) → β x) : β a := f a

/-- error: Unknown constant `mul.apply` -/
#guard_msgs in #check mul.apply 2 3

/-- info: Function.apply 2 mul 3 : Nat -/
#guard_msgs in open MyNS in #check mul.apply 2 3

/-!
Function field notation can be used in recursive definitions.
-/
def Function.iterate {α} (f : α → α) (n : Nat) (x : α) : α :=
  match n with
  | 0 => x
  | n+1 => f.iterate n (f x)

/-- info: 1024 -/
#guard_msgs in #eval (·*2).iterate 10 1

/-!
Another example of a definition that is reasonable to use with field notation. This is from Mathlib.
-/
def Function.update {α : Sort u} {β : α → Sort v} [DecidableEq α]
    (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
    if h : a = a' then Eq.ndrec v h.symm else f a

/-- info: 108 -/
#guard_msgs in #eval (mul.update 2 (· + 100)) 2 8
