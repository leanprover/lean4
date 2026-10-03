import Lean

/-!
Tests that `newtype` handles parameters exactly like `def`: explicit binders, universe parameters,
section variables and auto-bound implicits. As for `structure`, explicit parameters become implicit
in the generated constructor and projector, and virtual iota/eta as well as `unsealing_newtype`
work in the presence of parameters.
-/

universe u

newtype OrderDual (α : Type u) := α with ofDual

/-- info: OrderDual.{u} (α : Type u) : Type u -/
#guard_msgs in #check OrderDual
/-- info: OrderDual.mk.{u} {α : Type u} (ofDual : α) : OrderDual α -/
#guard_msgs in #check OrderDual.mk
/-- info: OrderDual.ofDual.{u} {α : Type u} (self : OrderDual α) : α -/
#guard_msgs in #check OrderDual.ofDual

example (a : α) : OrderDual.ofDual (OrderDual.mk a) = a := rfl
example (x : OrderDual α) : OrderDual.mk (OrderDual.ofDual x) = x := rfl
example (a : α) : (OrderDual.mk a).ofDual = a := by simp only
example : OrderDual α = α := by unsealing_newtype OrderDual => rfl

section
variable (β : Type) [Inhabited β]

newtype Wrap := List β with toList

/-- info: Wrap (β : Type) : Type -/
#guard_msgs in #check Wrap
/-- info: Wrap.mk {β : Type} (toList : List β) : Wrap β -/
#guard_msgs in #check Wrap.mk

-- The unused instance variable is not included, as for `def`.
example (l : List β) : (Wrap.mk l).toList = l := rfl
end

-- Auto-bound universe levels in the binders, as for `def`.
newtype Wrap' (γ : Type _) := Option γ with get

/-- info: Wrap'.{u_1} (γ : Type u_1) : Type u_1 -/
#guard_msgs in #check Wrap'
/-- info: Wrap'.mk.{u_1} {γ : Type u_1} (get : Option γ) : Wrap' γ -/
#guard_msgs in #check Wrap'.mk

example (o : Option γ) : (Wrap'.mk o).get = o := rfl

/-- doc -/
private newtype Priv (n : Nat) := Fin n with val

example (i : Fin 3) : (Priv.mk i).val = i := rfl

/-- error: invalid `newtype`, the right-hand side must be a type, but has type
  Nat -/
#guard_msgs in newtype Bad := 5 with val
