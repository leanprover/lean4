class MyClass (α : Type u) where
  point : α

/--
error: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 3: `(n : Nat)`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance bad1 {α : Type} [Inhabited α] (n : Nat) : MyClass α := sorry

/--
error: This instance has 2 arguments that cannot be inferred using typeclass synthesis. Specifically

  argument 3: `(n : Nat)`
  argument 4: `(m : Nat)`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance bad2 {α : Type} [Inhabited α] (n m : Nat) : MyClass α := sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance good {α : Type} [Inhabited α] : MyClass α := sorry

/--
error: This instance has 4 arguments that cannot be inferred using typeclass synthesis. Specifically

  argument 2: `{β : Type}`
  argument 3: `(b : Array β)`
  argument 4: `(a : Array α)`
  argument 6: `⦃h : b = b⦄`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.
---
warning: declaration uses `sorry`
-/
#guard_msgs in
instance bad3 {α β : Type} (b : Array β) (a : Array α) [Inhabited α]
    ⦃h : b = b⦄
    -- Note: `usedA` is a dependency of a dependency of a dependency of the return type
    (usedA : Array α) (i : Fin usedA.size) (j : Fin i.val) :
    Nonempty { ar : Array α // ar.size = j.val } := sorry

-- The following checks that the error shows up at line containing `attribute`
-- (and not at line where the decl is defined).
/-- warning: declaration uses `sorry` -/
#guard_msgs in
@[implicit_reducible]
def bad4 {α : Type} [Inhabited α] (n : Nat) : MyClass α := sorry

/--
error: This instance has 1 argument that cannot be inferred using typeclass synthesis. Specifically

  argument 3: `(n : Nat)`

These arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis.
-/
#guard_msgs in
attribute [instance] bad4

/-- warning: declaration uses `sorry` -/
#guard_msgs in
instance bad5 : sorry := sorry
