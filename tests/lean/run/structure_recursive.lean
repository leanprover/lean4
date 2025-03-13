/-!
# Tests for recursive structures
-/

/-!
No parameters, variables, or universes.
-/
structure A1 where
  xs : List A1

/-- info: A1 : Type -/
#guard_msgs in #check A1

/-!
Projections
-/
section
variable (a : A1)
/-- info: a.xs : List A1 -/
#guard_msgs in #check a.xs
/-- info: a.xs : List A1 -/
#guard_msgs in #check a.1
end

/-!
A parameter
-/
structure A2 (n : Nat) where
  x : Fin n
  xs : List (A2 n)

/-- info: A2 (n : Nat) : Type -/
#guard_msgs in #check A2

/-!
Numeric projections
-/
section
variable (a : A2 2)
/-- info: a.x : Fin 2 -/
#guard_msgs in #check a.x
/-- info: a.xs : List (A2 2) -/
#guard_msgs in #check a.xs
/-- info: a.x : Fin 2 -/
#guard_msgs in #check a.1
/-- info: a.xs : List (A2 2) -/
#guard_msgs in #check a.2
end

/-!
A `variable`
-/
section
variable (n : Nat)

structure A3 where
  x : Fin n
  xs : List A3

/-- info: A3 (n : Nat) : Type -/
#guard_msgs in #check A3
end

/-!
A variable and parameter with universe metavariables
-/
section
variable (α : Type _)

structure A4 (β : Type _) where
  x : α
  y : β
  xs : List (A4 β)

/-- info: A4.{u_1, u_2} (α : Type u_1) (β : Type u_2) : Type (max u_1 u_2) -/
#guard_msgs in #check A4
end

/-!
Example from https://github.com/leanprover/lean4/issues/2512
-/
structure Foo where
  name     : String
  children : List Foo

/-!
Defining a recursive function on a recursive structure
-/
structure Foo' where
  name     : String
  n : Nat
  children : Fin n → Foo'

def Foo'.preorder : Foo' → String
  | {name, n, children} => Id.run do
    let mut acc := name
    for h : i in [0:n] do
      acc := acc ++ (children ⟨i, h.2.1⟩).preorder
    return acc

/-- info: Foo'.preorder : Foo' → String -/
#guard_msgs in #check Foo'.preorder

/-!
Extending with default values.
-/
structure A5 extends A4 Nat Bool where
  x := 0
  y := true

/-!
Default value whose type depends on the recursive structure.
Reported in https://github.com/leanprover/lean4/issues/6140
-/

structure RecS where
  n : Nat
  recS : Option RecS := none

/-- info: { n := 0, recS := none } : RecS -/
#guard_msgs in #check ({ n := 0 } : RecS)

/-!
Incidental new feature: checking projections when the structure is Prop.
-/
/--
error: failed to generate projection 'Exists'.x' for the 'Prop'-valued type 'Exists'', field must be a proof, but it has type
  α
-/
#guard_msgs in
structure Exists' {α : Sort _} (p : α → Prop) : Prop where
  x : α
  h : p x

/-!
Testing numeric projections on recursive inductive types now that the elaborator isn't restricted to structure-likes.
-/
inductive I1 where
  | mk (x : Nat) (xs : I1)
/-- info: fun v => v.1 : I1 → Nat -/
#guard_msgs in #check fun (v : I1) => v.1
/-- info: fun v => v.2 : I1 → I1 -/
#guard_msgs in #check fun (v : I1) => v.2

inductive I2 : Nat → Type where
  | mk (x : Nat) (xs : I2 (x + 1)) : I2 x
/-- info: fun v => v.1 : I2 2 → Nat -/
#guard_msgs in #check fun (v : I2 2) => v.1
/-- info: fun v => v.2 : (v : I2 2) → I2 (v.1 + 1) -/
#guard_msgs in #check fun (v : I2 2) => v.2
