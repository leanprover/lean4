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
A parameter
-/
structure A2 (n : Nat) where
  x : Fin n
  xs : List (A2 n)

/-- info: A2 (n : Nat) : Type -/
#guard_msgs in #check A2

/-!
A variable
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
      acc := acc ++ (children ⟨i, h.2⟩).preorder
    return acc

/-- info: Foo'.preorder : Foo' → String -/
#guard_msgs in #check Foo'.preorder

/-!
Expected failure to use numeric projection notation.
This should be fixed at some point. A number of processes assume is_structure_like.
-/
section
variable (a : A1)
/--
error: invalid projection, structure expected
  a
has type
  A1
-/
#guard_msgs in #check a.1
end

/-!
Extending with default values.
-/
structure A5 extends A4 Nat Bool where
  x := 0
  y := true

/-!
Incidental new feature: checking projections when the structure is Prop.
-/
/-- error: failed to generate projections for 'Prop' structure, field 'x' is not a proof -/
#guard_msgs in
structure Exists' {α : Sort _} (p : α → Prop) : Prop where
  x : α
  h : p x
