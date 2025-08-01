/-!
# Tests that type annotations in binders are cleaned up when elaborating declaration bodies
-/

set_option linter.unusedVariables false

/-!
Test definitions, theorems, and instances. (MutualDef elaborator)
Both scope variables and header variables are handled.
-/

variable (a := true)

/--
trace: a : Bool
b : Nat
⊢ True
-/
#guard_msgs in
def d1 (b := 0) : Bool :=
  have : True := by trace_state; trivial
  a

/-- info: d1 (a : Bool := true) (b : Nat := 0) : Bool -/
#guard_msgs in #check d1

/--
trace: a : Bool
h : a = true
b : Nat
⊢ True
-/
#guard_msgs in
theorem t1 (h : a) (b := 0) : True := by
  trace_state
  trivial

/-- info: t1 (a : Bool := true) (h : a = true) (b : Nat := 0) : True -/
#guard_msgs in #check t1

/--
trace: a : Bool
b : Nat
⊢ True
-/
#guard_msgs in
instance i1 (b := 0) : Decidable (a.toNat = b) :=
  have : True := by trace_state; trivial
  inferInstance

/-- info: i1 (a : Bool := true) (b : Nat := 0) : Decidable (Bool.toNat a = b) -/
#guard_msgs in #check i1

/-!
Mutually recursive functions still can make use of optional parameters
-/
mutual
def d2 (b := 0) (c : Bool := true) : Bool :=
  if c then
    match b with
    | 0 => true
    | b' + 1 => d3 b'
  else
    true
def d3 (b := 0) : Bool :=
  d2 b
end
/-- info: d2 (b : Nat := 0) (c : Bool := true) : Bool -/
#guard_msgs in #check d2
/-- info: d3 (b : Nat := 0) : Bool -/
#guard_msgs in #check d3
