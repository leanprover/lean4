module

/-!
Declarations with their own visibility (`public instance`, `public axiom`, ...) must elaborate the
section variables with the visibility of the enclosing scope, not with their own (#15302).
Otherwise an unused section variable whose type is a private class fails to elaborate, and for
anonymous instances this failure happened during instance name generation, where the error was
discarded and the instance was silently not created.
-/

public class A (α : Type) where
public structure B where

class C where

variable [C]

public instance : A B := {}

/-- info: instAB : A B -/
#guard_msgs in
#check instAB

public axiom ax : A B

/-- info: ax : A B -/
#guard_msgs in
#check ax

public structure S where
  x : Nat

/-- info: S : Type -/
#guard_msgs in
#check S

public inductive T where
  | a

/-- info: T : Type -/
#guard_msgs in
#check T

-- A `public` declaration whose own signature mentions the private class is still rejected.
/--
error: Unknown identifier `C`

Note: A private declaration `C` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public instance [C] : A B := {}
