module

/-!
Regression tests for #15302: unused private section variables must not prevent public instance
name generation. Enabling the naming trace must not prevent named instances from being created.
-/

namespace UnusedPrivateVariable

public class A (α : Type) where
public structure B where
class C where

variable [C]

public instance : A B := {}

example : A B := instAB
example : A B := inferInstance

#guard_msgs (drop trace) in
set_option trace.Elab.instance.mkInstanceName true in
public instance named : A B := {}

example : A B := named

end UnusedPrivateVariable

namespace ExplicitPrivateBinder

public class A (α : Type) where
public structure B where
class C where

/--
error: Unknown identifier `C`

Note: A private declaration `C` (from the current module) exists but would need to be public to access here.
-/
#guard_msgs in
public instance [C] : A B := {}

end ExplicitPrivateBinder
