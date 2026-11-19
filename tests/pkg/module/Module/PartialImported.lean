module

public import Module.PartialExported

/-!
A `partial` definition must not become usable in safe declarations just because it crossed a module
boundary as an axiom stub.
-/

/--
error: (kernel) invalid declaration, it uses unsafe declaration 'partialFalse'
-/
#guard_msgs in
public theorem partialBoom : _root_.False :=
  partialFalse
