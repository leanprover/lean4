set_option pp.mvars.anonymous false

/--
error: typeclass instance problem is stuck
  ForInNew Id ?_ ?α

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `ForInNew` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
example {c} := Id.run do
  for x in c do
    pure ()
  pure ()


/--
error: don't know how to synthesize implicit argument `α`
  @List.nil ?_
context:
⊢ Type _
-/
#guard_msgs in
example : Unit := Id.run do
  for x in [] do
    pure ()
  pure ()

/--
error: typeclass instance problem is stuck
  ForInNew' Id ?_ ?α ?p

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `ForInNew'` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
example {c} := Id.run do
  for h : x in c do
    pure ()
  pure ()

/--
error: don't know how to synthesize implicit argument `α`
  @List.nil ?_
context:
⊢ Type _
-/
#guard_msgs in
example : Unit := Id.run do
  for h : x in [] do
    pure ()
  pure ()
