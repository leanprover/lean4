set_option pp.mvars.anonymous false

/--
error: failed to construct 'ForIn' instance for collection
  ?_
and monad
  Id
-/
#guard_msgs in
example {c} := Id.run do
  for x in c do
    pure ()
  pure ()


/--
error: Implicit argument could not be inferred in application of `List.nil`.

The argument `α` is not determined by the other arguments or the expected type in
  @List.nil ?_

context:
⊢ Type _
---
error: Failed to infer type for binder `x`.

context:
⊢ Type _
---
error: Implicit argument could not be inferred in application of `forIn`.

The argument `ρ` is not determined by the other arguments or the expected type in
  @forIn Id (List ?_) ?_ instForInOfForIn' PUnit Id.instMonad [] PUnit.unit fun x r => do
    pure ()
    pure (ForInStep.yield PUnit.unit)

Argument `ρ` has partial assignment
  List ?_

context:
⊢ Type _
-/
#guard_msgs in
example : Unit := Id.run do
  for x in [] do
    pure ()
  pure ()

/--
error: failed to construct `ForIn'` instance for collection
  ?_
and monad
  Id
-/
#guard_msgs in
example {c} := Id.run do
  for h : x in c do
    pure ()
  pure ()

/--
error: Implicit argument could not be inferred in application of `List.nil`.

The argument `α` is not determined by the other arguments or the expected type in
  @List.nil ?_

context:
⊢ Type _
---
error: Failed to infer type for binder `x`.

context:
⊢ Type _
---
error: Failed to infer type for binder `h`.

Partial assignment
  x ∈ []

context:
x : ?_
⊢ Prop
---
error: Implicit arguments could not be inferred in application of `forIn'`.

The arguments `ρ` and `d` are not determined by the other arguments or the expected type in
  @forIn' Id (List ?_) ?_ inferInstance List.instForIn'InferInstanceMembership PUnit Id.instMonad [] PUnit.unit
    fun x h r => do
    pure ()
    pure (ForInStep.yield PUnit.unit)

Argument `ρ` has partial assignment
  List ?_

Argument `d` has partial assignment
  inferInstance

context:
⊢ Type _
-/
#guard_msgs in
example : Unit := Id.run do
  for h : x in [] do
    pure ()
  pure ()
