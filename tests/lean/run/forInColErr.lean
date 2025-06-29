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
error: don't know how to synthesize implicit argument 'ρ'
  @forIn Id (List ?_) ?_ instForInOfForIn' PUnit Id.instMonad [] PUnit.unit fun x r => do
    pure ()
    pure (ForInStep.yield PUnit.unit)
context:
⊢ Type _
---
error: failed to infer binder type
---
error: don't know how to synthesize implicit argument 'α'
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
error: don't know how to synthesize implicit argument 'd'
  @forIn' Id (List ?_) ?_ inferInstance List.instForIn'InferInstanceMembership PUnit Id.instMonad [] PUnit.unit
    fun x h r => do
    pure ()
    pure (ForInStep.yield PUnit.unit)
context:
⊢ outParam (Membership ?_ (List ?_))
---
error: don't know how to synthesize implicit argument 'ρ'
  @forIn' Id (List ?_) ?_ inferInstance List.instForIn'InferInstanceMembership PUnit Id.instMonad [] PUnit.unit
    fun x h r => do
    pure ()
    pure (ForInStep.yield PUnit.unit)
context:
⊢ Type _
---
error: failed to infer binder type
---
error: failed to infer binder type
---
error: don't know how to synthesize implicit argument 'α'
  @List.nil ?_
context:
⊢ Type _
-/
#guard_msgs in
example : Unit := Id.run do
  for h : x in [] do
    pure ()
  pure ()
