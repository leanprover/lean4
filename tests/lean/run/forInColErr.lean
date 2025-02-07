/--
error: failed to construct 'ForIn' instance for collection
  ?m.2
and monad
  Id
-/
#guard_msgs in
example {c} := Id.run do
  for x in c do
    pure ()
  pure ()
