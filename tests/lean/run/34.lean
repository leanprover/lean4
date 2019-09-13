partial def foo : ∀ (n : Nat), State Unit Unit
| n =>
  if n == 0 then pure () else
  match n with
  | 0   => pure ()
  | n+1 => foo n
