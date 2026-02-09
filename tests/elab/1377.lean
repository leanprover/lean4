def foo: Unit := ()
where
  bar: (_: Unit) → {n : Nat} → Fin n → Fin n
  | _, _, _ => sorry

#check foo.bar
