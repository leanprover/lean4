open nat

notation `foo` a :=
  match a with
   (c, d) := c +[nat] d
  end

eval foo (2, 3)

notation `bla` a `with` H := a ↓ H
