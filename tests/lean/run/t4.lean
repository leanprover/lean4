namespace foo
  definition f.{l} (A : Type.{l}) : Type.{l} := A
  check f.{1}
end

variable N : Type.{1}
section
  parameter A : Type
  definition g (a : A) (B : Type) : A := a
  check g.{2}
end
check g.{2 3}

