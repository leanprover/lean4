import logic


section
  universe l
  variable A : Type.{l}
  variable a : A
  parameter B : Type.{l}
  parameter b : B

  definition foo := fun (H : A = B), cast H a = b
end

check foo
