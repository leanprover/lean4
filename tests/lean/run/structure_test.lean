import logic data.sigma

inductive point (A B : Type) :=
mk : Π (x : A) (y : B), point A B

inductive color [class] :=
red | green | blue

constant foo.{l} (A : Type.{l}) [H : decidable_eq A] : Type.{l}

constants a : num

section
  universe variable l
  variable A : Type.{l}
  variable Ha : decidable_eq A
  include Ha
  variable E : Type₂
  include E
   -- include Ha

  structure point3d_color (B C : Type) (D : B → Type) extends point (foo A) B, sigma D renaming pr1→y pr2→w :=
  mk :: (c : color) (H : x == y)

  check point3d_color.c

  check point3d_color.to_point
end

section
  universe l
  parameters A : Type.{l}
  parameters B : Type.{l}

  structure tst :=
  mk :: (a : A) (b : B)

end
