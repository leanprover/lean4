import logic data.unit

set_option pp.universes true

context
  parameter (A : Type)

  context
    parameter (B : Type)

    structure point :=
    mk :: (x : A) (y : B)

    check point
    check point.mk
    check point.x
  end

  check point
  check point.mk
  check point.x
end
