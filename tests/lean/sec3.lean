section
  parameter A : Type
  definition tst (a : A) := a
  set_option pp.universes true
  check tst.{1}
end
