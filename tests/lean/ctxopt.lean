import logic
definition id {A : Type} (a : A) := a

context
  set_option pp.implicit true
  check id true
end

check id true
