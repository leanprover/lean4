import logic
definition id {A : Type} (a : A) := a
check id id
set_option pp.universes true
check id id
check id Prop
check id num
check @id.{0}
check @id.{1}
check id num.zero
check @eq
check eq eq
