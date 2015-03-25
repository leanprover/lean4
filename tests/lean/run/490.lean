structure foo.{l} : Type.{l+2} :=
(elim : Type.{l} → Type.{l})

set_option pp.universes true
check foo.elim
check foo
