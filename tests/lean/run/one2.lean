import data.num

inductive one.{l} : Type.{l} :=
unit : one

inductive pone : Type.{0} :=
unit : pone

inductive two.{l} : Type.{max 1 l} :=
| o : two
| u : two

inductive wrap.{l} : Type.{max 1 l} :=
mk : true → wrap

inductive wrap2.{l} (A : Type.{l}) : Type.{max 1 l} :=
mk : A → wrap2 A

set_option pp.universes true
check @one.rec
check @pone.rec
check @two.rec
check @wrap.rec
check @wrap2.rec
