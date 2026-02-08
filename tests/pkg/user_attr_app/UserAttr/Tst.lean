import UserAttr.BlaAttr

@[bla] def f (x : Nat) := x + 2
@[bla] def g (x : Nat) := x + 1

@[testPred] coinductive infSeq (r : α → α → Prop) : α → Prop where
  | mk : r a b → infSeq r b → infSeq r a
