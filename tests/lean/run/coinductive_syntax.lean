set_option trace.Elab.inductive true

coinductive infSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → infSeq r b → infSeq r a
  | symm : infSeq r a

#check infSeq
mutual
  coinductive Tick : Prop where
  | mk : Tock → Tick

  coinductive Tock : Prop where
  | mk : Tick → Tock
end
