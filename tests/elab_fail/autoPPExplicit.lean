def f {a b c : α} : a = c :=
  Eq.trans (a := a) (b := b = c)
