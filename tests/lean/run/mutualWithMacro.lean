module

/-! Macros unfolding to legal `mutual` element(s) are accepted by `mutual`. -/

macro "single" name:ident arg:ident : command =>
  `(inductive $name where | mk : $arg → $name)

mutual

single Foo Bar

inductive Bar where
  | mk : Foo → Bar

end


macro "double" name1:ident name2:ident : command =>
  `(inductive $name1 where | mk : $name2 → $name1
    inductive $name2 where | mk : $name1 → $name2)

mutual

double Foo2 Bar2

end
