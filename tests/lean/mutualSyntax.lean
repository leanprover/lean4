mutual
notation "§" => Foo
inductive Foo where
  | mk : §
end
#print Foo
#check §
set_option pp.notation false in
#check §

mutual
local notation (priority := high) "§" => Foo.Bar
inductive Foo.Bar where
  | mk : §
end
#print Foo.Bar
set_option pp.notation false in
#check §

namespace Foo
mutual
notation "§§" => Baz
inductive Baz where
  | mk : §§
end
#print Foo.Baz
set_option pp.notation false in
#check §§
end Foo

mutual
notation:60 "⟨" c ", " σ "⟩"  " ⇓ " σ' => Bigstep c σ σ'
inductive Bigstep : Com → State → State → Prop where
  | skip : ⟨skip, σ⟩ ⇓ σ
end
#check ⟨0, 0⟩ ⇓ 0
