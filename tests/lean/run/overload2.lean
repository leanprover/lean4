import standard
inductive F2 : Type
| O : F2
| I : F2

namespace F2

definition add : F2 → F2 → F2
| O O := O
| O I := I
| I O := I
| I I := O

infix + := F2.add

end F2

open F2 nat

eval (1 : nat) + 1
eval (1 : nat) + (1 : nat)

example :  true :=
begin
 assert H : (1 : nat) + (1 : nat) = 2,
 reflexivity,
 constructor
end

example :  true :=
begin
 assert H : 1 + 1 = 2,
 reflexivity,
 constructor
end

example :  true :=
begin
 assert H : (1:nat) + 1 = 2,
 reflexivity,
 constructor
end

example :  true :=
begin
 assert H : I + O = I,
 reflexivity,
 constructor
end

example :  true :=
begin
 assert H1 : I + O = I,
 reflexivity,
 assert H2 : 1 + 0 = 1,
 reflexivity,
 assert H3 : (1:int) + 0 = 1,
 reflexivity,
 constructor
end
