namespace ex
constant array : Type
constant read : array → nat → nat
constant write : array → nat → nat → array
axiom rw1 : ∀ a i v, read (: write a i v :) i = v
axiom rw2 : ∀ a i j v, i = j ∨ (: read (write a i v) j :) = read a j

attribute [ematch] rw1 rw2

lemma ex3 (a1 a2 a3 a4 a5 : array) (v : nat) :
a2 = write a1 0 v →
a3 = write a2 1 v →
a4 = write a3 2 v →
a5 = write a4 3 v →
read a5 4 = read a1 4
:=
begin [smt]
  intros, eblast
end

end ex
