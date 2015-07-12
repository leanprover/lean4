import data.vector
open nat vector

variable {A : Type}

definition rev : Π {n : nat}, vector A n → vector A n
| ⌞0⌟     []      := []
| ⌞n+1⌟ (x :: xs) := concat (rev xs) x

theorem rev_concat : Π {n : nat} (xs : vector A n) (a : A), rev (concat xs a) = a :: rev xs
| 0     []         a := rfl
| (n+1) (x :: xs)  a :=
  begin
    unfold [concat, rev], rewrite rev_concat
  end

theorem rev_rev : Π {n : nat} (xs : vector A n), rev (rev xs) = xs
| 0     []        := rfl
| (n+1) (x :: xs) :=
  begin
    unfold rev at {1}, krewrite rev_concat, rewrite rev_rev
  end
