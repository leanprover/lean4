import data.list data.vector

variables {A B : Type}

section
open list
theorem last_concat {x : A} : ∀ {l : list A} (h : concat x l ≠ []), last (concat x l) h = x
| []          h := rfl
| [a]         h := rfl
| (a₁::a₂::l) h :=
  by xrewrite [↑concat, ↑concat, last_cons_cons, ↓concat x (a₂::l), last_concat]

theorem reverse_append : ∀ (s t : list A), reverse (s ++ t) = (reverse t) ++ (reverse s)
| []         t2 :=
  by esimp [append, reverse]; rewrite append_nil_right
| (a2 :: s2) t2 :=
  by rewrite [↑append, ↑reverse, reverse_append, concat_eq_append, append.assoc, -concat_eq_append]
end

section
open vector nat prod

theorem unzip_zip : ∀ {n : nat} (v₁ : vector A n) (v₂ : vector B n), unzip (zip v₁ v₂) = (v₁, v₂)
| 0     []      []      := rfl
| (n+1) (a::va) (b::vb) := by rewrite [↑zip, ↑unzip, unzip_zip]

theorem zip_unzip : ∀ {n : nat} (v : vector (A × B) n), zip (pr₁ (unzip v)) (pr₂ (unzip v)) = v
| 0     []             := rfl
| (n+1) ((a, b) :: v)  := by rewrite [↑unzip,↑zip,zip_unzip]

theorem reverse_concat : Π {n : nat} (xs : vector A n) (a : A), reverse (concat xs a) = a :: reverse xs
| 0     []         a := rfl
| (n+1) (x :: xs)  a := by xrewrite [↑concat,↑reverse,reverse_concat]

theorem reverse_reverse : Π {n : nat} (xs : vector A n), reverse (reverse xs) = xs
| 0        []        := rfl
| (succ n) (x :: xs) := by rewrite [↑reverse at {1}, reverse_concat, reverse_reverse]

end
