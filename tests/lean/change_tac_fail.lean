import data.list
open list

variable {T : Type}

theorem append.assoc : ∀ (s t u : list T), s ++ t ++ u = s ++ (t ++ u)
| append.assoc nil t u      := by esimp
| append.assoc (a :: l) t u :=
  begin
    change (a :: (l ++ t ++ u) = (a :: l) ++ (t ++ a)),
    rewrite append.assoc
  end
