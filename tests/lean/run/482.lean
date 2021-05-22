inductive Mem' (a : α) : List α → Prop where
  | intro (as bs) : Mem' a (as ++ (a :: bs))

example {x : α} (h : Mem' x l) : True :=
  match h with
  | ⟨as', bs'⟩ => True.intro

example {x : α} (h : Mem' x l ∧ Mem' x l') : True :=
  match h with
  | ⟨⟨as', bs'⟩, _⟩ => True.intro
