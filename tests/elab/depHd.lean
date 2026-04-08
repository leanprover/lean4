def Hd : List α → Type
  | []     => PUnit
  | a :: _ => α

def hd : (as : List α) → Hd as
  | []     => ()
  | a :: l => a

theorem inj_hd (α : Type) : (a a': α) → (l l' : List α) → a :: l = a' :: l' → a = a' := by
  intro a a' l l' h
  show hd (a :: l) = hd (a' :: l')
  cases h
  rfl
