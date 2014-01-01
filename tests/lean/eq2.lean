Import Int.
Variable List : Type -> Type
Variable nil  {A : Type} : List A
Variable cons {A : Type} (head : A) (tail : List A) : List A
Variable l : List Int.
Check l = nil.
SetOption pp::implicit true
Check l = nil.
