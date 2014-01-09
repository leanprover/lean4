import Int.
variable List : Type -> Type
variable nil  {A : Type} : List A
variable cons {A : Type} (head : A) (tail : List A) : List A
variable l : List Int.
check l = nil.
set_option pp::implicit true
check l = nil.
