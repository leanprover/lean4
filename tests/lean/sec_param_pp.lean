section
 parameters {A : Type} (a : A)
 variable f : A → A → A

 definition id2 : A := a
 check id2


 definition pr (b : A) : A := f a b

 check pr f id2

 set_option pp.universes true

 check pr f id2

 definition pr2 (B : Type) (b : B) : A := a

 check pr2 num 10
end
