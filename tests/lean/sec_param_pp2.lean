section
 parameters {A : Type} (a : A)

 section
   parameters {B : Type} (b : B)

   variable f : A → B → A

   definition id2 := f a b

   check id2
   set_option pp.universes true
   check id2
 end
 check id2
end
check id2
