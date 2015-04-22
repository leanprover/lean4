section
 parameters {A : Type} (a : A)

 section
   parameters {B : Type} (b : B)

   variable f : A → B → A

   definition id := f a b

   check id
   set_option pp.universes true
   check id
 end
 check id
end
check id
