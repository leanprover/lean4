set_option new_elaborator true
open tactic

example : true :=
by do
   trace $ "hello",
   constructor
