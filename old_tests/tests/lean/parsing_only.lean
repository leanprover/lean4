--

constant f : nat → nat
constant g : nat → nat
notation a `+++` := f a
notation [parsing_only] a `***` := g a
#check 10 +++
#check 10 ***
#check Type.{8}  -- Type₊ should not be used
