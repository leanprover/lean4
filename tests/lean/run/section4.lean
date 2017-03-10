set_option pp.universes true
set_option pp.implicit true

section
  universe k
  parameter A : Type

  section
    universe variable l
    universe variable u
    parameter B : Type
    definition foo (a : A) (b : B) := b

    inductive mypair
    | mk : A → B → mypair

    #print mypair.rec
    #check mypair.mk

    definition pr1' : mypair → A
    | (mypair.mk a b) := a

    definition pr2' : mypair → B
    | (mypair.mk a b) := b

  end
  #check mypair.rec
  variable a : A
  #check foo num a 0

  definition pr1 : mypair num → A
  | (mypair.mk a b) := a

  definition pr2 : mypair num → num
  | (mypair.mk a b) := b
end
