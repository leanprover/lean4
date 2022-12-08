def g {α : Type}   (a : α) := a
def f {{α : Type}} (a : α) := a

#check g
#check f
#check g 1
#check f 1
