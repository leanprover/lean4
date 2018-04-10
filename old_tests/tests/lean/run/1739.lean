inductive type
| bool : type
| fn : list type → type → type

def f : type → nat
| (type.bool)       := 0
| (type.fn args rt) := 1
