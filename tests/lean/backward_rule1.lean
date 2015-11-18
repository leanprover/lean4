constants (A B C : Prop) (H : A → B) (G : A → B → C)
constants (T : Type) (f : T → A)
attribute H [backward]
attribute G [backward]
attribute f [backward]

print H
print G
print f

print [backward]
