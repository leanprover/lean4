constants (A B C : Prop) (H : A → B) (G : A → B → C)
constants (T : Type) (f : T → A)
attribute H [intro]
attribute G [intro]
attribute f [intro]

print H
print G
print f

print [intro]
