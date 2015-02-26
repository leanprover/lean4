inductive list (T : Type) : Type := nil {} : list T | cons   : T → list T → list T

namespace explicit

inductive ftree.{l₁ l₂} (A : Type.{l₁}) (B : Type.{l₂}) : Type.{max 1 l₁ l₂} :=
leafa : A → ftree A B |
leafb : B → ftree A B |
node  : (A → ftree A B) → (B → ftree A B) → ftree A B

end explicit

namespace implicit

inductive ftree (A : Type) (B : Type) : Type :=
leafa : ftree A B |
node  : (A → B → ftree A B) → (B → ftree A B) → ftree A B

set_option pp.universes true
check ftree
end implicit


namespace implicit2

inductive ftree (A : Type) (B : Type) : Type :=
leafa : A → ftree A B |
leafb : B → ftree A B |
node  : (list A → ftree A B) → (B → ftree A B) → ftree A B

check ftree
end implicit2
