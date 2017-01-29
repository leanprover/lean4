inductive List (T : Sort*) : Sort* | nil {} : List | cons   : T → List → List

namespace explicit

inductive {u₁ u₂} ftree (A : Type u₁) (B : Type u₂) : Type (max 1 u₁ u₂)
| leafa : A → ftree
| leafb : B → ftree
| node  : (A → ftree) → (B → ftree) → ftree

end explicit

namespace implicit

inductive ftree (A : Type) (B : Type) : Type
| leafa : ftree
| node  : (A → B → ftree) → (B → ftree) → ftree

set_option pp.universes true
check ftree
end implicit


namespace implicit2

inductive ftree (A : Type) (B : Type) : Type
| leafa : A → ftree
| leafb : B → ftree
| node  : (List A → ftree) → (B → ftree) → ftree
set_option pp.universes true
check ftree
end implicit2
