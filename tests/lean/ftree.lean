inductive List (T : Type) : Type | nil {} : List | cons   : T → List → List

namespace explicit

inductive ftree.{l₁ l₂} (A : Type.{l₁}) (B : Type.{l₂}) : Type.{max 1 l₁ l₂}
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
