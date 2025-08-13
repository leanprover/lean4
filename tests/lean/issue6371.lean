set_option inductive.autoPromoteIndices false in
inductive Foo (A : Type) : (A -> A) → Type where

/-- error: (kernel) unknown constant 'Bar' -/
#guard_msgs in
inductive Bar where
  | bar : Foo Bar (fun x => x) → Bar
