set_option inductive.autoPromoteIndices false in
inductive Foo (A : Type) : (A -> A) → Type where

/--
error: In argument #1 of constructor Bar.bar:
  Invalid occurrence of inductive type `Bar`, must not occur in index of `Foo`
-/
#guard_msgs in
inductive Bar where
  | bar : Foo Bar (fun x => x) → Bar
