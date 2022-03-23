inductive HList : List (Type u) → Type (u+1)
  | nil  : HList []
  | cons : α → HList αs → HList (α::αs)

-- Overload `::` notation for HLists
infixr:67 " :: " => HList.cons

-- Overload `[]` notation for HLists
syntax (name := hlist) "[" term,* "]"  : term
macro_rules (kind := hlist)
  | `([ ])           => `(HList.nil)
  | `([ $a ])        => `(HList.cons $a HList.nil)
  | `([ $a, $as,* ]) => `(HList.cons $a [$as,*])

def List.nth : (as : List α) → (i : Fin as.length) → α
  | a::as, ⟨0, _⟩   => a
  | a::as, ⟨i+1, h⟩ => nth as ⟨i, Nat.lt_of_succ_lt_succ h⟩

def HList.nth : HList αs → (n : Fin αs.length) → αs.nth n
  | x::_,  ⟨0, _⟩   => x
  | _::xs, ⟨n+1, h⟩ => xs.nth ⟨n, Nat.lt_of_succ_lt_succ h⟩

def HList.length : HList αs → Nat
  | []    => 0
  | _::xs => xs.length

-- Helper notation for creating Fin literals
notation:max "#" a:max  => (Fin.mk a (by decide))

example : [10, true, 20.1].nth #0 = (10:Nat) := rfl
example : [10, true, 20.1].nth #1 = true     := rfl
example : [10, true, 20.1].nth #2 = 20.1     := rfl

#eval [10, true, 20.1].nth #0
#eval [10, true, 20.1].nth #1
#eval [10, true, 20.1].nth #2

def HListPatternMatch (l : HList [Nat, String]) :=
  match l with
  | [1, "2"] => true
  | [2, "1"] => true
  | _ => false

#eval HListPatternMatch [1, "2"]
#eval HListPatternMatch [2, "1"]
#eval HListPatternMatch [3, "1"]

example : HListPatternMatch [1, "2"] := rfl
example : HListPatternMatch [2, "1"] := rfl
example : !HListPatternMatch [3, "1"] := rfl

example : HListPatternMatch (1 :: "2" :: []) := rfl

instance : Repr (HList []) where
  reprPrec xs _ := "[]"

instance [Repr α] (αs : List Type) [Repr (HList αs)] : Repr (HList (α :: αs)) where
  reprPrec xs _ :=
    match xs with
    | x :: xs => repr x ++ " :: " ++ repr xs

def xs : HList [Nat, String, Bool] := [0, "hello", true]

#eval xs
-- 0 :: "hello" :: true :: []

def ys : HList (([Nat] : List Type) ++ ([String, Bool] : List Type)) := 0 :: "hello" :: true :: []

#eval ys

example : xs = ys :=
  rfl
