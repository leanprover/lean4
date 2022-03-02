inductive LazyList (α : Type u)
  | nil : LazyList α
  | cons (hd : α) (tl : LazyList α) : LazyList α
  | delayed (t : Thunk (LazyList α)) : LazyList α
  deriving Inhabited

namespace LazyList

@[inline] protected def pure (a : α) : LazyList α :=
  cons a nil

/-
Length of a list is number of actual elements
in the list, ignoring delays
-/
@[simp] def length : LazyList α → Nat
  | nil        => 0
  | cons _ as  => length as + 1
  | delayed as => length as.get

@[simp] def toList : LazyList α → List α
  | nil        => []
  | cons a as  => a :: toList as
  | delayed as => toList as.get

theorem length_toList (l : LazyList α) : l.toList.length = l.length := by
  match l with
  | nil => rfl
  | cons a as => simp [length_toList as]
  | delayed as => simp [length_toList as.get]

def force : LazyList α → Option (α × LazyList α)
  | delayed as => force as.get
  | nil        => none
  | cons a as  => some (a,as)

theorem toList_force_none (l : LazyList α) : force l = none ↔ l.toList = List.nil := by
  match l with
  | nil => simp [force]
  | delayed as => simp [force, toList_force_none as.get]
  | cons a as => simp [force, toList_force_none as]

end LazyList
