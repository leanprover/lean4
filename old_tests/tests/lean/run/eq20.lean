open nat list

section
  parameter {A : Type}
  parameter (p : A → Prop)
  parameter [H : decidable_pred p]
  include H

  definition filter : list A → list A
  | nil      := nil
  | (a :: l) := if p a then a :: filter l else filter l

  theorem filter_nil : filter nil = nil :=
  rfl

  theorem filter_cons (a : A) (l : list A) : filter (a :: l) = if p a then a :: filter l else filter l :=
  rfl

  theorem filter_cons_of_pos {a : A} (l : list A) (h : p a) : filter (a :: l) = a :: filter l :=
  (if_pos h : (if p a then a :: filter l else filter l) = a :: filter l) ▸ filter_cons a l

  theorem filter_cons_of_neg {a : A} (l : list A) (h : ¬ p a) : filter (a :: l) = filter l :=
  (if_neg h : (if p a then a :: filter l else filter l) = filter l) ▸ filter_cons a l
end

#check @_root_.filter
#check @_root_.filter_cons_of_pos
#check @_root_.filter_cons_of_neg
