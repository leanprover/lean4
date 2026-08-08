module

namespace List

def reverseRec {motive : List α → Sort _} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : ∀ l, motive l
  | [] => nil
  | a :: l => (dropLast_concat_getLast (cons_ne_nil a l)) ▸
    append_singleton _ _ ((a :: l).dropLast.reverseRec nil append_singleton)
  termination_by l => l.length

set_option grind.debug true in
theorem reverseRec_concat {motive : List α → Sort _} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    (xs ++ [x]).reverseRec nil append_singleton =
    append_singleton xs x (xs.reverseRec nil append_singleton) := by
  grind [reverseRec, cases List]
