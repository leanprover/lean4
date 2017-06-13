inductive statement : Type
| Sswitch   : list (option ℤ × statement) → statement
open statement

mutual def find_label, find_label_ls
with find_label : statement → nat → option (statement × nat)
| (Sswitch sl)  := λ k, find_label_ls sl k
with find_label_ls : list (option ℤ × statement) → nat → option (statement × nat)
| []       := λk, none
| ((_, s) :: sl') := λk, find_label s k <|> find_label_ls sl' k

example : find_label_ls [] = λ k, none :=
by simp [find_label_ls]

example (n s sl) : find_label_ls ((n, s)::sl) = λ k, find_label s k <|> find_label_ls sl k :=
by simp [find_label_ls]
