syntax "enum'" ident " where " ("|" ident)* : command
macro_rules
  | `(enum' $id where $[| $ids ]*) =>`(inductive $id where $[| $ids:ident ]*)
