prelude

constant vec.{l} : Type.{l} → Type.{l}
constant lst.{l} : Type.{l} → Type.{l}
constant vec.nil {A : Type} : vec A
constant lst.nil {A : Type} : lst A
constant vec.cons {A : Type} : A → vec A → vec A
constant lst.cons {A : Type} : A → lst A → lst A

notation `[` l:(foldr `, ` (h t, vec.cons h t) vec.nil `]`) := l
notation `[` l:(foldr `, ` (h t, lst.cons h t) lst.nil `]`) := l

constant A : Type.{1}
variables a b c : A

check [a, b, c]
check ([a, b, c] : vec A)
check ([a, b, c] : lst A)
set_option pp.all true
check ([a, b, c] : vec A)
check ([a, b, c] : lst A)
