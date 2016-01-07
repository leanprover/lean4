import data.unit
open nat unit

set_option blast.strategy "cc"

constant r {A B : Type} : A → B → A

definition ex1 (a b c d : unit) : r a b = r c d :=
by blast

-- The congruence closure module does not automatically merge subsingleton equivalence classes.
--
-- example (a b : unit) : a = b :=
-- by blast
