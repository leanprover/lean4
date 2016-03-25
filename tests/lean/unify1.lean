import data.list
open list

definition ID {A : Type} (a : A) := a

-- set_option trace.type_context.is_def_eq_detail true
-- set_option pp.purify_metavars false

#unify id (_ ++ (_ : list nat)), ([1, 2] ++ [(3:nat), 4])

#unify (_ ++ (_ : list nat)), id ([1, 2] ++ [(3:nat), 4])

#unify (_ ++ (_ : list nat)), ID ([1, 2] ++ [(3:nat), 4])

#unify (_ ++ (_ : list nat)), ID (ID ([1, 2] ++ [(3:nat), 4]))

#unify ID (_ ++ (_ : list nat)), ID ([1, 2] ++ [(3:nat), 4])

#unify ID (_ ++ (_ : list nat)), ([1, 2] ++ [(3:nat), 4])

-- The following one fails because both sides are productive, and
-- we need to unfolding steps in the lhs to get the same
-- head symbol in the rhs
-- #unify ID (ID (_ ++ (_ : list nat))), ([1, 2] ++ [(3:nat), 4])

#unify ([(1:nat)] ++ [2, 3, 4]), ([1, 2] ++ [(3:nat), 4])

constant y1 : nat
constant y2 : nat

#unify (y1 :: _) ++ _, (let l := [y1] in l ++ [y2])
