definition id1 {A : Type} (a : A) : A := a
definition id2 (A : Type) (a : A) : A := a

(*
 local t1 = get_env():find("id1"):type()
 local t2 = get_env():find("id2"):type()
 assert(t1:hash() == t2:hash())
 assert(t1:hash_bi() ~= t2:hash_bi())
*)
