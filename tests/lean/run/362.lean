variables {a : Type}

definition foo (A : Type) : A → A :=
begin
  intro a, assumption
end

(*
local d = get_env():find("foo")
assert(#d:univ_params() == 1)
*)

set_option pp.universes true
check foo
