local env = environment()
local l = mk_param_univ("l")
check_error(function() env = add_decl(env, mk_constant_assumption("A", {l, l}, mk_sort(l))) end)
