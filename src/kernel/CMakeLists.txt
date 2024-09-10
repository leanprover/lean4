add_library(kernel OBJECT level.cpp expr.cpp expr_eq_fn.cpp
for_each_fn.cpp replace_fn.cpp abstract.cpp instantiate.cpp
local_ctx.cpp declaration.cpp environment.cpp type_checker.cpp
init_module.cpp expr_cache.cpp equiv_manager.cpp quot.cpp
inductive.cpp trace.cpp instantiate_mvars.cpp)
