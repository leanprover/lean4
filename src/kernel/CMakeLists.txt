add_library(kernel OBJECT level.cpp expr.cpp expr_eq_fn.cpp for_each_fn.cpp
replace_fn.cpp free_vars.cpp abstract.cpp instantiate.cpp
formatter.cpp declaration.cpp environment.cpp pos_info_provider.cpp
type_checker.cpp error_msgs.cpp kernel_exception.cpp
normalizer_extension.cpp init_module.cpp expr_cache.cpp scope_pos_info_provider.cpp
equiv_manager.cpp quot.cpp abstract_type_context.cpp standard_kernel.cpp)
