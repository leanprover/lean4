add_library(compiler OBJECT util.cpp eta_expansion.cpp preprocess.cpp
  compiler_step_visitor.cpp elim_recursors.cpp comp_irrelevant.cpp
  inliner.cpp rec_fn_macro.cpp erase_irrelevant.cpp reduce_arity.cpp
  lambda_lifting.cpp simp_inductive.cpp nat_value.cpp
  vm_compiler.cpp cse.cpp elim_unused_lets.cpp extract_values.cpp init_module.cpp)
