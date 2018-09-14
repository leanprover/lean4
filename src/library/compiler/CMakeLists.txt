add_library(compiler OBJECT util.cpp eta_expansion.cpp preprocess.cpp
  compiler_step_visitor.cpp elim_recursors.cpp comp_irrelevant.cpp
  inliner.cpp erase_irrelevant.cpp reduce_arity.cpp
  lambda_lifting.cpp simp_inductive.cpp nat_value.cpp
  vm_compiler.cpp old_cse.cpp elim_unused_lets.cpp extract_values.cpp init_module.cpp
  ## New compiler
  lc_util.cpp lcnf.cpp csimp.cpp elim_dead_let.cpp
  )
