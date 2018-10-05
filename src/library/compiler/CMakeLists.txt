add_library(compiler OBJECT old_util.cpp preprocess.cpp
  compiler_step_visitor.cpp
  lambda_lifting.cpp simp_inductive.cpp
  vm_compiler.cpp extract_values.cpp init_module.cpp
  ## New compiler
  util.cpp lcnf.cpp csimp.cpp elim_dead_let.cpp cse.cpp erase_irrelevant.cpp
  specialize.cpp compiler.cpp
  )
