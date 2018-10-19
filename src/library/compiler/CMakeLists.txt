add_library(compiler OBJECT
  emit_bytecode.cpp simp_inductive.cpp init_module.cpp
  ## New compiler
  util.cpp lcnf.cpp csimp.cpp elim_dead_let.cpp cse.cpp erase_irrelevant.cpp
  specialize.cpp compiler.cpp lambda_lifting.cpp extract_closed.cpp
  )
