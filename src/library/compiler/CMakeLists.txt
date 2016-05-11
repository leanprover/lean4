add_library(compiler OBJECT util.cpp eta_expansion.cpp simp_pr1_rec.cpp preprocess_rec.cpp
  compiler_step_visitor.cpp elim_recursors.cpp comp_irrelevant.cpp
  inliner.cpp rec_fn_macro.cpp erase_irrelevant.cpp reduce_arity.cpp
  lambda_lifting.cpp init_module.cpp)
