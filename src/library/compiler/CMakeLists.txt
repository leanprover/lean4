add_library(compiler OBJECT emit_bytecode.cpp init_module.cpp ## New
  compiler util.cpp lcnf.cpp csimp.cpp elim_dead_let.cpp cse.cpp
  erase_irrelevant.cpp specialize.cpp compiler.cpp lambda_lifting.cpp
  extract_closed.cpp simp_app_args.cpp llnf.cpp ll_infer_type.cpp
  reduce_arity.cpp closed_term_cache.cpp name_mangling.cpp
  emit_cpp.cpp export_attribute.cpp llnf_code.cpp extern_attribute.cpp
  borrowed_annotation.cpp init_attribute.cpp eager_lambda_lifting.cpp
  struct_cases_on.cpp find_jp.cpp ir.cpp)
