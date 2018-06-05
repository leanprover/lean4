add_library(util OBJECT object_ref.cpp name.cpp name_set.cpp fresh_name.cpp hash.cpp
  escaped.cpp bit_tricks.cpp safe_arith.cpp ascii.cpp shared_mutex.cpp
  path.cpp lean_path.cpp lbool.cpp bitap_fuzzy_search.cpp
  init_module.cpp name_map.cpp list_fn.cpp file_lock.cpp
  timeit.cpp timer.cpp task.cpp task_builder.cpp cancellable.cpp
  log_tree.cpp parser_exception.cpp
  name_generator.cpp)
