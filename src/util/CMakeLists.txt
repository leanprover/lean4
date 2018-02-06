add_library(util OBJECT debug.cpp name.cpp name_set.cpp fresh_name.cpp
  exception.cpp interrupt.cpp hash.cpp escaped.cpp bit_tricks.cpp
  safe_arith.cpp ascii.cpp memory.cpp shared_mutex.cpp path.cpp
  stackinfo.cpp lean_path.cpp serializer.cpp lbool.cpp
  bitap_fuzzy_search.cpp init_module.cpp thread.cpp memory_pool.cpp
  utf8.cpp name_map.cpp list_fn.cpp file_lock.cpp
  timeit.cpp timer.cpp task.cpp task_builder.cpp cancellable.cpp
  log_tree.cpp small_object_allocator.cpp subscripted_name_set.cpp
  parser_exception.cpp name_generator.cpp)
