add_library(library OBJECT expr_lt.cpp
  bin_app.cpp constants.cpp max_sharing.cpp
  module.cpp replace_visitor.cpp num.cpp
  class.cpp util.cpp print.cpp annotation.cpp
  reducible.cpp init_module.cpp
  projection.cpp
  aux_recursors.cpp
  profiling.cpp time_task.cpp
  formatter.cpp
  elab_environment.cpp)
