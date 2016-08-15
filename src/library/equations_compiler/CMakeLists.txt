add_library(equations_compiler OBJECT
  equations.cpp util.cpp compiler.cpp init_module.cpp
#LEGACY
  old_compiler.cpp old_goal.cpp old_inversion.cpp)
