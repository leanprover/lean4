add_library(equations_compiler OBJECT
  equations.cpp init_module.cpp
#LEGACY
  old_compiler.cpp old_goal.cpp old_inversion.cpp)
