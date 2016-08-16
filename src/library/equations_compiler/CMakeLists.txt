add_library(equations_compiler OBJECT
  equations.cpp util.cpp pack_domain.cpp
  structural_rec.cpp unbounded_rec.cpp
  compiler.cpp init_module.cpp
#LEGACY
  old_compiler.cpp old_goal.cpp old_inversion.cpp)
