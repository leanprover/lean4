add_library(equations_compiler OBJECT equations.cpp util.cpp
  pack_domain.cpp structural_rec.cpp unbounded_rec.cpp elim_match.cpp
  compiler.cpp wf_rec.cpp partial_rec.cpp pack_mutual.cpp
  init_module.cpp)
