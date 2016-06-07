add_library(vm OBJECT vm.cpp optimize.cpp vm_nat.cpp vm_string.cpp vm_aux.cpp vm_io.cpp vm_name.cpp
  vm_options.cpp vm_format.cpp vm_rb_map.cpp vm_level.cpp vm_expr.cpp vm_exceptional.cpp
  init_module.cpp)