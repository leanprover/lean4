add_library(vm OBJECT vm.cpp optimize.cpp vm_nat.cpp vm_string.cpp vm_aux.cpp vm_io.cpp vm_name.cpp
  vm_options.cpp vm_format.cpp vm_rb_map.cpp vm_level.cpp vm_expr.cpp vm_exceptional.cpp
  vm_declaration.cpp vm_environment.cpp vm_list.cpp vm_pexpr.cpp vm_task.cpp
  vm_int.cpp init_module.cpp vm_parser.cpp vm_array.cpp vm_pos_info.cpp)
