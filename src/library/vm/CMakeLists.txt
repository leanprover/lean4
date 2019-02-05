add_library(vm OBJECT vm.cpp optimize.cpp vm_nat.cpp vm_string.cpp vm_aux.cpp vm_io.cpp
  vm_int.cpp vm_uint.cpp vm_thunk.cpp vm_name.cpp init_module.cpp)
