#include <lean/lean.h>

extern "C" void leanrt_cpp_partial_hidden_lean_initialize_thread() {}
extern "C" void leanrt_cpp_partial_hidden_lean_finalize_thread() {}
extern "C" void leanrt_cpp_partial_hidden_lean_initialize_runtime_module() {}
extern "C" void leanrt_cpp_partial_hidden_lean_io_mark_end_initialization() {}
extern "C" char ** leanrt_cpp_partial_hidden_lean_setup_args(int, char ** argv) { return argv; }
extern "C" void leanrt_cpp_partial_hidden_lean_free_object_impl(lean_object *) {}
