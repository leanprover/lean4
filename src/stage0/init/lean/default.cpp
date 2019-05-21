// Lean compiler output
// Module: init.lean.default
// Imports: init.lean.compiler.default init.lean.frontend init.lean.extern init.lean.environment init.lean.modifiers init.lean.runtime
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* initialize_init_lean_compiler_default(obj*);
obj* initialize_init_lean_frontend(obj*);
obj* initialize_init_lean_extern(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_modifiers(obj*);
obj* initialize_init_lean_runtime(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_frontend(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_extern(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_modifiers(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (io_result_is_error(w)) return w;
return w;
}
