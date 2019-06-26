// Lean compiler output
// Module: init.lean.compiler.default
// Imports: init.lean.compiler.inlineattrs init.lean.compiler.specializeattrs init.lean.compiler.constfolding init.lean.compiler.closedtermcache init.lean.compiler.externattr init.lean.compiler.implementedbyattr init.lean.compiler.ir.default
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
obj* initialize_init_lean_compiler_inlineattrs(obj*);
obj* initialize_init_lean_compiler_specializeattrs(obj*);
obj* initialize_init_lean_compiler_constfolding(obj*);
obj* initialize_init_lean_compiler_closedtermcache(obj*);
obj* initialize_init_lean_compiler_externattr(obj*);
obj* initialize_init_lean_compiler_implementedbyattr(obj*);
obj* initialize_init_lean_compiler_ir_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_inlineattrs(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_specializeattrs(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_constfolding(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_closedtermcache(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_externattr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_implementedbyattr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_default(w);
if (io_result_is_error(w)) return w;
return w;
}
