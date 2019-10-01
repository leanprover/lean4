// Lean compiler output
// Module: init.lean.compiler.default
// Imports: init.lean.compiler.inlineattrs init.lean.compiler.specialize init.lean.compiler.constfolding init.lean.compiler.closedtermcache init.lean.compiler.externattr init.lean.compiler.implementedbyattr init.lean.compiler.neverextractattr init.lean.compiler.ir.default
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_init_lean_compiler_inlineattrs(lean_object*);
lean_object* initialize_init_lean_compiler_specialize(lean_object*);
lean_object* initialize_init_lean_compiler_constfolding(lean_object*);
lean_object* initialize_init_lean_compiler_closedtermcache(lean_object*);
lean_object* initialize_init_lean_compiler_externattr(lean_object*);
lean_object* initialize_init_lean_compiler_implementedbyattr(lean_object*);
lean_object* initialize_init_lean_compiler_neverextractattr(lean_object*);
lean_object* initialize_init_lean_compiler_ir_default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_inlineattrs(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_specialize(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_constfolding(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_closedtermcache(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_externattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_implementedbyattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_neverextractattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
