// Lean compiler output
// Module: init.lean.elaborator.default
// Imports: init.lean.elaborator.basic init.lean.elaborator.elabstrategyattrs init.lean.elaborator.command init.lean.elaborator.preterm init.lean.elaborator.term
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
lean_object* initialize_init_lean_elaborator_basic(lean_object*);
lean_object* initialize_init_lean_elaborator_elabstrategyattrs(lean_object*);
lean_object* initialize_init_lean_elaborator_command(lean_object*);
lean_object* initialize_init_lean_elaborator_preterm(lean_object*);
lean_object* initialize_init_lean_elaborator_term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_elaborator_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_elabstrategyattrs(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_command(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_preterm(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_term(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
