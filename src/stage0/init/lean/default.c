// Lean compiler output
// Module: init.lean.default
// Imports: init.lean.path init.lean.compiler.default init.lean.environment init.lean.modifiers init.lean.projfns init.lean.runtime init.lean.attributes init.lean.parser.default init.lean.reducibilityattrs init.lean.elaborator.default init.lean.eqncompiler.default init.lean.class init.lean.localcontext init.lean.metavarcontext init.lean.typeclass.default
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
lean_object* initialize_init_lean_path(lean_object*);
lean_object* initialize_init_lean_compiler_default(lean_object*);
lean_object* initialize_init_lean_environment(lean_object*);
lean_object* initialize_init_lean_modifiers(lean_object*);
lean_object* initialize_init_lean_projfns(lean_object*);
lean_object* initialize_init_lean_runtime(lean_object*);
lean_object* initialize_init_lean_attributes(lean_object*);
lean_object* initialize_init_lean_parser_default(lean_object*);
lean_object* initialize_init_lean_reducibilityattrs(lean_object*);
lean_object* initialize_init_lean_elaborator_default(lean_object*);
lean_object* initialize_init_lean_eqncompiler_default(lean_object*);
lean_object* initialize_init_lean_class(lean_object*);
lean_object* initialize_init_lean_localcontext(lean_object*);
lean_object* initialize_init_lean_metavarcontext(lean_object*);
lean_object* initialize_init_lean_typeclass_default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_path(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_modifiers(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_projfns(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_reducibilityattrs(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_eqncompiler_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_class(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_metavarcontext(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_typeclass_default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
