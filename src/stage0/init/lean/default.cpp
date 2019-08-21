// Lean compiler output
// Module: init.lean.default
// Imports: init.lean.path init.lean.compiler.default init.lean.environment init.lean.modifiers init.lean.projfns init.lean.runtime init.lean.attributes init.lean.parser.default init.lean.reducibilityattrs init.lean.elaborator.default init.lean.eqncompiler.default init.lean.class init.lean.localcontext init.lean.metavarcontext
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
obj* initialize_init_lean_path(obj*);
obj* initialize_init_lean_compiler_default(obj*);
obj* initialize_init_lean_environment(obj*);
obj* initialize_init_lean_modifiers(obj*);
obj* initialize_init_lean_projfns(obj*);
obj* initialize_init_lean_runtime(obj*);
obj* initialize_init_lean_attributes(obj*);
obj* initialize_init_lean_parser_default(obj*);
obj* initialize_init_lean_reducibilityattrs(obj*);
obj* initialize_init_lean_elaborator_default(obj*);
obj* initialize_init_lean_eqncompiler_default(obj*);
obj* initialize_init_lean_class(obj*);
obj* initialize_init_lean_localcontext(obj*);
obj* initialize_init_lean_metavarcontext(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_path(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_environment(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_modifiers(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_projfns(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_attributes(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_reducibilityattrs(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_elaborator_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_eqncompiler_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_class(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_localcontext(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_metavarcontext(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
