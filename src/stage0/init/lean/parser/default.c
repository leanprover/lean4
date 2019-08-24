// Lean compiler output
// Module: init.lean.parser.default
// Imports: init.lean.parser.parser init.lean.parser.level init.lean.parser.term init.lean.parser.command init.lean.parser.module
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
lean_object* initialize_init_lean_parser_parser(lean_object*);
lean_object* initialize_init_lean_parser_level(lean_object*);
lean_object* initialize_init_lean_parser_term(lean_object*);
lean_object* initialize_init_lean_parser_command(lean_object*);
lean_object* initialize_init_lean_parser_module(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_parser_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_level(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_term(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_command(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
