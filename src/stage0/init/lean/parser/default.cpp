// Lean compiler output
// Module: init.lean.parser.default
// Imports: init.lean.parser.parser init.lean.parser.level init.lean.parser.term init.lean.parser.command init.lean.parser.module
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
extern "C" {
obj* initialize_init_lean_parser_parser(obj*);
obj* initialize_init_lean_parser_level(obj*);
obj* initialize_init_lean_parser_term(obj*);
obj* initialize_init_lean_parser_command(obj*);
obj* initialize_init_lean_parser_module(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_level(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_term(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_command(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
}
