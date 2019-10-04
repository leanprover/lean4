// Lean compiler output
// Module: Init.Lean.Parser.Default
// Imports: Init.Lean.Parser.Parser Init.Lean.Parser.Level Init.Lean.Parser.Term Init.Lean.Parser.Command Init.Lean.Parser.Module
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
lean_object* initialize_Init_Lean_Parser_Parser(lean_object*);
lean_object* initialize_Init_Lean_Parser_Level(lean_object*);
lean_object* initialize_Init_Lean_Parser_Term(lean_object*);
lean_object* initialize_Init_Lean_Parser_Command(lean_object*);
lean_object* initialize_Init_Lean_Parser_Module(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Parser(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Level(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Term(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Command(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Module(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
