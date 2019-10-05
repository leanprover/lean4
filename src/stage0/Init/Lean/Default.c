// Lean compiler output
// Module: Init.Lean.Default
// Imports: Init.Lean.Path Init.Lean.Compiler.Default Init.Lean.Environment Init.Lean.Modifiers Init.Lean.ProjFns Init.Lean.Runtime Init.Lean.Attributes Init.Lean.Parser.Default Init.Lean.ReducibilityAttrs Init.Lean.Elaborator.Default Init.Lean.EqnCompiler.Default Init.Lean.Class Init.Lean.LocalContext Init.Lean.MetavarContext Init.Lean.TypeClass.Default
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
lean_object* initialize_Init_Lean_Path(lean_object*);
lean_object* initialize_Init_Lean_Compiler_Default(lean_object*);
lean_object* initialize_Init_Lean_Environment(lean_object*);
lean_object* initialize_Init_Lean_Modifiers(lean_object*);
lean_object* initialize_Init_Lean_ProjFns(lean_object*);
lean_object* initialize_Init_Lean_Runtime(lean_object*);
lean_object* initialize_Init_Lean_Attributes(lean_object*);
lean_object* initialize_Init_Lean_Parser_Default(lean_object*);
lean_object* initialize_Init_Lean_ReducibilityAttrs(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Default(lean_object*);
lean_object* initialize_Init_Lean_EqnCompiler_Default(lean_object*);
lean_object* initialize_Init_Lean_Class(lean_object*);
lean_object* initialize_Init_Lean_LocalContext(lean_object*);
lean_object* initialize_Init_Lean_MetavarContext(lean_object*);
lean_object* initialize_Init_Lean_TypeClass_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Path(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Environment(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Modifiers(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_ProjFns(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Runtime(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Attributes(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Parser_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_ReducibilityAttrs(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_EqnCompiler_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Class(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_LocalContext(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_MetavarContext(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_TypeClass_Default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
