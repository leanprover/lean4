// Lean compiler output
// Module: Init.Lean.Compiler.Default
// Imports: Init.Lean.Compiler.InlineAttrs Init.Lean.Compiler.Specialize Init.Lean.Compiler.ConstFolding Init.Lean.Compiler.ClosedTermCache Init.Lean.Compiler.ExternAttr Init.Lean.Compiler.ImplementedByAttr Init.Lean.Compiler.NeverExtractAttr Init.Lean.Compiler.IR.Default
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
lean_object* initialize_Init_Lean_Compiler_InlineAttrs(lean_object*);
lean_object* initialize_Init_Lean_Compiler_Specialize(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ConstFolding(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ClosedTermCache(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExternAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ImplementedByAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_NeverExtractAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_InlineAttrs(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_Specialize(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_ConstFolding(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_ClosedTermCache(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_ExternAttr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_ImplementedByAttr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_NeverExtractAttr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
