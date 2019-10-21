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
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_InlineAttrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_Specialize(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ConstFolding(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ClosedTermCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ImplementedByAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_NeverExtractAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
