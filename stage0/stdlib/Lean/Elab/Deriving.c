// Lean compiler output
// Module: Lean.Elab.Deriving
// Imports: public import Lean.Elab.Deriving.Basic public import Lean.Elab.Deriving.Util public import Lean.Elab.Deriving.Inhabited public import Lean.Elab.Deriving.Nonempty public import Lean.Elab.Deriving.TypeName public import Lean.Elab.Deriving.BEq public import Lean.Elab.Deriving.DecEq public import Lean.Elab.Deriving.Repr public import Lean.Elab.Deriving.FromToJson public import Lean.Elab.Deriving.SizeOf public import Lean.Elab.Deriving.Hashable public import Lean.Elab.Deriving.Ord public import Lean.Elab.Deriving.ToExpr public import Lean.Elab.Deriving.ReflBEq public import Lean.Elab.Deriving.LawfulBEq
#include <lean/lean.h>
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
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Inhabited(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Nonempty(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_TypeName(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_BEq(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_DecEq(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_FromToJson(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_SizeOf(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Hashable(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Ord(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_ReflBEq(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_LawfulBEq(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Inhabited(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Nonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_TypeName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_DecEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_FromToJson(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_SizeOf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_ReflBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_LawfulBEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
