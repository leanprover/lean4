// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Clz
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Const import Init.Data.BitVec.Lemmas import Init.Data.Int.Pow import Init.Omega
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
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Const(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Operations_Clz(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
