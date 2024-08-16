// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations
// Imports: Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsb Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Replicate Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateLeft Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.RotateRight Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.SignExtend Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult Lean.Elab.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend
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
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsb(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_SignExtend(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsb(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Replicate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_RotateRight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_SignExtend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
