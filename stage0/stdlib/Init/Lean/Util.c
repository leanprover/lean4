// Lean compiler output
// Module: Init.Lean.Util
// Imports: Init.Lean.Util.CollectFVars Init.Lean.Util.CollectLevelParams Init.Lean.Util.CollectMVars Init.Lean.Util.FindMVar Init.Lean.Util.MonadCache Init.Lean.Util.PPExt Init.Lean.Util.PPGoal Init.Lean.Util.Path Init.Lean.Util.Profile Init.Lean.Util.RecDepth Init.Lean.Util.Sorry Init.Lean.Util.Trace Init.Lean.Util.WHNF Init.Lean.Util.FindExpr Init.Lean.Util.ReplaceExpr Init.Lean.Util.FoldConsts
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
lean_object* initialize_Init_Lean_Util_CollectFVars(lean_object*);
lean_object* initialize_Init_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Init_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Init_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Init_Lean_Util_MonadCache(lean_object*);
lean_object* initialize_Init_Lean_Util_PPExt(lean_object*);
lean_object* initialize_Init_Lean_Util_PPGoal(lean_object*);
lean_object* initialize_Init_Lean_Util_Path(lean_object*);
lean_object* initialize_Init_Lean_Util_Profile(lean_object*);
lean_object* initialize_Init_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Init_Lean_Util_Sorry(lean_object*);
lean_object* initialize_Init_Lean_Util_Trace(lean_object*);
lean_object* initialize_Init_Lean_Util_WHNF(lean_object*);
lean_object* initialize_Init_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Init_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Init_Lean_Util_FoldConsts(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_MonadCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_PPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_Path(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_Profile(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_WHNF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
