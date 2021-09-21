// Lean compiler output
// Module: Lean.Util
// Imports: Init Lean.Util.CollectFVars Lean.Util.CollectLevelParams Lean.Util.CollectMVars Lean.Util.FindMVar Lean.Util.FindLevelMVar Lean.Util.MonadCache Lean.Util.PPExt Lean.Util.Path Lean.Util.Profile Lean.Util.RecDepth Lean.Util.Sorry Lean.Util.Trace Lean.Util.FindExpr Lean.Util.ReplaceExpr Lean.Util.ForEachExpr Lean.Util.ReplaceLevel Lean.Util.FoldConsts Lean.Util.SCC Lean.Util.OccursCheck
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Util_FindLevelMVar(lean_object*);
lean_object* initialize_Lean_Util_MonadCache(lean_object*);
lean_object* initialize_Lean_Util_PPExt(lean_object*);
lean_object* initialize_Lean_Util_Path(lean_object*);
lean_object* initialize_Lean_Util_Profile(lean_object*);
lean_object* initialize_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Lean_Util_Sorry(lean_object*);
lean_object* initialize_Lean_Util_Trace(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Util_SCC(lean_object*);
lean_object* initialize_Lean_Util_OccursCheck(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindLevelMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profile(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SCC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_OccursCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
