// Lean compiler output
// Module: Std.Internal.Sat.AIG
// Imports: public import Std.Internal.Sat.AIG.Basic public import Std.Internal.Sat.AIG.LawfulOperator public import Std.Internal.Sat.AIG.Lemmas public import Std.Internal.Sat.AIG.Cached public import Std.Internal.Sat.AIG.CachedLemmas public import Std.Internal.Sat.AIG.CachedGates public import Std.Internal.Sat.AIG.CachedGatesLemmas public import Std.Internal.Sat.AIG.CNF public import Std.Internal.Sat.AIG.Relabel public import Std.Internal.Sat.AIG.RelabelNat public import Std.Internal.Sat.AIG.RefVec public import Std.Internal.Sat.AIG.RefVecOperator public import Std.Internal.Sat.AIG.LawfulVecOperator public import Std.Internal.Sat.AIG.If
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
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_LawfulOperator(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Cached(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_CachedLemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_CachedGates(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_CachedGatesLemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_CNF(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_RelabelNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_RefVec(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_RefVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Sat_AIG_If(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Sat_AIG(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_LawfulOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_CachedGates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_CachedGatesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_RelabelNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Sat_AIG(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Sat_AIG_Basic(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_LawfulOperator(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_Cached(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_CachedLemmas(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_CachedGates(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_CachedGatesLemmas(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_CNF(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_Relabel(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_RelabelNat(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_RefVec(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_RefVecOperator(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Std_Internal_Sat_AIG_If(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Sat_AIG(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_LawfulOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_Cached(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_CachedGates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_CachedGatesLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_RelabelNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_RefVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_RefVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_LawfulVecOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Sat_AIG_If(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Sat_AIG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Sat_AIG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Sat_AIG(builtin);
}
#ifdef __cplusplus
}
#endif
