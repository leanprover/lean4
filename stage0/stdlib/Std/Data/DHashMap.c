// Lean compiler output
// Module: Std.Data.DHashMap
// Imports: public import Std.Data.DHashMap.Basic public import Std.Data.DHashMap.AdditionalOperations public import Std.Data.DHashMap.Iterator public import Std.Data.DHashMap.Lemmas public import Std.Data.DHashMap.IteratorLemmas public import Std.Data.DHashMap.DecidableEquiv
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
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_IteratorLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_DecidableEquiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_IteratorLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
