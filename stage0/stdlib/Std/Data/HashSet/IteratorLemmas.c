// Lean compiler output
// Module: Std.Data.HashSet.IteratorLemmas
// Imports: import Std.Data.DHashMap.IteratorLemmas import all Std.Data.HashMap.IteratorLemmas public import Std.Data.HashSet.Iterator import all Std.Data.HashSet.Iterator import Std.Data.HashSet.RawLemmas import all Std.Data.DHashMap.Basic
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
lean_object* initialize_Std_Data_DHashMap_IteratorLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_IteratorLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_RawLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_IteratorLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_IteratorLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_IteratorLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
