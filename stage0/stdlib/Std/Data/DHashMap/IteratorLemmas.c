// Lean compiler output
// Module: Std.Data.DHashMap.IteratorLemmas
// Imports: public import Std.Data.Iterators public import Std.Data.DHashMap.Iterator import all Std.Data.DHashMap.Basic import all Std.Data.DHashMap.Raw import all Std.Data.DHashMap.Iterator import Init.Data.Iterators.Lemmas.Combinators import all Std.Data.DHashMap.Internal.Defs import Std.Data.DHashMap.RawLemmas import Std.Data.DHashMap.Lemmas
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
lean_object* initialize_Std_Data_Iterators(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_IteratorLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
