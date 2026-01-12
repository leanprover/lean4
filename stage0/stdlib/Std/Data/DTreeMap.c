// Lean compiler output
// Module: Std.Data.DTreeMap
// Imports: public import Std.Data.DTreeMap.Basic public import Std.Data.DTreeMap.AdditionalOperations public import Std.Data.DTreeMap.Lemmas public import Std.Data.DTreeMap.Iterator public import Std.Data.DTreeMap.Slice public import Std.Data.DTreeMap.DecidableEquiv
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
lean_object* initialize_Std_Data_DTreeMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Iterator(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Slice(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_DecidableEquiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
