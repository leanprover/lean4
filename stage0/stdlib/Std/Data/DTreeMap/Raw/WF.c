// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.WF
// Imports: Std.Data.DTreeMap.Internal.Lemmas Std.Data.DTreeMap.Raw.AdditionalOperations Std.Data.DTreeMap.Raw.Basic
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_WF_0__Std_DTreeMap_Raw_WF_instCoeTypeForall(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Raw_WF_0__Std_DTreeMap_Raw_WF_instCoeTypeForall(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Raw_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Raw_WF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
