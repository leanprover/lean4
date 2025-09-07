// Lean compiler output
// Module: Std.Data.DHashMap.AdditionalOperations
// Imports: Std.Data.DHashMap.Internal.Raw Std.Data.DHashMap.Internal.WF
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_filterMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_filterMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_DHashMap_map(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
lean_object* initialize_Std_Data_DHashMap_Internal_Raw(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DHashMap_Internal_WF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_AdditionalOperations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Internal_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_WF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
