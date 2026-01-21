// Lean compiler output
// Module: Lean.Data.NameMap.AdditionalOperations
// Imports: public import Lean.Data.NameMap.Basic public import Std.Data.TreeSet.AdditionalOperations
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
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_inc_ref(x_1);
x_8 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_1, x_5);
x_9 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_1, x_6);
x_10 = l_Std_DTreeMap_Internal_Impl_link2___redArg(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec_ref(x_7);
lean_inc_ref(x_1);
x_12 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_1, x_5);
x_13 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_1, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_link___redArg(x_3, x_11, x_12, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = lean_box(1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_NameMap_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_filterMap___at___00Lean_NameMap_filterMap_spec__0___redArg(x_3, x_4);
return x_6;
}
}
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_AdditionalOperations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_NameMap_AdditionalOperations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
