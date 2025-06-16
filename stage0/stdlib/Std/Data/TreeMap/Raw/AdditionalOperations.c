// Lean compiler output
// Module: Std.Data.TreeMap.Raw.AdditionalOperations
// Imports: Std.Data.TreeMap.Basic Std.Data.TreeMap.Raw.Basic Std.Data.DTreeMap.Raw.AdditionalOperations
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_link2_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_8 = lean_apply_2(x_2, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_2);
x_9 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_6);
x_10 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_7);
x_11 = l_Std_DTreeMap_Internal_Impl_link2_x21___rarg(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_2);
x_13 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_6);
x_14 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_7);
x_15 = l_Std_DTreeMap_Internal_Impl_link_x21___rarg(x_4, x_12, x_13, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_filterMap___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_filterMap_x21___at_Std_TreeMap_Raw_filterMap___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_filterMap___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_TreeMap_Raw_filterMap___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 3);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_2);
lean_inc(x_5);
x_9 = lean_apply_2(x_2, x_5, x_6);
lean_inc(x_2);
x_10 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_7);
x_11 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_8);
lean_ctor_set(x_3, 4, x_11);
lean_ctor_set(x_3, 3, x_10);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_17 = lean_apply_2(x_2, x_13, x_14);
lean_inc(x_2);
x_18 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_15);
x_19 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_16);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_box(1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_TreeMap_Raw_map___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_map___at_Std_TreeMap_Raw_map___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_TreeMap_Raw_map___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_TreeMap_Raw_map___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_TreeMap_Raw_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeMap_Raw_AdditionalOperations(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
