// Lean compiler output
// Module: Init.Data.Array.BasicAux
// Imports: Init.Data.Array.Basic Init.Data.Nat.Linear Init.NotationExtra
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
lean_dec(x_1);
x_9 = lean_array_push(x_2, x_6);
x_10 = l_Array_mapM_x27_go___rarg(x_3, x_4, x_5, x_8, x_9, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_11 = lean_apply_1(x_2, x_10);
x_12 = lean_alloc_closure((void*)(l_Array_mapM_x27_go___rarg___lambda__1), 6, 5);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapM_x27_go___rarg), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_mapM_x27_go___rarg(x_1, x_2, x_3, x_6, x_5, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapM_x27___rarg), 3, 0);
return x_4;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_BasicAux(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
