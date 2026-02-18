// Lean compiler output
// Module: Init.Data.List.ToArray
// Imports: import all Init.Data.List.Control public import Init.Data.List.Monadic import all Init.Data.Array.Basic import all Init.Data.Array.Set import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Bool import Init.Data.List.Erase import Init.Data.List.Find import Init.Data.List.Nat.Erase import Init.Data.List.Nat.InsertIdx import Init.Data.List.Nat.TakeDrop import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.List.Zip import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas import Init.Omega import Init.TacticsExtra
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_eraseP__eq__eraseIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_eraseP__eq__eraseIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_1(x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_apply_2(x_5, x_3, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__4_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_1(x_2, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_3, x_8, lean_box(0));
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findM_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_findM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__Array_findM_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_eraseP__eq__eraseIdx_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_ToArray_0__List_eraseP__eq__eraseIdx_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Data_List_ToArray_0__List_eraseP__eq__eraseIdx_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_List_Control(uint8_t builtin);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
