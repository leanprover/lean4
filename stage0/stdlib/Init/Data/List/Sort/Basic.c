// Lean compiler output
// Module: Init.Data.List.Sort.Basic
// Imports: Init.Data.List.Impl
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
LEAN_EXPORT lean_object* l_List_splitInTwo(lean_object*);
LEAN_EXPORT lean_object* l_List_mergeSort___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_merge(lean_object*);
LEAN_EXPORT lean_object* l_List_splitInTwo___rarg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_List_splitAt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_merge___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_enumLE(lean_object*);
LEAN_EXPORT lean_object* l_List_splitInTwo___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_enumLE___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_enumLE___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mergeSort(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_6);
x_10 = lean_apply_2(x_1, x_6, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_6);
x_12 = l_List_merge___rarg(x_1, x_3, x_9);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_13; 
x_13 = l_List_merge___rarg(x_1, x_7, x_3);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_16);
lean_inc(x_14);
x_18 = lean_apply_2(x_1, x_14, x_16);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_15);
x_21 = l_List_merge___rarg(x_1, x_20, x_17);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
x_23 = l_List_merge___rarg(x_1, x_15, x_22);
lean_ctor_set(x_2, 1, x_23);
return x_2;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_28 = x_3;
} else {
 lean_dec_ref(x_3);
 x_28 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_26);
lean_inc(x_24);
x_29 = lean_apply_2(x_1, x_24, x_26);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
x_32 = l_List_merge___rarg(x_1, x_31, x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
x_35 = l_List_merge___rarg(x_1, x_25, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_merge___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_1, lean_box(0));
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_4(x_5, x_8, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Sort_Basic_0__List_merge_match__1_splitter___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_splitInTwo___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_List_splitAt___rarg(x_6, x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_splitInTwo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_splitInTwo___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_splitInTwo___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_splitInTwo___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mergeSort___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_List_lengthTRAux___rarg(x_2, x_14);
x_16 = l_List_splitInTwo___rarg(x_15, x_2);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l_List_mergeSort___rarg(x_1, x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_1);
x_20 = l_List_mergeSort___rarg(x_1, x_19);
x_21 = l_List_merge___rarg(x_1, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_2, 1, x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_List_lengthTRAux___rarg(x_2, x_25);
x_27 = l_List_splitInTwo___rarg(x_26, x_2);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_inc(x_1);
x_29 = l_List_mergeSort___rarg(x_1, x_28);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_1);
x_31 = l_List_mergeSort___rarg(x_1, x_30);
x_32 = l_List_merge___rarg(x_1, x_29, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_36 = x_4;
} else {
 lean_dec_ref(x_4);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_List_lengthTRAux___rarg(x_38, x_39);
x_41 = l_List_splitInTwo___rarg(x_40, x_38);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_inc(x_1);
x_43 = l_List_mergeSort___rarg(x_1, x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_1);
x_45 = l_List_mergeSort___rarg(x_1, x_44);
x_46 = l_List_merge___rarg(x_1, x_43, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mergeSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mergeSort___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_enumLE___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_apply_2(x_1, x_4, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_apply_2(x_1, x_5, x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_enumLE(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_enumLE___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_enumLE___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_enumLE___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
