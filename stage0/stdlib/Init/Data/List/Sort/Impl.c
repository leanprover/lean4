// Lean compiler output
// Module: Init.Data.List.Sort.Impl
// Imports: Init.Data.List.Sort.Lemmas
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
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt_go___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run(lean_object*);
lean_object* l_List_reverseAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt(lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object*);
lean_object* l_List_splitInTwo___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt_go(lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR_go(lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverseAux___rarg(x_4, x_3);
return x_5;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_List_reverseAux___rarg(x_4, x_2);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_9);
x_13 = lean_apply_2(x_1, x_9, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_ctor_set(x_3, 1, x_10);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_11);
{
lean_object* _tmp_1 = x_3;
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_10;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_19);
lean_inc(x_17);
x_21 = lean_apply_2(x_1, x_17, x_19);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_2, 1, x_4);
lean_ctor_set(x_2, 0, x_19);
{
lean_object* _tmp_1 = x_23;
lean_object* _tmp_2 = x_20;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_2, 1, x_4);
{
lean_object* _tmp_1 = x_18;
lean_object* _tmp_2 = x_25;
lean_object* _tmp_3 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_31 = x_3;
} else {
 lean_dec_ref(x_3);
 x_31 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_29);
lean_inc(x_27);
x_32 = lean_apply_2(x_1, x_27, x_29);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_4);
x_2 = x_34;
x_3 = x_30;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; 
if (lean_is_scalar(x_31)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_31;
}
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_4);
x_2 = x_28;
x_3 = x_37;
x_4 = x_38;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeTR_go___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_List_MergeSort_Internal_mergeTR_go___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeTR___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_4, x_2, x_3);
return x_7;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_apply_3(x_5, x_1, x_3, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_5(x_6, x_9, x_10, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_3);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_3);
x_1 = x_6;
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_1);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_splitRevAt_go___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_MergeSort_Internal_splitRevAt_go___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_splitRevAt___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_4(x_5, x_1, x_2, x_3, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = lean_apply_4(x_4, x_7, x_8, x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_4(x_5, x_1, x_9, x_3, lean_box(0));
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_splitInTwo___rarg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_div(x_15, x_10);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_List_MergeSort_Internal_mergeSortTR_run___rarg(x_1, x_16, x_13);
lean_dec(x_16);
x_18 = lean_nat_div(x_11, x_10);
lean_dec(x_11);
lean_inc(x_1);
x_19 = l_List_MergeSort_Internal_mergeSortTR_run___rarg(x_1, x_18, x_14);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___rarg(x_1, x_17, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_3, 1, x_23);
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeSortTR_run___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_run___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_mergeSortTR_run___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
x_5 = l_List_MergeSort_Internal_mergeSortTR_run___rarg(x_1, x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeSortTR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_List_MergeSort_Internal_splitRevAt___rarg(x_6, x_2);
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
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_splitRevInTwo___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_MergeSort_Internal_splitRevInTwo___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_div(x_1, x_3);
x_5 = l_List_MergeSort_Internal_splitRevAt___rarg(x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_splitRevInTwo_x27___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_splitRevInTwo_x27___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_MergeSort_Internal_splitRevInTwo_x27___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_MergeSort_Internal_splitRevInTwo___rarg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_div(x_15, x_10);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg(x_1, x_16, x_13);
lean_dec(x_16);
x_18 = lean_nat_div(x_11, x_10);
lean_dec(x_11);
lean_inc(x_1);
x_19 = l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(x_1, x_18, x_14);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___rarg(x_1, x_17, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_3, 1, x_23);
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_List_MergeSort_Internal_splitRevInTwo_x27___rarg(x_11, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_nat_div(x_15, x_10);
lean_dec(x_15);
lean_inc(x_1);
x_17 = l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg(x_1, x_16, x_14);
lean_dec(x_16);
x_18 = lean_nat_div(x_11, x_10);
lean_dec(x_11);
lean_inc(x_1);
x_19 = l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(x_1, x_18, x_13);
lean_dec(x_18);
x_20 = l_List_MergeSort_Internal_mergeTR___rarg(x_1, x_17, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_3, 1, x_23);
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_MergeSort_Internal_mergeSortTR_u2082_run_x27___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
x_5 = l_List_MergeSort_Internal_mergeSortTR_u2082_run___rarg(x_1, x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_MergeSort_Internal_mergeSortTR_u2082(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_MergeSort_Internal_mergeSortTR_u2082___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_nat_sub(x_9, x_8);
lean_dec(x_9);
x_12 = lean_apply_2(x_5, x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_4, x_13, lean_box(0));
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_apply_1(x_3, lean_box(0));
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__2_splitter___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_Data_List_Sort_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Sort_Impl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Sort_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
