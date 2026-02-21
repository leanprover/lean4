// Lean compiler output
// Module: Std.Sat.CNF.RelabelFin
// Imports: public import Init.Data.Nat.Order public import Std.Sat.CNF.Relabel import Init.Data.Option.Lemmas import Init.Omega import Init.Data.List.Impl import Init.Data.List.MinMax public import Init.Data.Array.MinMax import Init.TacticsExtra
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
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_foldl___at___00List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1_spec__1(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(x_1, x_2);
x_4 = l_List_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__1(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_11);
x_12 = l_Std_Sat_CNF_Clause_maxLiteral(x_11);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_array_push(x_4, x_13);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_obj_once(&l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0, &l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_once, _init_l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0);
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_2, x_6);
if (x_8 == 0)
{
return x_4;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(x_1, x_9, x_10, x_4);
return x_11;
}
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_2);
x_13 = lean_usize_of_nat(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(x_1, x_12, x_13, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_uget_borrowed(x_1, x_2);
x_12 = lean_nat_dec_le(x_4, x_11);
if (x_12 == 0)
{
x_5 = x_4;
goto block_9;
}
else
{
lean_dec(x_4);
lean_inc(x_11);
x_5 = x_11;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_fget_borrowed(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
if (x_6 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_of_nat(x_5);
lean_inc(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(x_1, x_8, x_9, x_3);
return x_10;
}
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_of_nat(x_5);
lean_inc(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2_spec__3(x_1, x_11, x_12, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___redArg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(x_1, x_2, x_3);
x_5 = l_Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_maxLiteral(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_maxLiteral_spec__1_spec__2(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_maxLiteral(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_numLiterals(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_CNF_relabelFin___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc_ref(x_1);
x_2 = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_get_size(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(0);
x_5 = lean_mk_array(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Std_Sat_CNF_numLiterals(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = l_Std_Sat_CNF_relabel___redArg(x_7, x_1);
return x_8;
}
}
}
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MinMax(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MinMax(builtin);
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
