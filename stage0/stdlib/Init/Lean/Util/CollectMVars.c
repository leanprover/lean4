// Lean compiler output
// Module: Init.Lean.Util.CollectMVars
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_CollectMVars_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSetImp___rarg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_foldl___main___at_Lean_CollectMVars_visit___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_main___main(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_mkHashSet___at_Lean_CollectMVars_State_inhabited___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_List_elem___main___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__1;
lean_object* l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited;
lean_object* l_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectMVars_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectMVars_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectMVars_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CollectMVars_State_inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_CollectMVars_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectMVars_State_inhabited___closed__2;
return x_1;
}
}
uint8_t l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_expr_eqv(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_List_foldl___main___at_Lean_CollectMVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 1, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = l_Lean_Expr_hash(x_12);
x_16 = lean_usize_modn(x_15, x_14);
lean_dec(x_14);
x_17 = lean_array_uget(x_1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_1, x_16, x_18);
x_1 = x_19;
x_2 = x_13;
goto _start;
}
}
}
}
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_List_foldl___main___at_Lean_CollectMVars_visit___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashSetImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_expr_eqv(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_expr_eqv(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(x_10, x_2, x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
}
}
lean_object* l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_usize_modn(x_7, x_6);
x_9 = lean_array_uget(x_5, x_8);
x_10 = l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_uset(x_5, x_8, x_13);
x_15 = lean_nat_dec_le(x_12, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_1);
x_16 = l_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(x_12, x_14);
return x_16;
}
else
{
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_2);
x_17 = l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(x_9, x_2, x_2);
lean_dec(x_2);
x_18 = lean_array_uset(x_5, x_8, x_17);
lean_ctor_set(x_1, 1, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = l_Lean_Expr_hash(x_2);
x_23 = lean_usize_modn(x_22, x_21);
x_24 = lean_array_uget(x_20, x_23);
x_25 = l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_19, x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_uset(x_20, x_23, x_28);
x_30 = lean_nat_dec_le(x_27, x_21);
lean_dec(x_21);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_HashSetImp_expand___at_Lean_CollectMVars_visit___spec__4(x_27, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_inc(x_2);
x_33 = l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(x_24, x_2, x_2);
lean_dec(x_2);
x_34 = lean_array_uset(x_20, x_23, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_CollectMVars_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_5, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
lean_inc(x_2);
x_11 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_5, x_2);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_apply_2(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_2);
x_13 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_5, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_apply_2(x_1, x_2, x_14);
return x_15;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_CollectMVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_replace___main___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___main___at_Lean_CollectMVars_visit___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_CollectMVars_main___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_push(x_5, x_3);
lean_ctor_set(x_2, 1, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_array_push(x_8, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 5:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Expr_hasMVar(x_11);
x_14 = l_Lean_Expr_hasMVar(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_15, x_12);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
lean_inc(x_12);
x_21 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_15, x_12);
lean_ctor_set(x_2, 0, x_21);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
lean_inc(x_12);
x_23 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_15, x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
x_1 = x_12;
x_2 = x_24;
goto _start;
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
return x_2;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_26, x_11);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_2, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 0);
lean_dec(x_31);
lean_inc(x_11);
x_32 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_26, x_11);
lean_ctor_set(x_2, 0, x_32);
x_33 = l_Lean_CollectMVars_main___main(x_11, x_2);
if (x_14 == 0)
{
lean_dec(x_12);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_34, x_12);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
lean_inc(x_12);
x_40 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_34, x_12);
lean_ctor_set(x_33, 0, x_40);
x_1 = x_12;
x_2 = x_33;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_33);
lean_inc(x_12);
x_42 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_34, x_12);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
x_1 = x_12;
x_2 = x_43;
goto _start;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_12);
return x_33;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
lean_inc(x_11);
x_45 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_26, x_11);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_27);
x_47 = l_Lean_CollectMVars_main___main(x_11, x_46);
if (x_14 == 0)
{
lean_dec(x_12);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_48, x_12);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
lean_inc(x_12);
x_52 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_48, x_12);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_1 = x_12;
x_2 = x_53;
goto _start;
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_12);
return x_47;
}
}
}
}
else
{
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_55; 
x_55 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_26, x_12);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_2, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_2, 0);
lean_dec(x_58);
lean_inc(x_12);
x_59 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_26, x_12);
lean_ctor_set(x_2, 0, x_59);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
lean_inc(x_12);
x_61 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_26, x_12);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_27);
x_1 = x_12;
x_2 = x_62;
goto _start;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
return x_2;
}
}
}
}
}
case 6:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
lean_dec(x_1);
x_66 = l_Lean_Expr_hasMVar(x_64);
x_67 = l_Lean_Expr_hasMVar(x_65);
if (x_66 == 0)
{
lean_dec(x_64);
if (x_67 == 0)
{
lean_dec(x_65);
return x_2;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_68, x_65);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_2, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
lean_inc(x_65);
x_74 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_68, x_65);
lean_ctor_set(x_2, 0, x_74);
x_1 = x_65;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_2);
lean_inc(x_65);
x_76 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_68, x_65);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
x_1 = x_65;
x_2 = x_77;
goto _start;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
return x_2;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_79, x_64);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_2);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_2, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_2, 0);
lean_dec(x_84);
lean_inc(x_64);
x_85 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_79, x_64);
lean_ctor_set(x_2, 0, x_85);
x_86 = l_Lean_CollectMVars_main___main(x_64, x_2);
if (x_67 == 0)
{
lean_dec(x_65);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
x_89 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_87, x_65);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_86);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_86, 0);
lean_dec(x_92);
lean_inc(x_65);
x_93 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_87, x_65);
lean_ctor_set(x_86, 0, x_93);
x_1 = x_65;
x_2 = x_86;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_86);
lean_inc(x_65);
x_95 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_87, x_65);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
x_1 = x_65;
x_2 = x_96;
goto _start;
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_65);
return x_86;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_2);
lean_inc(x_64);
x_98 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_79, x_64);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_80);
x_100 = l_Lean_CollectMVars_main___main(x_64, x_99);
if (x_67 == 0)
{
lean_dec(x_65);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
x_103 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_101, x_65);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
lean_inc(x_65);
x_105 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_101, x_65);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
x_1 = x_65;
x_2 = x_106;
goto _start;
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_65);
return x_100;
}
}
}
}
else
{
lean_dec(x_64);
if (x_67 == 0)
{
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_65);
return x_2;
}
else
{
uint8_t x_108; 
x_108 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_79, x_65);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_2, 1);
lean_dec(x_110);
x_111 = lean_ctor_get(x_2, 0);
lean_dec(x_111);
lean_inc(x_65);
x_112 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_79, x_65);
lean_ctor_set(x_2, 0, x_112);
x_1 = x_65;
goto _start;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
lean_inc(x_65);
x_114 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_79, x_65);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_80);
x_1 = x_65;
x_2 = x_115;
goto _start;
}
}
else
{
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_65);
return x_2;
}
}
}
}
}
case 7:
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_1, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 2);
lean_inc(x_118);
lean_dec(x_1);
x_119 = l_Lean_Expr_hasMVar(x_117);
x_120 = l_Lean_Expr_hasMVar(x_118);
if (x_119 == 0)
{
lean_dec(x_117);
if (x_120 == 0)
{
lean_dec(x_118);
return x_2;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_121 = lean_ctor_get(x_2, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_2, 1);
lean_inc(x_122);
x_123 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_121, x_118);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_2);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_2, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_2, 0);
lean_dec(x_126);
lean_inc(x_118);
x_127 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_121, x_118);
lean_ctor_set(x_2, 0, x_127);
x_1 = x_118;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_2);
lean_inc(x_118);
x_129 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_121, x_118);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
x_1 = x_118;
x_2 = x_130;
goto _start;
}
}
else
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_118);
return x_2;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_2, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_132, x_117);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_2);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_2, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_2, 0);
lean_dec(x_137);
lean_inc(x_117);
x_138 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_132, x_117);
lean_ctor_set(x_2, 0, x_138);
x_139 = l_Lean_CollectMVars_main___main(x_117, x_2);
if (x_120 == 0)
{
lean_dec(x_118);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
x_142 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_140, x_118);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_139);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_139, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_139, 0);
lean_dec(x_145);
lean_inc(x_118);
x_146 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_140, x_118);
lean_ctor_set(x_139, 0, x_146);
x_1 = x_118;
x_2 = x_139;
goto _start;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_139);
lean_inc(x_118);
x_148 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_140, x_118);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_141);
x_1 = x_118;
x_2 = x_149;
goto _start;
}
}
else
{
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_118);
return x_139;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
lean_inc(x_117);
x_151 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_132, x_117);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_133);
x_153 = l_Lean_CollectMVars_main___main(x_117, x_152);
if (x_120 == 0)
{
lean_dec(x_118);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
x_156 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_154, x_118);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_157 = x_153;
} else {
 lean_dec_ref(x_153);
 x_157 = lean_box(0);
}
lean_inc(x_118);
x_158 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_154, x_118);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_155);
x_1 = x_118;
x_2 = x_159;
goto _start;
}
else
{
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_118);
return x_153;
}
}
}
}
else
{
lean_dec(x_117);
if (x_120 == 0)
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_118);
return x_2;
}
else
{
uint8_t x_161; 
x_161 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_132, x_118);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_2);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_2, 1);
lean_dec(x_163);
x_164 = lean_ctor_get(x_2, 0);
lean_dec(x_164);
lean_inc(x_118);
x_165 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_132, x_118);
lean_ctor_set(x_2, 0, x_165);
x_1 = x_118;
goto _start;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_2);
lean_inc(x_118);
x_167 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_132, x_118);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_133);
x_1 = x_118;
x_2 = x_168;
goto _start;
}
}
else
{
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_118);
return x_2;
}
}
}
}
}
case 8:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_189; 
x_170 = lean_ctor_get(x_1, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_1, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_1, 3);
lean_inc(x_172);
lean_dec(x_1);
x_173 = l_Lean_Expr_hasMVar(x_170);
x_174 = l_Lean_Expr_hasMVar(x_171);
x_175 = l_Lean_Expr_hasMVar(x_172);
if (x_173 == 0)
{
lean_dec(x_170);
if (x_174 == 0)
{
lean_dec(x_171);
x_176 = x_2;
goto block_188;
}
else
{
x_189 = x_2;
goto block_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_2, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_2, 1);
lean_inc(x_230);
x_231 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_229, x_170);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_2);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_2, 1);
lean_dec(x_233);
x_234 = lean_ctor_get(x_2, 0);
lean_dec(x_234);
lean_inc(x_170);
x_235 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_229, x_170);
lean_ctor_set(x_2, 0, x_235);
x_236 = l_Lean_CollectMVars_main___main(x_170, x_2);
if (x_174 == 0)
{
lean_dec(x_171);
x_176 = x_236;
goto block_188;
}
else
{
x_189 = x_236;
goto block_228;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_2);
lean_inc(x_170);
x_237 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_229, x_170);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_230);
x_239 = l_Lean_CollectMVars_main___main(x_170, x_238);
if (x_174 == 0)
{
lean_dec(x_171);
x_176 = x_239;
goto block_188;
}
else
{
x_189 = x_239;
goto block_228;
}
}
}
else
{
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_170);
if (x_174 == 0)
{
lean_dec(x_171);
x_176 = x_2;
goto block_188;
}
else
{
x_189 = x_2;
goto block_228;
}
}
}
block_188:
{
if (x_175 == 0)
{
lean_dec(x_172);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
x_179 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_177, x_172);
if (x_179 == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_176);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_176, 1);
lean_dec(x_181);
x_182 = lean_ctor_get(x_176, 0);
lean_dec(x_182);
lean_inc(x_172);
x_183 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_177, x_172);
lean_ctor_set(x_176, 0, x_183);
x_1 = x_172;
x_2 = x_176;
goto _start;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_176);
lean_inc(x_172);
x_185 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_177, x_172);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_178);
x_1 = x_172;
x_2 = x_186;
goto _start;
}
}
else
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_172);
return x_176;
}
}
}
block_228:
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
x_192 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_190, x_171);
if (x_192 == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_189);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_189, 1);
lean_dec(x_194);
x_195 = lean_ctor_get(x_189, 0);
lean_dec(x_195);
lean_inc(x_171);
x_196 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_190, x_171);
lean_ctor_set(x_189, 0, x_196);
x_197 = l_Lean_CollectMVars_main___main(x_171, x_189);
if (x_175 == 0)
{
lean_dec(x_172);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
x_200 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_198, x_172);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_197);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_197, 1);
lean_dec(x_202);
x_203 = lean_ctor_get(x_197, 0);
lean_dec(x_203);
lean_inc(x_172);
x_204 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_198, x_172);
lean_ctor_set(x_197, 0, x_204);
x_1 = x_172;
x_2 = x_197;
goto _start;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_197);
lean_inc(x_172);
x_206 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_198, x_172);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_199);
x_1 = x_172;
x_2 = x_207;
goto _start;
}
}
else
{
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_172);
return x_197;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_189);
lean_inc(x_171);
x_209 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_190, x_171);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_191);
x_211 = l_Lean_CollectMVars_main___main(x_171, x_210);
if (x_175 == 0)
{
lean_dec(x_172);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
x_214 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_212, x_172);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_215 = x_211;
} else {
 lean_dec_ref(x_211);
 x_215 = lean_box(0);
}
lean_inc(x_172);
x_216 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_212, x_172);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
x_1 = x_172;
x_2 = x_217;
goto _start;
}
else
{
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_172);
return x_211;
}
}
}
}
else
{
lean_dec(x_171);
if (x_175 == 0)
{
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_172);
return x_189;
}
else
{
uint8_t x_219; 
x_219 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_190, x_172);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_189);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_189, 1);
lean_dec(x_221);
x_222 = lean_ctor_get(x_189, 0);
lean_dec(x_222);
lean_inc(x_172);
x_223 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_190, x_172);
lean_ctor_set(x_189, 0, x_223);
x_1 = x_172;
x_2 = x_189;
goto _start;
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_189);
lean_inc(x_172);
x_225 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_190, x_172);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_191);
x_1 = x_172;
x_2 = x_226;
goto _start;
}
}
else
{
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_172);
return x_189;
}
}
}
}
}
case 10:
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_1, 1);
lean_inc(x_240);
lean_dec(x_1);
x_241 = l_Lean_Expr_hasMVar(x_240);
if (x_241 == 0)
{
lean_dec(x_240);
return x_2;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_2, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 1);
lean_inc(x_243);
x_244 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_242, x_240);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_2);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_2, 1);
lean_dec(x_246);
x_247 = lean_ctor_get(x_2, 0);
lean_dec(x_247);
lean_inc(x_240);
x_248 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_242, x_240);
lean_ctor_set(x_2, 0, x_248);
x_1 = x_240;
goto _start;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_2);
lean_inc(x_240);
x_250 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_242, x_240);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_243);
x_1 = x_240;
x_2 = x_251;
goto _start;
}
}
else
{
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_240);
return x_2;
}
}
}
case 11:
{
lean_object* x_253; uint8_t x_254; 
x_253 = lean_ctor_get(x_1, 2);
lean_inc(x_253);
lean_dec(x_1);
x_254 = l_Lean_Expr_hasMVar(x_253);
if (x_254 == 0)
{
lean_dec(x_253);
return x_2;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_255 = lean_ctor_get(x_2, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_2, 1);
lean_inc(x_256);
x_257 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_255, x_253);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_2);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_2, 1);
lean_dec(x_259);
x_260 = lean_ctor_get(x_2, 0);
lean_dec(x_260);
lean_inc(x_253);
x_261 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_255, x_253);
lean_ctor_set(x_2, 0, x_261);
x_1 = x_253;
goto _start;
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_2);
lean_inc(x_253);
x_263 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_255, x_253);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_256);
x_1 = x_253;
x_2 = x_264;
goto _start;
}
}
else
{
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_253);
return x_2;
}
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_CollectMVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectMVars_main___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_collectMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
lean_inc(x_2);
x_10 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_2);
lean_ctor_set(x_1, 0, x_10);
x_11 = l_Lean_CollectMVars_main___main(x_2, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
lean_inc(x_2);
x_12 = l_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = l_Lean_CollectMVars_main___main(x_2, x_13);
return x_14;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_CollectMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectMVars_State_inhabited___closed__1 = _init_l_Lean_CollectMVars_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_CollectMVars_State_inhabited___closed__1);
l_Lean_CollectMVars_State_inhabited___closed__2 = _init_l_Lean_CollectMVars_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_CollectMVars_State_inhabited___closed__2);
l_Lean_CollectMVars_State_inhabited = _init_l_Lean_CollectMVars_State_inhabited();
lean_mark_persistent(l_Lean_CollectMVars_State_inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
