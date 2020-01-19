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
lean_object* l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__6(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_main___main(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_mkHashSet___at_Lean_CollectMVars_State_inhabited___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectMVars_State_inhabited___spec__2(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__1;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_main(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectMVars_State_inhabited___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_CollectMVars_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectMVars_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
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
uint8_t l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
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
uint8_t l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__4(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
x_7 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_5, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_inc(x_2);
x_12 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_5, x_2, x_11);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_apply_2(x_1, x_2, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_14 = lean_box(0);
lean_inc(x_2);
x_15 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_5, x_2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_apply_2(x_1, x_2, x_16);
return x_17;
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
lean_object* l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_28; uint8_t x_29; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_28 = l_Lean_Expr_hasMVar(x_11);
x_29 = l_Lean_Expr_hasMVar(x_12);
if (x_28 == 0)
{
lean_dec(x_11);
if (x_29 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
x_13 = x_2;
goto block_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_30, x_11);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_2, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_inc(x_11);
x_37 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_30, x_11, x_36);
lean_ctor_set(x_2, 0, x_37);
x_38 = l_Lean_CollectMVars_main___main(x_11, x_2);
if (x_29 == 0)
{
lean_dec(x_12);
return x_38;
}
else
{
x_13 = x_38;
goto block_27;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_39 = lean_box(0);
lean_inc(x_11);
x_40 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_30, x_11, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
x_42 = l_Lean_CollectMVars_main___main(x_11, x_41);
if (x_29 == 0)
{
lean_dec(x_12);
return x_42;
}
else
{
x_13 = x_42;
goto block_27;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
if (x_29 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
x_13 = x_2;
goto block_27;
}
}
}
block_27:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_14, x_12);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_inc(x_12);
x_21 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_14, x_12, x_20);
lean_ctor_set(x_13, 0, x_21);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_23 = lean_box(0);
lean_inc(x_12);
x_24 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_14, x_12, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
x_1 = x_12;
x_2 = x_25;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
return x_13;
}
}
}
case 6:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_60; uint8_t x_61; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_60 = l_Lean_Expr_hasMVar(x_43);
x_61 = l_Lean_Expr_hasMVar(x_44);
if (x_60 == 0)
{
lean_dec(x_43);
if (x_61 == 0)
{
lean_dec(x_44);
return x_2;
}
else
{
x_45 = x_2;
goto block_59;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_62, x_43);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_2, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_2, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_inc(x_43);
x_69 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_62, x_43, x_68);
lean_ctor_set(x_2, 0, x_69);
x_70 = l_Lean_CollectMVars_main___main(x_43, x_2);
if (x_61 == 0)
{
lean_dec(x_44);
return x_70;
}
else
{
x_45 = x_70;
goto block_59;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_71 = lean_box(0);
lean_inc(x_43);
x_72 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_62, x_43, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_63);
x_74 = l_Lean_CollectMVars_main___main(x_43, x_73);
if (x_61 == 0)
{
lean_dec(x_44);
return x_74;
}
else
{
x_45 = x_74;
goto block_59;
}
}
}
else
{
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_43);
if (x_61 == 0)
{
lean_dec(x_44);
return x_2;
}
else
{
x_45 = x_2;
goto block_59;
}
}
}
block_59:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_46, x_44);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_45, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_inc(x_44);
x_53 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_46, x_44, x_52);
lean_ctor_set(x_45, 0, x_53);
x_1 = x_44;
x_2 = x_45;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_45);
x_55 = lean_box(0);
lean_inc(x_44);
x_56 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_46, x_44, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
x_1 = x_44;
x_2 = x_57;
goto _start;
}
}
else
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
return x_45;
}
}
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_92; uint8_t x_93; 
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
lean_dec(x_1);
x_92 = l_Lean_Expr_hasMVar(x_75);
x_93 = l_Lean_Expr_hasMVar(x_76);
if (x_92 == 0)
{
lean_dec(x_75);
if (x_93 == 0)
{
lean_dec(x_76);
return x_2;
}
else
{
x_77 = x_2;
goto block_91;
}
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
x_96 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_94, x_75);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_2, 1);
lean_dec(x_98);
x_99 = lean_ctor_get(x_2, 0);
lean_dec(x_99);
x_100 = lean_box(0);
lean_inc(x_75);
x_101 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_94, x_75, x_100);
lean_ctor_set(x_2, 0, x_101);
x_102 = l_Lean_CollectMVars_main___main(x_75, x_2);
if (x_93 == 0)
{
lean_dec(x_76);
return x_102;
}
else
{
x_77 = x_102;
goto block_91;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_2);
x_103 = lean_box(0);
lean_inc(x_75);
x_104 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_94, x_75, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = l_Lean_CollectMVars_main___main(x_75, x_105);
if (x_93 == 0)
{
lean_dec(x_76);
return x_106;
}
else
{
x_77 = x_106;
goto block_91;
}
}
}
else
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_75);
if (x_93 == 0)
{
lean_dec(x_76);
return x_2;
}
else
{
x_77 = x_2;
goto block_91;
}
}
}
block_91:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
x_80 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_78, x_76);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 1);
lean_dec(x_82);
x_83 = lean_ctor_get(x_77, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_inc(x_76);
x_85 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_78, x_76, x_84);
lean_ctor_set(x_77, 0, x_85);
x_1 = x_76;
x_2 = x_77;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_77);
x_87 = lean_box(0);
lean_inc(x_76);
x_88 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_78, x_76, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_79);
x_1 = x_76;
x_2 = x_89;
goto _start;
}
}
else
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_76);
return x_77;
}
}
}
case 8:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; 
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 3);
lean_inc(x_109);
lean_dec(x_1);
x_125 = l_Lean_Expr_hasMVar(x_107);
x_126 = l_Lean_Expr_hasMVar(x_108);
x_127 = l_Lean_Expr_hasMVar(x_109);
if (x_125 == 0)
{
lean_dec(x_107);
if (x_126 == 0)
{
lean_dec(x_108);
if (x_127 == 0)
{
lean_dec(x_109);
return x_2;
}
else
{
x_110 = x_2;
goto block_124;
}
}
else
{
x_128 = x_2;
goto block_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_2, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 1);
lean_inc(x_144);
x_145 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_143, x_107);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_2);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_2, 1);
lean_dec(x_147);
x_148 = lean_ctor_get(x_2, 0);
lean_dec(x_148);
x_149 = lean_box(0);
lean_inc(x_107);
x_150 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_143, x_107, x_149);
lean_ctor_set(x_2, 0, x_150);
x_151 = l_Lean_CollectMVars_main___main(x_107, x_2);
if (x_126 == 0)
{
lean_dec(x_108);
if (x_127 == 0)
{
lean_dec(x_109);
return x_151;
}
else
{
x_110 = x_151;
goto block_124;
}
}
else
{
x_128 = x_151;
goto block_142;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
x_152 = lean_box(0);
lean_inc(x_107);
x_153 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_143, x_107, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
x_155 = l_Lean_CollectMVars_main___main(x_107, x_154);
if (x_126 == 0)
{
lean_dec(x_108);
if (x_127 == 0)
{
lean_dec(x_109);
return x_155;
}
else
{
x_110 = x_155;
goto block_124;
}
}
else
{
x_128 = x_155;
goto block_142;
}
}
}
else
{
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_107);
if (x_126 == 0)
{
lean_dec(x_108);
if (x_127 == 0)
{
lean_dec(x_109);
return x_2;
}
else
{
x_110 = x_2;
goto block_124;
}
}
else
{
x_128 = x_2;
goto block_142;
}
}
}
block_124:
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
x_113 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_111, x_109);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_110, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_110, 0);
lean_dec(x_116);
x_117 = lean_box(0);
lean_inc(x_109);
x_118 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_111, x_109, x_117);
lean_ctor_set(x_110, 0, x_118);
x_1 = x_109;
x_2 = x_110;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_110);
x_120 = lean_box(0);
lean_inc(x_109);
x_121 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_111, x_109, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_112);
x_1 = x_109;
x_2 = x_122;
goto _start;
}
}
else
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
return x_110;
}
}
block_142:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
x_131 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_129, x_108);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_128, 1);
lean_dec(x_133);
x_134 = lean_ctor_get(x_128, 0);
lean_dec(x_134);
x_135 = lean_box(0);
lean_inc(x_108);
x_136 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_129, x_108, x_135);
lean_ctor_set(x_128, 0, x_136);
x_137 = l_Lean_CollectMVars_main___main(x_108, x_128);
if (x_127 == 0)
{
lean_dec(x_109);
return x_137;
}
else
{
x_110 = x_137;
goto block_124;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_128);
x_138 = lean_box(0);
lean_inc(x_108);
x_139 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_129, x_108, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_130);
x_141 = l_Lean_CollectMVars_main___main(x_108, x_140);
if (x_127 == 0)
{
lean_dec(x_109);
return x_141;
}
else
{
x_110 = x_141;
goto block_124;
}
}
}
else
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_108);
if (x_127 == 0)
{
lean_dec(x_109);
return x_128;
}
else
{
x_110 = x_128;
goto block_124;
}
}
}
}
case 10:
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_1, 1);
lean_inc(x_156);
lean_dec(x_1);
x_157 = l_Lean_Expr_hasMVar(x_156);
if (x_157 == 0)
{
lean_dec(x_156);
return x_2;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_2, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_2, 1);
lean_inc(x_159);
x_160 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_158, x_156);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_2);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_2, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_2, 0);
lean_dec(x_163);
x_164 = lean_box(0);
lean_inc(x_156);
x_165 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_158, x_156, x_164);
lean_ctor_set(x_2, 0, x_165);
x_1 = x_156;
goto _start;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_2);
x_167 = lean_box(0);
lean_inc(x_156);
x_168 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_158, x_156, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_159);
x_1 = x_156;
x_2 = x_169;
goto _start;
}
}
else
{
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_156);
return x_2;
}
}
}
case 11:
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_1, 2);
lean_inc(x_171);
lean_dec(x_1);
x_172 = l_Lean_Expr_hasMVar(x_171);
if (x_172 == 0)
{
lean_dec(x_171);
return x_2;
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_2, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_2, 1);
lean_inc(x_174);
x_175 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_173, x_171);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_2);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_2, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_2, 0);
lean_dec(x_178);
x_179 = lean_box(0);
lean_inc(x_171);
x_180 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_173, x_171, x_179);
lean_ctor_set(x_2, 0, x_180);
x_1 = x_171;
goto _start;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_2);
x_182 = lean_box(0);
lean_inc(x_171);
x_183 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_173, x_171, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_174);
x_1 = x_171;
x_2 = x_184;
goto _start;
}
}
else
{
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_171);
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
x_6 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__1(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_inc(x_2);
x_11 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_2, x_10);
lean_ctor_set(x_1, 0, x_11);
x_12 = l_Lean_CollectMVars_main___main(x_2, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_13 = lean_box(0);
lean_inc(x_2);
x_14 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = l_Lean_CollectMVars_main___main(x_2, x_15);
return x_16;
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
