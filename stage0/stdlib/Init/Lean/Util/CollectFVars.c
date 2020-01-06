// Lean compiler output
// Module: Init.Lean.Util.CollectFVars
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
lean_object* l_Lean_CollectFVars_State_inhabited;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__2;
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectFVars_State_inhabited___spec__2(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectFVars_State_inhabited___spec__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__6(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectFVars_State_inhabited___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_CollectFVars_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectFVars_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectFVars_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_CollectFVars_State_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_CollectFVars_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectFVars_State_inhabited___closed__2;
return x_1;
}
}
uint8_t l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__4(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(x_2, x_3, x_10);
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
x_26 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__4(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_CollectFVars_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_2);
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
x_7 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_5, x_2);
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
x_12 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2, x_11);
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
x_15 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2, x_14);
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
lean_object* l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_CollectFVars_main___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_5, x_3, x_6);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_9, x_3, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_30 = l_Lean_Expr_hasFVar(x_13);
x_31 = l_Lean_Expr_hasFVar(x_14);
if (x_30 == 0)
{
lean_dec(x_13);
if (x_31 == 0)
{
lean_dec(x_14);
return x_2;
}
else
{
x_15 = x_2;
goto block_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_32, x_13);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_2, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_inc(x_13);
x_39 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_32, x_13, x_38);
lean_ctor_set(x_2, 0, x_39);
x_40 = l_Lean_CollectFVars_main___main(x_13, x_2);
if (x_31 == 0)
{
lean_dec(x_14);
return x_40;
}
else
{
x_15 = x_40;
goto block_29;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_41 = lean_box(0);
lean_inc(x_13);
x_42 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_32, x_13, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_CollectFVars_main___main(x_13, x_43);
if (x_31 == 0)
{
lean_dec(x_14);
return x_44;
}
else
{
x_15 = x_44;
goto block_29;
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
if (x_31 == 0)
{
lean_dec(x_14);
return x_2;
}
else
{
x_15 = x_2;
goto block_29;
}
}
}
block_29:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_16, x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_inc(x_14);
x_23 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_16, x_14, x_22);
lean_ctor_set(x_15, 0, x_23);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = lean_box(0);
lean_inc(x_14);
x_26 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_16, x_14, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_1 = x_14;
x_2 = x_27;
goto _start;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
return x_15;
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_62; uint8_t x_63; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_62 = l_Lean_Expr_hasFVar(x_45);
x_63 = l_Lean_Expr_hasFVar(x_46);
if (x_62 == 0)
{
lean_dec(x_45);
if (x_63 == 0)
{
lean_dec(x_46);
return x_2;
}
else
{
x_47 = x_2;
goto block_61;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
x_66 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_64, x_45);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_2, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_2, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_inc(x_45);
x_71 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_64, x_45, x_70);
lean_ctor_set(x_2, 0, x_71);
x_72 = l_Lean_CollectFVars_main___main(x_45, x_2);
if (x_63 == 0)
{
lean_dec(x_46);
return x_72;
}
else
{
x_47 = x_72;
goto block_61;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
x_73 = lean_box(0);
lean_inc(x_45);
x_74 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_64, x_45, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_65);
x_76 = l_Lean_CollectFVars_main___main(x_45, x_75);
if (x_63 == 0)
{
lean_dec(x_46);
return x_76;
}
else
{
x_47 = x_76;
goto block_61;
}
}
}
else
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_45);
if (x_63 == 0)
{
lean_dec(x_46);
return x_2;
}
else
{
x_47 = x_2;
goto block_61;
}
}
}
block_61:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_50 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_48, x_46);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_inc(x_46);
x_55 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_48, x_46, x_54);
lean_ctor_set(x_47, 0, x_55);
x_1 = x_46;
x_2 = x_47;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_47);
x_57 = lean_box(0);
lean_inc(x_46);
x_58 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_48, x_46, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_1 = x_46;
x_2 = x_59;
goto _start;
}
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_46);
return x_47;
}
}
}
case 7:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_94; uint8_t x_95; 
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 2);
lean_inc(x_78);
lean_dec(x_1);
x_94 = l_Lean_Expr_hasFVar(x_77);
x_95 = l_Lean_Expr_hasFVar(x_78);
if (x_94 == 0)
{
lean_dec(x_77);
if (x_95 == 0)
{
lean_dec(x_78);
return x_2;
}
else
{
x_79 = x_2;
goto block_93;
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
x_98 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_96, x_77);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_2);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_2, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_2, 0);
lean_dec(x_101);
x_102 = lean_box(0);
lean_inc(x_77);
x_103 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_96, x_77, x_102);
lean_ctor_set(x_2, 0, x_103);
x_104 = l_Lean_CollectFVars_main___main(x_77, x_2);
if (x_95 == 0)
{
lean_dec(x_78);
return x_104;
}
else
{
x_79 = x_104;
goto block_93;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_2);
x_105 = lean_box(0);
lean_inc(x_77);
x_106 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_96, x_77, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = l_Lean_CollectFVars_main___main(x_77, x_107);
if (x_95 == 0)
{
lean_dec(x_78);
return x_108;
}
else
{
x_79 = x_108;
goto block_93;
}
}
}
else
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_77);
if (x_95 == 0)
{
lean_dec(x_78);
return x_2;
}
else
{
x_79 = x_2;
goto block_93;
}
}
}
block_93:
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_80, x_78);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_79, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_inc(x_78);
x_87 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_80, x_78, x_86);
lean_ctor_set(x_79, 0, x_87);
x_1 = x_78;
x_2 = x_79;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_79);
x_89 = lean_box(0);
lean_inc(x_78);
x_90 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_80, x_78, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
x_1 = x_78;
x_2 = x_91;
goto _start;
}
}
else
{
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_78);
return x_79;
}
}
}
case 8:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; 
x_109 = lean_ctor_get(x_1, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_1, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 3);
lean_inc(x_111);
lean_dec(x_1);
x_127 = l_Lean_Expr_hasFVar(x_109);
x_128 = l_Lean_Expr_hasFVar(x_110);
x_129 = l_Lean_Expr_hasFVar(x_111);
if (x_127 == 0)
{
lean_dec(x_109);
if (x_128 == 0)
{
lean_dec(x_110);
if (x_129 == 0)
{
lean_dec(x_111);
return x_2;
}
else
{
x_112 = x_2;
goto block_126;
}
}
else
{
x_130 = x_2;
goto block_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_2, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_2, 1);
lean_inc(x_146);
x_147 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_145, x_109);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_2);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_2, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_2, 0);
lean_dec(x_150);
x_151 = lean_box(0);
lean_inc(x_109);
x_152 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_145, x_109, x_151);
lean_ctor_set(x_2, 0, x_152);
x_153 = l_Lean_CollectFVars_main___main(x_109, x_2);
if (x_128 == 0)
{
lean_dec(x_110);
if (x_129 == 0)
{
lean_dec(x_111);
return x_153;
}
else
{
x_112 = x_153;
goto block_126;
}
}
else
{
x_130 = x_153;
goto block_144;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_154 = lean_box(0);
lean_inc(x_109);
x_155 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_145, x_109, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_146);
x_157 = l_Lean_CollectFVars_main___main(x_109, x_156);
if (x_128 == 0)
{
lean_dec(x_110);
if (x_129 == 0)
{
lean_dec(x_111);
return x_157;
}
else
{
x_112 = x_157;
goto block_126;
}
}
else
{
x_130 = x_157;
goto block_144;
}
}
}
else
{
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_109);
if (x_128 == 0)
{
lean_dec(x_110);
if (x_129 == 0)
{
lean_dec(x_111);
return x_2;
}
else
{
x_112 = x_2;
goto block_126;
}
}
else
{
x_130 = x_2;
goto block_144;
}
}
}
block_126:
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
x_115 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_113, x_111);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_112);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_112, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_inc(x_111);
x_120 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_113, x_111, x_119);
lean_ctor_set(x_112, 0, x_120);
x_1 = x_111;
x_2 = x_112;
goto _start;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_112);
x_122 = lean_box(0);
lean_inc(x_111);
x_123 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_113, x_111, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_114);
x_1 = x_111;
x_2 = x_124;
goto _start;
}
}
else
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_111);
return x_112;
}
}
block_144:
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
x_133 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_131, x_110);
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_130);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_130, 1);
lean_dec(x_135);
x_136 = lean_ctor_get(x_130, 0);
lean_dec(x_136);
x_137 = lean_box(0);
lean_inc(x_110);
x_138 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_131, x_110, x_137);
lean_ctor_set(x_130, 0, x_138);
x_139 = l_Lean_CollectFVars_main___main(x_110, x_130);
if (x_129 == 0)
{
lean_dec(x_111);
return x_139;
}
else
{
x_112 = x_139;
goto block_126;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_130);
x_140 = lean_box(0);
lean_inc(x_110);
x_141 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_131, x_110, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_132);
x_143 = l_Lean_CollectFVars_main___main(x_110, x_142);
if (x_129 == 0)
{
lean_dec(x_111);
return x_143;
}
else
{
x_112 = x_143;
goto block_126;
}
}
}
else
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_110);
if (x_129 == 0)
{
lean_dec(x_111);
return x_130;
}
else
{
x_112 = x_130;
goto block_126;
}
}
}
}
case 10:
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_1, 1);
lean_inc(x_158);
lean_dec(x_1);
x_159 = l_Lean_Expr_hasFVar(x_158);
if (x_159 == 0)
{
lean_dec(x_158);
return x_2;
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_2, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_2, 1);
lean_inc(x_161);
x_162 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_160, x_158);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_2);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_2, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_2, 0);
lean_dec(x_165);
x_166 = lean_box(0);
lean_inc(x_158);
x_167 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_160, x_158, x_166);
lean_ctor_set(x_2, 0, x_167);
x_1 = x_158;
goto _start;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_2);
x_169 = lean_box(0);
lean_inc(x_158);
x_170 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_160, x_158, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_161);
x_1 = x_158;
x_2 = x_171;
goto _start;
}
}
else
{
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
return x_2;
}
}
}
case 11:
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
lean_dec(x_1);
x_174 = l_Lean_Expr_hasFVar(x_173);
if (x_174 == 0)
{
lean_dec(x_173);
return x_2;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_inc(x_176);
x_177 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__1(x_175, x_173);
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_2);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_2, 0);
lean_dec(x_180);
x_181 = lean_box(0);
lean_inc(x_173);
x_182 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_175, x_173, x_181);
lean_ctor_set(x_2, 0, x_182);
x_1 = x_173;
goto _start;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_2);
x_184 = lean_box(0);
lean_inc(x_173);
x_185 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__3(x_175, x_173, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
x_1 = x_173;
x_2 = x_186;
goto _start;
}
}
else
{
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_173);
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
lean_object* l_Lean_CollectFVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectFVars_main___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_collectFVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectFVars_main___main(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_CollectFVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectFVars_State_inhabited___closed__1 = _init_l_Lean_CollectFVars_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_CollectFVars_State_inhabited___closed__1);
l_Lean_CollectFVars_State_inhabited___closed__2 = _init_l_Lean_CollectFVars_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_CollectFVars_State_inhabited___closed__2);
l_Lean_CollectFVars_State_inhabited = _init_l_Lean_CollectFVars_State_inhabited();
lean_mark_persistent(l_Lean_CollectFVars_State_inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
