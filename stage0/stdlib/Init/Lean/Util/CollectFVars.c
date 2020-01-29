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
lean_object* l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__2;
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__1;
lean_object* l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__5(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectFVars_State_inhabited___spec__2(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__3(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectFVars_State_inhabited___spec__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
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
lean_object* l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectFVars_visit___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_array_uset(x_6, x_9, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__3(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
x_25 = lean_usize_modn(x_24, x_23);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_AssocList_contains___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_26);
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_26);
x_32 = lean_array_uset(x_22, x_25, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_HashMapImp_expand___at_Lean_CollectFVars_visit___spec__3(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_AssocList_replace___main___at_Lean_CollectFVars_visit___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_CollectFVars_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_String_posOfAux___main___closed__2;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_7, x_2, x_8);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
lean_inc(x_2);
x_14 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_11, x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_apply_2(x_1, x_2, x_15);
return x_16;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_17, x_2);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_3, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_3, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_inc(x_2);
x_25 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_17, x_2, x_24);
lean_ctor_set(x_3, 0, x_25);
x_26 = lean_apply_2(x_1, x_2, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_3);
x_27 = lean_box(0);
lean_inc(x_2);
x_28 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_17, x_2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_30 = lean_apply_2(x_1, x_2, x_29);
return x_30;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
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
lean_object* l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_1, x_2);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_29; uint8_t x_45; uint8_t x_46; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_45 = l_Lean_Expr_hasFVar(x_13);
x_46 = l_Lean_Expr_hasFVar(x_14);
if (x_45 == 0)
{
uint8_t x_47; 
x_47 = l_String_posOfAux___main___closed__2;
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_box(0);
lean_inc(x_13);
x_51 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_49, x_13, x_50);
lean_ctor_set(x_2, 0, x_51);
x_52 = l_Lean_CollectFVars_main___main(x_13, x_2);
if (x_46 == 0)
{
x_15 = x_52;
goto block_28;
}
else
{
x_29 = x_52;
goto block_44;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_55 = lean_box(0);
lean_inc(x_13);
x_56 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_53, x_13, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
x_58 = l_Lean_CollectFVars_main___main(x_13, x_57);
if (x_46 == 0)
{
x_15 = x_58;
goto block_28;
}
else
{
x_29 = x_58;
goto block_44;
}
}
}
else
{
lean_dec(x_13);
if (x_46 == 0)
{
x_15 = x_2;
goto block_28;
}
else
{
x_29 = x_2;
goto block_44;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_61 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_59, x_13);
x_62 = l_coeDecidableEq(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_2, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_2, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_inc(x_13);
x_67 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_59, x_13, x_66);
lean_ctor_set(x_2, 0, x_67);
x_68 = l_Lean_CollectFVars_main___main(x_13, x_2);
if (x_46 == 0)
{
x_15 = x_68;
goto block_28;
}
else
{
x_29 = x_68;
goto block_44;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_2);
x_69 = lean_box(0);
lean_inc(x_13);
x_70 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_59, x_13, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_60);
x_72 = l_Lean_CollectFVars_main___main(x_13, x_71);
if (x_46 == 0)
{
x_15 = x_72;
goto block_28;
}
else
{
x_29 = x_72;
goto block_44;
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_13);
if (x_46 == 0)
{
x_15 = x_2;
goto block_28;
}
else
{
x_29 = x_2;
goto block_44;
}
}
}
block_28:
{
uint8_t x_16; 
x_16 = l_String_posOfAux___main___closed__2;
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_box(0);
lean_inc(x_14);
x_20 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_18, x_14, x_19);
lean_ctor_set(x_15, 0, x_20);
x_1 = x_14;
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_box(0);
lean_inc(x_14);
x_25 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_22, x_14, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_1 = x_14;
x_2 = x_26;
goto _start;
}
}
else
{
lean_dec(x_14);
return x_15;
}
}
block_44:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_30, x_14);
x_33 = l_coeDecidableEq(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_inc(x_14);
x_38 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_30, x_14, x_37);
lean_ctor_set(x_29, 0, x_38);
x_1 = x_14;
x_2 = x_29;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_40 = lean_box(0);
lean_inc(x_14);
x_41 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_30, x_14, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_31);
x_1 = x_14;
x_2 = x_42;
goto _start;
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_14);
return x_29;
}
}
}
case 6:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_89; uint8_t x_105; uint8_t x_106; 
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_dec(x_1);
x_105 = l_Lean_Expr_hasFVar(x_73);
x_106 = l_Lean_Expr_hasFVar(x_74);
if (x_105 == 0)
{
uint8_t x_107; 
x_107 = l_String_posOfAux___main___closed__2;
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_2);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_2, 0);
x_110 = lean_box(0);
lean_inc(x_73);
x_111 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_109, x_73, x_110);
lean_ctor_set(x_2, 0, x_111);
x_112 = l_Lean_CollectFVars_main___main(x_73, x_2);
if (x_106 == 0)
{
x_75 = x_112;
goto block_88;
}
else
{
x_89 = x_112;
goto block_104;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_2, 0);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_2);
x_115 = lean_box(0);
lean_inc(x_73);
x_116 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_113, x_73, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
x_118 = l_Lean_CollectFVars_main___main(x_73, x_117);
if (x_106 == 0)
{
x_75 = x_118;
goto block_88;
}
else
{
x_89 = x_118;
goto block_104;
}
}
}
else
{
lean_dec(x_73);
if (x_106 == 0)
{
x_75 = x_2;
goto block_88;
}
else
{
x_89 = x_2;
goto block_104;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_2, 1);
lean_inc(x_120);
x_121 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_119, x_73);
x_122 = l_coeDecidableEq(x_121);
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_2);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_2, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_2, 0);
lean_dec(x_125);
x_126 = lean_box(0);
lean_inc(x_73);
x_127 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_119, x_73, x_126);
lean_ctor_set(x_2, 0, x_127);
x_128 = l_Lean_CollectFVars_main___main(x_73, x_2);
if (x_106 == 0)
{
x_75 = x_128;
goto block_88;
}
else
{
x_89 = x_128;
goto block_104;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_2);
x_129 = lean_box(0);
lean_inc(x_73);
x_130 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_119, x_73, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_120);
x_132 = l_Lean_CollectFVars_main___main(x_73, x_131);
if (x_106 == 0)
{
x_75 = x_132;
goto block_88;
}
else
{
x_89 = x_132;
goto block_104;
}
}
}
else
{
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_73);
if (x_106 == 0)
{
x_75 = x_2;
goto block_88;
}
else
{
x_89 = x_2;
goto block_104;
}
}
}
block_88:
{
uint8_t x_76; 
x_76 = l_String_posOfAux___main___closed__2;
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_box(0);
lean_inc(x_74);
x_80 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_78, x_74, x_79);
lean_ctor_set(x_75, 0, x_80);
x_1 = x_74;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
x_84 = lean_box(0);
lean_inc(x_74);
x_85 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_82, x_74, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_1 = x_74;
x_2 = x_86;
goto _start;
}
}
else
{
lean_dec(x_74);
return x_75;
}
}
block_104:
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
x_92 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_90, x_74);
x_93 = l_coeDecidableEq(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 1);
lean_dec(x_95);
x_96 = lean_ctor_get(x_89, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_inc(x_74);
x_98 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_90, x_74, x_97);
lean_ctor_set(x_89, 0, x_98);
x_1 = x_74;
x_2 = x_89;
goto _start;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_89);
x_100 = lean_box(0);
lean_inc(x_74);
x_101 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_90, x_74, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
x_1 = x_74;
x_2 = x_102;
goto _start;
}
}
else
{
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_74);
return x_89;
}
}
}
case 7:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_149; uint8_t x_165; uint8_t x_166; 
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_1, 2);
lean_inc(x_134);
lean_dec(x_1);
x_165 = l_Lean_Expr_hasFVar(x_133);
x_166 = l_Lean_Expr_hasFVar(x_134);
if (x_165 == 0)
{
uint8_t x_167; 
x_167 = l_String_posOfAux___main___closed__2;
if (x_167 == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_2);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_2, 0);
x_170 = lean_box(0);
lean_inc(x_133);
x_171 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_169, x_133, x_170);
lean_ctor_set(x_2, 0, x_171);
x_172 = l_Lean_CollectFVars_main___main(x_133, x_2);
if (x_166 == 0)
{
x_135 = x_172;
goto block_148;
}
else
{
x_149 = x_172;
goto block_164;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_2, 0);
x_174 = lean_ctor_get(x_2, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_2);
x_175 = lean_box(0);
lean_inc(x_133);
x_176 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_173, x_133, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
x_178 = l_Lean_CollectFVars_main___main(x_133, x_177);
if (x_166 == 0)
{
x_135 = x_178;
goto block_148;
}
else
{
x_149 = x_178;
goto block_164;
}
}
}
else
{
lean_dec(x_133);
if (x_166 == 0)
{
x_135 = x_2;
goto block_148;
}
else
{
x_149 = x_2;
goto block_164;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_179, x_133);
x_182 = l_coeDecidableEq(x_181);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_2);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_2, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_2, 0);
lean_dec(x_185);
x_186 = lean_box(0);
lean_inc(x_133);
x_187 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_179, x_133, x_186);
lean_ctor_set(x_2, 0, x_187);
x_188 = l_Lean_CollectFVars_main___main(x_133, x_2);
if (x_166 == 0)
{
x_135 = x_188;
goto block_148;
}
else
{
x_149 = x_188;
goto block_164;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_2);
x_189 = lean_box(0);
lean_inc(x_133);
x_190 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_179, x_133, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_180);
x_192 = l_Lean_CollectFVars_main___main(x_133, x_191);
if (x_166 == 0)
{
x_135 = x_192;
goto block_148;
}
else
{
x_149 = x_192;
goto block_164;
}
}
}
else
{
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_133);
if (x_166 == 0)
{
x_135 = x_2;
goto block_148;
}
else
{
x_149 = x_2;
goto block_164;
}
}
}
block_148:
{
uint8_t x_136; 
x_136 = l_String_posOfAux___main___closed__2;
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_135, 0);
x_139 = lean_box(0);
lean_inc(x_134);
x_140 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_138, x_134, x_139);
lean_ctor_set(x_135, 0, x_140);
x_1 = x_134;
x_2 = x_135;
goto _start;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_135, 0);
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_135);
x_144 = lean_box(0);
lean_inc(x_134);
x_145 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_142, x_134, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
x_1 = x_134;
x_2 = x_146;
goto _start;
}
}
else
{
lean_dec(x_134);
return x_135;
}
}
block_164:
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
x_152 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_150, x_134);
x_153 = l_coeDecidableEq(x_152);
if (x_153 == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_149);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_149, 1);
lean_dec(x_155);
x_156 = lean_ctor_get(x_149, 0);
lean_dec(x_156);
x_157 = lean_box(0);
lean_inc(x_134);
x_158 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_150, x_134, x_157);
lean_ctor_set(x_149, 0, x_158);
x_1 = x_134;
x_2 = x_149;
goto _start;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_149);
x_160 = lean_box(0);
lean_inc(x_134);
x_161 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_150, x_134, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_151);
x_1 = x_134;
x_2 = x_162;
goto _start;
}
}
else
{
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_134);
return x_149;
}
}
}
case 8:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_210; uint8_t x_226; uint8_t x_227; uint8_t x_228; lean_object* x_229; lean_object* x_243; 
x_193 = lean_ctor_get(x_1, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_1, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_1, 3);
lean_inc(x_195);
lean_dec(x_1);
x_226 = l_Lean_Expr_hasFVar(x_193);
x_227 = l_Lean_Expr_hasFVar(x_194);
x_228 = l_Lean_Expr_hasFVar(x_195);
if (x_226 == 0)
{
uint8_t x_259; 
x_259 = l_String_posOfAux___main___closed__2;
if (x_259 == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_2);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_2, 0);
x_262 = lean_box(0);
lean_inc(x_193);
x_263 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_261, x_193, x_262);
lean_ctor_set(x_2, 0, x_263);
x_264 = l_Lean_CollectFVars_main___main(x_193, x_2);
if (x_227 == 0)
{
x_229 = x_264;
goto block_242;
}
else
{
x_243 = x_264;
goto block_258;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_2, 0);
x_266 = lean_ctor_get(x_2, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_2);
x_267 = lean_box(0);
lean_inc(x_193);
x_268 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_265, x_193, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
x_270 = l_Lean_CollectFVars_main___main(x_193, x_269);
if (x_227 == 0)
{
x_229 = x_270;
goto block_242;
}
else
{
x_243 = x_270;
goto block_258;
}
}
}
else
{
lean_dec(x_193);
if (x_227 == 0)
{
x_229 = x_2;
goto block_242;
}
else
{
x_243 = x_2;
goto block_258;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_2, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_2, 1);
lean_inc(x_272);
x_273 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_271, x_193);
x_274 = l_coeDecidableEq(x_273);
if (x_274 == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_2);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_2, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_2, 0);
lean_dec(x_277);
x_278 = lean_box(0);
lean_inc(x_193);
x_279 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_271, x_193, x_278);
lean_ctor_set(x_2, 0, x_279);
x_280 = l_Lean_CollectFVars_main___main(x_193, x_2);
if (x_227 == 0)
{
x_229 = x_280;
goto block_242;
}
else
{
x_243 = x_280;
goto block_258;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_2);
x_281 = lean_box(0);
lean_inc(x_193);
x_282 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_271, x_193, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_272);
x_284 = l_Lean_CollectFVars_main___main(x_193, x_283);
if (x_227 == 0)
{
x_229 = x_284;
goto block_242;
}
else
{
x_243 = x_284;
goto block_258;
}
}
}
else
{
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_193);
if (x_227 == 0)
{
x_229 = x_2;
goto block_242;
}
else
{
x_243 = x_2;
goto block_258;
}
}
}
block_209:
{
uint8_t x_197; 
x_197 = l_String_posOfAux___main___closed__2;
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 0);
x_200 = lean_box(0);
lean_inc(x_195);
x_201 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_199, x_195, x_200);
lean_ctor_set(x_196, 0, x_201);
x_1 = x_195;
x_2 = x_196;
goto _start;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_196, 0);
x_204 = lean_ctor_get(x_196, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_196);
x_205 = lean_box(0);
lean_inc(x_195);
x_206 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_203, x_195, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
x_1 = x_195;
x_2 = x_207;
goto _start;
}
}
else
{
lean_dec(x_195);
return x_196;
}
}
block_225:
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
x_213 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_211, x_195);
x_214 = l_coeDecidableEq(x_213);
if (x_214 == 0)
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_210);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_210, 1);
lean_dec(x_216);
x_217 = lean_ctor_get(x_210, 0);
lean_dec(x_217);
x_218 = lean_box(0);
lean_inc(x_195);
x_219 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_211, x_195, x_218);
lean_ctor_set(x_210, 0, x_219);
x_1 = x_195;
x_2 = x_210;
goto _start;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_210);
x_221 = lean_box(0);
lean_inc(x_195);
x_222 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_211, x_195, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_212);
x_1 = x_195;
x_2 = x_223;
goto _start;
}
}
else
{
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_195);
return x_210;
}
}
block_242:
{
uint8_t x_230; 
x_230 = l_String_posOfAux___main___closed__2;
if (x_230 == 0)
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_229, 0);
x_233 = lean_box(0);
lean_inc(x_194);
x_234 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_232, x_194, x_233);
lean_ctor_set(x_229, 0, x_234);
x_235 = l_Lean_CollectFVars_main___main(x_194, x_229);
if (x_228 == 0)
{
x_196 = x_235;
goto block_209;
}
else
{
x_210 = x_235;
goto block_225;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_229, 0);
x_237 = lean_ctor_get(x_229, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_229);
x_238 = lean_box(0);
lean_inc(x_194);
x_239 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_236, x_194, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
x_241 = l_Lean_CollectFVars_main___main(x_194, x_240);
if (x_228 == 0)
{
x_196 = x_241;
goto block_209;
}
else
{
x_210 = x_241;
goto block_225;
}
}
}
else
{
lean_dec(x_194);
if (x_228 == 0)
{
x_196 = x_229;
goto block_209;
}
else
{
x_210 = x_229;
goto block_225;
}
}
}
block_258:
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
x_246 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_244, x_194);
x_247 = l_coeDecidableEq(x_246);
if (x_247 == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_243);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_ctor_get(x_243, 1);
lean_dec(x_249);
x_250 = lean_ctor_get(x_243, 0);
lean_dec(x_250);
x_251 = lean_box(0);
lean_inc(x_194);
x_252 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_244, x_194, x_251);
lean_ctor_set(x_243, 0, x_252);
x_253 = l_Lean_CollectFVars_main___main(x_194, x_243);
if (x_228 == 0)
{
x_196 = x_253;
goto block_209;
}
else
{
x_210 = x_253;
goto block_225;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_243);
x_254 = lean_box(0);
lean_inc(x_194);
x_255 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_244, x_194, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_245);
x_257 = l_Lean_CollectFVars_main___main(x_194, x_256);
if (x_228 == 0)
{
x_196 = x_257;
goto block_209;
}
else
{
x_210 = x_257;
goto block_225;
}
}
}
else
{
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_194);
if (x_228 == 0)
{
x_196 = x_243;
goto block_209;
}
else
{
x_210 = x_243;
goto block_225;
}
}
}
}
case 10:
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_ctor_get(x_1, 1);
lean_inc(x_285);
lean_dec(x_1);
x_286 = l_Lean_Expr_hasFVar(x_285);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = l_String_posOfAux___main___closed__2;
if (x_287 == 0)
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_2);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_2, 0);
x_290 = lean_box(0);
lean_inc(x_285);
x_291 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_289, x_285, x_290);
lean_ctor_set(x_2, 0, x_291);
x_1 = x_285;
goto _start;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_2, 0);
x_294 = lean_ctor_get(x_2, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_2);
x_295 = lean_box(0);
lean_inc(x_285);
x_296 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_293, x_285, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_294);
x_1 = x_285;
x_2 = x_297;
goto _start;
}
}
else
{
lean_dec(x_285);
return x_2;
}
}
else
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_302; 
x_299 = lean_ctor_get(x_2, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_2, 1);
lean_inc(x_300);
x_301 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_299, x_285);
x_302 = l_coeDecidableEq(x_301);
if (x_302 == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_2);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_2, 1);
lean_dec(x_304);
x_305 = lean_ctor_get(x_2, 0);
lean_dec(x_305);
x_306 = lean_box(0);
lean_inc(x_285);
x_307 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_299, x_285, x_306);
lean_ctor_set(x_2, 0, x_307);
x_1 = x_285;
goto _start;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_2);
x_309 = lean_box(0);
lean_inc(x_285);
x_310 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_299, x_285, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_300);
x_1 = x_285;
x_2 = x_311;
goto _start;
}
}
else
{
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_285);
return x_2;
}
}
}
case 11:
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_ctor_get(x_1, 2);
lean_inc(x_313);
lean_dec(x_1);
x_314 = l_Lean_Expr_hasFVar(x_313);
if (x_314 == 0)
{
uint8_t x_315; 
x_315 = l_String_posOfAux___main___closed__2;
if (x_315 == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_2);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_2, 0);
x_318 = lean_box(0);
lean_inc(x_313);
x_319 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_317, x_313, x_318);
lean_ctor_set(x_2, 0, x_319);
x_1 = x_313;
goto _start;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_ctor_get(x_2, 0);
x_322 = lean_ctor_get(x_2, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_2);
x_323 = lean_box(0);
lean_inc(x_313);
x_324 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_321, x_313, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
x_1 = x_313;
x_2 = x_325;
goto _start;
}
}
else
{
lean_dec(x_313);
return x_2;
}
}
else
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_330; 
x_327 = lean_ctor_get(x_2, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_2, 1);
lean_inc(x_328);
x_329 = l_HashMapImp_contains___at_Lean_CollectFVars_visit___spec__7(x_327, x_313);
x_330 = l_coeDecidableEq(x_329);
if (x_330 == 0)
{
uint8_t x_331; 
x_331 = !lean_is_exclusive(x_2);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_2, 1);
lean_dec(x_332);
x_333 = lean_ctor_get(x_2, 0);
lean_dec(x_333);
x_334 = lean_box(0);
lean_inc(x_313);
x_335 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_327, x_313, x_334);
lean_ctor_set(x_2, 0, x_335);
x_1 = x_313;
goto _start;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_2);
x_337 = lean_box(0);
lean_inc(x_313);
x_338 = l_HashMapImp_insert___at_Lean_CollectFVars_visit___spec__1(x_327, x_313, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_328);
x_1 = x_313;
x_2 = x_339;
goto _start;
}
}
else
{
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_313);
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
