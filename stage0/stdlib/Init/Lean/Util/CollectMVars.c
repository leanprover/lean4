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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectMVars_main___main(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_mkHashSet___at_Lean_CollectMVars_State_inhabited___spec__1(lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectMVars_State_inhabited___spec__2(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__2;
uint8_t l_coeDecidableEq(uint8_t);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited___closed__1;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__5(lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_CollectMVars_State_inhabited;
lean_object* l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object*, lean_object*);
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
lean_object* l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectMVars_visit___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectMVars_visit___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_10);
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
x_18 = l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__3(x_14, x_16);
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
x_19 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(x_2, x_3, x_10);
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
x_27 = l_AssocList_contains___main___at_Lean_CollectMVars_visit___spec__2(x_2, x_26);
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
x_34 = l_HashMapImp_expand___at_Lean_CollectMVars_visit___spec__3(x_30, x_32);
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
x_36 = l_AssocList_replace___main___at_Lean_CollectMVars_visit___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_CollectMVars_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
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
x_9 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_7, x_2, x_8);
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
x_14 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_11, x_2, x_13);
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
x_19 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_17, x_2);
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
x_25 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_17, x_2, x_24);
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
x_28 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_17, x_2, x_27);
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
lean_object* l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_1, x_2);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_27; uint8_t x_43; uint8_t x_44; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_43 = l_Lean_Expr_hasMVar(x_11);
x_44 = l_Lean_Expr_hasMVar(x_12);
if (x_43 == 0)
{
uint8_t x_45; 
x_45 = l_String_posOfAux___main___closed__2;
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_box(0);
lean_inc(x_11);
x_49 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_47, x_11, x_48);
lean_ctor_set(x_2, 0, x_49);
x_50 = l_Lean_CollectMVars_main___main(x_11, x_2);
if (x_44 == 0)
{
x_13 = x_50;
goto block_26;
}
else
{
x_27 = x_50;
goto block_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_53 = lean_box(0);
lean_inc(x_11);
x_54 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_51, x_11, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = l_Lean_CollectMVars_main___main(x_11, x_55);
if (x_44 == 0)
{
x_13 = x_56;
goto block_26;
}
else
{
x_27 = x_56;
goto block_42;
}
}
}
else
{
lean_dec(x_11);
if (x_44 == 0)
{
x_13 = x_2;
goto block_26;
}
else
{
x_27 = x_2;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_57, x_11);
x_60 = l_coeDecidableEq(x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_2, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_2, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_inc(x_11);
x_65 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_57, x_11, x_64);
lean_ctor_set(x_2, 0, x_65);
x_66 = l_Lean_CollectMVars_main___main(x_11, x_2);
if (x_44 == 0)
{
x_13 = x_66;
goto block_26;
}
else
{
x_27 = x_66;
goto block_42;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
x_67 = lean_box(0);
lean_inc(x_11);
x_68 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_57, x_11, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_58);
x_70 = l_Lean_CollectMVars_main___main(x_11, x_69);
if (x_44 == 0)
{
x_13 = x_70;
goto block_26;
}
else
{
x_27 = x_70;
goto block_42;
}
}
}
else
{
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_11);
if (x_44 == 0)
{
x_13 = x_2;
goto block_26;
}
else
{
x_27 = x_2;
goto block_42;
}
}
}
block_26:
{
uint8_t x_14; 
x_14 = l_String_posOfAux___main___closed__2;
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_box(0);
lean_inc(x_12);
x_18 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_16, x_12, x_17);
lean_ctor_set(x_13, 0, x_18);
x_1 = x_12;
x_2 = x_13;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_box(0);
lean_inc(x_12);
x_23 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_20, x_12, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_1 = x_12;
x_2 = x_24;
goto _start;
}
}
else
{
lean_dec(x_12);
return x_13;
}
}
block_42:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_28, x_12);
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_27, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_inc(x_12);
x_36 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_28, x_12, x_35);
lean_ctor_set(x_27, 0, x_36);
x_1 = x_12;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
x_38 = lean_box(0);
lean_inc(x_12);
x_39 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_28, x_12, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
x_1 = x_12;
x_2 = x_40;
goto _start;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_12);
return x_27;
}
}
}
case 6:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_87; uint8_t x_103; uint8_t x_104; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
lean_dec(x_1);
x_103 = l_Lean_Expr_hasMVar(x_71);
x_104 = l_Lean_Expr_hasMVar(x_72);
if (x_103 == 0)
{
uint8_t x_105; 
x_105 = l_String_posOfAux___main___closed__2;
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_2);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_2, 0);
x_108 = lean_box(0);
lean_inc(x_71);
x_109 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_107, x_71, x_108);
lean_ctor_set(x_2, 0, x_109);
x_110 = l_Lean_CollectMVars_main___main(x_71, x_2);
if (x_104 == 0)
{
x_73 = x_110;
goto block_86;
}
else
{
x_87 = x_110;
goto block_102;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_2, 0);
x_112 = lean_ctor_get(x_2, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_2);
x_113 = lean_box(0);
lean_inc(x_71);
x_114 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_111, x_71, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
x_116 = l_Lean_CollectMVars_main___main(x_71, x_115);
if (x_104 == 0)
{
x_73 = x_116;
goto block_86;
}
else
{
x_87 = x_116;
goto block_102;
}
}
}
else
{
lean_dec(x_71);
if (x_104 == 0)
{
x_73 = x_2;
goto block_86;
}
else
{
x_87 = x_2;
goto block_102;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
x_119 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_117, x_71);
x_120 = l_coeDecidableEq(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_2);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_2, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_2, 0);
lean_dec(x_123);
x_124 = lean_box(0);
lean_inc(x_71);
x_125 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_117, x_71, x_124);
lean_ctor_set(x_2, 0, x_125);
x_126 = l_Lean_CollectMVars_main___main(x_71, x_2);
if (x_104 == 0)
{
x_73 = x_126;
goto block_86;
}
else
{
x_87 = x_126;
goto block_102;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_2);
x_127 = lean_box(0);
lean_inc(x_71);
x_128 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_117, x_71, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_118);
x_130 = l_Lean_CollectMVars_main___main(x_71, x_129);
if (x_104 == 0)
{
x_73 = x_130;
goto block_86;
}
else
{
x_87 = x_130;
goto block_102;
}
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_71);
if (x_104 == 0)
{
x_73 = x_2;
goto block_86;
}
else
{
x_87 = x_2;
goto block_102;
}
}
}
block_86:
{
uint8_t x_74; 
x_74 = l_String_posOfAux___main___closed__2;
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_box(0);
lean_inc(x_72);
x_78 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_76, x_72, x_77);
lean_ctor_set(x_73, 0, x_78);
x_1 = x_72;
x_2 = x_73;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_73, 0);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_73);
x_82 = lean_box(0);
lean_inc(x_72);
x_83 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_80, x_72, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
x_1 = x_72;
x_2 = x_84;
goto _start;
}
}
else
{
lean_dec(x_72);
return x_73;
}
}
block_102:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_88, x_72);
x_91 = l_coeDecidableEq(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_87, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_87, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_inc(x_72);
x_96 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_88, x_72, x_95);
lean_ctor_set(x_87, 0, x_96);
x_1 = x_72;
x_2 = x_87;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_87);
x_98 = lean_box(0);
lean_inc(x_72);
x_99 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_88, x_72, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_89);
x_1 = x_72;
x_2 = x_100;
goto _start;
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_72);
return x_87;
}
}
}
case 7:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_147; uint8_t x_163; uint8_t x_164; 
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
lean_dec(x_1);
x_163 = l_Lean_Expr_hasMVar(x_131);
x_164 = l_Lean_Expr_hasMVar(x_132);
if (x_163 == 0)
{
uint8_t x_165; 
x_165 = l_String_posOfAux___main___closed__2;
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_2);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_2, 0);
x_168 = lean_box(0);
lean_inc(x_131);
x_169 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_167, x_131, x_168);
lean_ctor_set(x_2, 0, x_169);
x_170 = l_Lean_CollectMVars_main___main(x_131, x_2);
if (x_164 == 0)
{
x_133 = x_170;
goto block_146;
}
else
{
x_147 = x_170;
goto block_162;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_2, 0);
x_172 = lean_ctor_get(x_2, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_2);
x_173 = lean_box(0);
lean_inc(x_131);
x_174 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_171, x_131, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
x_176 = l_Lean_CollectMVars_main___main(x_131, x_175);
if (x_164 == 0)
{
x_133 = x_176;
goto block_146;
}
else
{
x_147 = x_176;
goto block_162;
}
}
}
else
{
lean_dec(x_131);
if (x_164 == 0)
{
x_133 = x_2;
goto block_146;
}
else
{
x_147 = x_2;
goto block_162;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_2, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
x_179 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_177, x_131);
x_180 = l_coeDecidableEq(x_179);
if (x_180 == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_2);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_2, 1);
lean_dec(x_182);
x_183 = lean_ctor_get(x_2, 0);
lean_dec(x_183);
x_184 = lean_box(0);
lean_inc(x_131);
x_185 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_177, x_131, x_184);
lean_ctor_set(x_2, 0, x_185);
x_186 = l_Lean_CollectMVars_main___main(x_131, x_2);
if (x_164 == 0)
{
x_133 = x_186;
goto block_146;
}
else
{
x_147 = x_186;
goto block_162;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_2);
x_187 = lean_box(0);
lean_inc(x_131);
x_188 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_177, x_131, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_178);
x_190 = l_Lean_CollectMVars_main___main(x_131, x_189);
if (x_164 == 0)
{
x_133 = x_190;
goto block_146;
}
else
{
x_147 = x_190;
goto block_162;
}
}
}
else
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_131);
if (x_164 == 0)
{
x_133 = x_2;
goto block_146;
}
else
{
x_147 = x_2;
goto block_162;
}
}
}
block_146:
{
uint8_t x_134; 
x_134 = l_String_posOfAux___main___closed__2;
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_133, 0);
x_137 = lean_box(0);
lean_inc(x_132);
x_138 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_136, x_132, x_137);
lean_ctor_set(x_133, 0, x_138);
x_1 = x_132;
x_2 = x_133;
goto _start;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_133, 0);
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_133);
x_142 = lean_box(0);
lean_inc(x_132);
x_143 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_140, x_132, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
x_1 = x_132;
x_2 = x_144;
goto _start;
}
}
else
{
lean_dec(x_132);
return x_133;
}
}
block_162:
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
x_150 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_148, x_132);
x_151 = l_coeDecidableEq(x_150);
if (x_151 == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_147, 1);
lean_dec(x_153);
x_154 = lean_ctor_get(x_147, 0);
lean_dec(x_154);
x_155 = lean_box(0);
lean_inc(x_132);
x_156 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_148, x_132, x_155);
lean_ctor_set(x_147, 0, x_156);
x_1 = x_132;
x_2 = x_147;
goto _start;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_147);
x_158 = lean_box(0);
lean_inc(x_132);
x_159 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_148, x_132, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_149);
x_1 = x_132;
x_2 = x_160;
goto _start;
}
}
else
{
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_132);
return x_147;
}
}
}
case 8:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_208; uint8_t x_224; uint8_t x_225; uint8_t x_226; lean_object* x_227; lean_object* x_241; 
x_191 = lean_ctor_get(x_1, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_1, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_1, 3);
lean_inc(x_193);
lean_dec(x_1);
x_224 = l_Lean_Expr_hasMVar(x_191);
x_225 = l_Lean_Expr_hasMVar(x_192);
x_226 = l_Lean_Expr_hasMVar(x_193);
if (x_224 == 0)
{
uint8_t x_257; 
x_257 = l_String_posOfAux___main___closed__2;
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_2);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_2, 0);
x_260 = lean_box(0);
lean_inc(x_191);
x_261 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_259, x_191, x_260);
lean_ctor_set(x_2, 0, x_261);
x_262 = l_Lean_CollectMVars_main___main(x_191, x_2);
if (x_225 == 0)
{
x_227 = x_262;
goto block_240;
}
else
{
x_241 = x_262;
goto block_256;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_2, 0);
x_264 = lean_ctor_get(x_2, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_2);
x_265 = lean_box(0);
lean_inc(x_191);
x_266 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_263, x_191, x_265);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
x_268 = l_Lean_CollectMVars_main___main(x_191, x_267);
if (x_225 == 0)
{
x_227 = x_268;
goto block_240;
}
else
{
x_241 = x_268;
goto block_256;
}
}
}
else
{
lean_dec(x_191);
if (x_225 == 0)
{
x_227 = x_2;
goto block_240;
}
else
{
x_241 = x_2;
goto block_256;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_2, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_2, 1);
lean_inc(x_270);
x_271 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_269, x_191);
x_272 = l_coeDecidableEq(x_271);
if (x_272 == 0)
{
uint8_t x_273; 
x_273 = !lean_is_exclusive(x_2);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_2, 1);
lean_dec(x_274);
x_275 = lean_ctor_get(x_2, 0);
lean_dec(x_275);
x_276 = lean_box(0);
lean_inc(x_191);
x_277 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_269, x_191, x_276);
lean_ctor_set(x_2, 0, x_277);
x_278 = l_Lean_CollectMVars_main___main(x_191, x_2);
if (x_225 == 0)
{
x_227 = x_278;
goto block_240;
}
else
{
x_241 = x_278;
goto block_256;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_2);
x_279 = lean_box(0);
lean_inc(x_191);
x_280 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_269, x_191, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_270);
x_282 = l_Lean_CollectMVars_main___main(x_191, x_281);
if (x_225 == 0)
{
x_227 = x_282;
goto block_240;
}
else
{
x_241 = x_282;
goto block_256;
}
}
}
else
{
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_191);
if (x_225 == 0)
{
x_227 = x_2;
goto block_240;
}
else
{
x_241 = x_2;
goto block_256;
}
}
}
block_207:
{
uint8_t x_195; 
x_195 = l_String_posOfAux___main___closed__2;
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_194, 0);
x_198 = lean_box(0);
lean_inc(x_193);
x_199 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_197, x_193, x_198);
lean_ctor_set(x_194, 0, x_199);
x_1 = x_193;
x_2 = x_194;
goto _start;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_194, 0);
x_202 = lean_ctor_get(x_194, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_194);
x_203 = lean_box(0);
lean_inc(x_193);
x_204 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_201, x_193, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
x_1 = x_193;
x_2 = x_205;
goto _start;
}
}
else
{
lean_dec(x_193);
return x_194;
}
}
block_223:
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
x_211 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_209, x_193);
x_212 = l_coeDecidableEq(x_211);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_208);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_208, 1);
lean_dec(x_214);
x_215 = lean_ctor_get(x_208, 0);
lean_dec(x_215);
x_216 = lean_box(0);
lean_inc(x_193);
x_217 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_209, x_193, x_216);
lean_ctor_set(x_208, 0, x_217);
x_1 = x_193;
x_2 = x_208;
goto _start;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_208);
x_219 = lean_box(0);
lean_inc(x_193);
x_220 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_209, x_193, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_210);
x_1 = x_193;
x_2 = x_221;
goto _start;
}
}
else
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_193);
return x_208;
}
}
block_240:
{
uint8_t x_228; 
x_228 = l_String_posOfAux___main___closed__2;
if (x_228 == 0)
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_227, 0);
x_231 = lean_box(0);
lean_inc(x_192);
x_232 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_230, x_192, x_231);
lean_ctor_set(x_227, 0, x_232);
x_233 = l_Lean_CollectMVars_main___main(x_192, x_227);
if (x_226 == 0)
{
x_194 = x_233;
goto block_207;
}
else
{
x_208 = x_233;
goto block_223;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_227, 0);
x_235 = lean_ctor_get(x_227, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_227);
x_236 = lean_box(0);
lean_inc(x_192);
x_237 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_234, x_192, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
x_239 = l_Lean_CollectMVars_main___main(x_192, x_238);
if (x_226 == 0)
{
x_194 = x_239;
goto block_207;
}
else
{
x_208 = x_239;
goto block_223;
}
}
}
else
{
lean_dec(x_192);
if (x_226 == 0)
{
x_194 = x_227;
goto block_207;
}
else
{
x_208 = x_227;
goto block_223;
}
}
}
block_256:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
x_244 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_242, x_192);
x_245 = l_coeDecidableEq(x_244);
if (x_245 == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_241);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_241, 1);
lean_dec(x_247);
x_248 = lean_ctor_get(x_241, 0);
lean_dec(x_248);
x_249 = lean_box(0);
lean_inc(x_192);
x_250 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_242, x_192, x_249);
lean_ctor_set(x_241, 0, x_250);
x_251 = l_Lean_CollectMVars_main___main(x_192, x_241);
if (x_226 == 0)
{
x_194 = x_251;
goto block_207;
}
else
{
x_208 = x_251;
goto block_223;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_241);
x_252 = lean_box(0);
lean_inc(x_192);
x_253 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_242, x_192, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_243);
x_255 = l_Lean_CollectMVars_main___main(x_192, x_254);
if (x_226 == 0)
{
x_194 = x_255;
goto block_207;
}
else
{
x_208 = x_255;
goto block_223;
}
}
}
else
{
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_192);
if (x_226 == 0)
{
x_194 = x_241;
goto block_207;
}
else
{
x_208 = x_241;
goto block_223;
}
}
}
}
case 10:
{
lean_object* x_283; uint8_t x_284; 
x_283 = lean_ctor_get(x_1, 1);
lean_inc(x_283);
lean_dec(x_1);
x_284 = l_Lean_Expr_hasMVar(x_283);
if (x_284 == 0)
{
uint8_t x_285; 
x_285 = l_String_posOfAux___main___closed__2;
if (x_285 == 0)
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_2);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_2, 0);
x_288 = lean_box(0);
lean_inc(x_283);
x_289 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_287, x_283, x_288);
lean_ctor_set(x_2, 0, x_289);
x_1 = x_283;
goto _start;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_291 = lean_ctor_get(x_2, 0);
x_292 = lean_ctor_get(x_2, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_2);
x_293 = lean_box(0);
lean_inc(x_283);
x_294 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_291, x_283, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
x_1 = x_283;
x_2 = x_295;
goto _start;
}
}
else
{
lean_dec(x_283);
return x_2;
}
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_300; 
x_297 = lean_ctor_get(x_2, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_2, 1);
lean_inc(x_298);
x_299 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_297, x_283);
x_300 = l_coeDecidableEq(x_299);
if (x_300 == 0)
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_2);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_2, 1);
lean_dec(x_302);
x_303 = lean_ctor_get(x_2, 0);
lean_dec(x_303);
x_304 = lean_box(0);
lean_inc(x_283);
x_305 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_297, x_283, x_304);
lean_ctor_set(x_2, 0, x_305);
x_1 = x_283;
goto _start;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_2);
x_307 = lean_box(0);
lean_inc(x_283);
x_308 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_297, x_283, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_298);
x_1 = x_283;
x_2 = x_309;
goto _start;
}
}
else
{
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_283);
return x_2;
}
}
}
case 11:
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_1, 2);
lean_inc(x_311);
lean_dec(x_1);
x_312 = l_Lean_Expr_hasMVar(x_311);
if (x_312 == 0)
{
uint8_t x_313; 
x_313 = l_String_posOfAux___main___closed__2;
if (x_313 == 0)
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_2);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_2, 0);
x_316 = lean_box(0);
lean_inc(x_311);
x_317 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_315, x_311, x_316);
lean_ctor_set(x_2, 0, x_317);
x_1 = x_311;
goto _start;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_2, 0);
x_320 = lean_ctor_get(x_2, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_2);
x_321 = lean_box(0);
lean_inc(x_311);
x_322 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_319, x_311, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_320);
x_1 = x_311;
x_2 = x_323;
goto _start;
}
}
else
{
lean_dec(x_311);
return x_2;
}
}
else
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_325 = lean_ctor_get(x_2, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_2, 1);
lean_inc(x_326);
x_327 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_325, x_311);
x_328 = l_coeDecidableEq(x_327);
if (x_328 == 0)
{
uint8_t x_329; 
x_329 = !lean_is_exclusive(x_2);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_2, 1);
lean_dec(x_330);
x_331 = lean_ctor_get(x_2, 0);
lean_dec(x_331);
x_332 = lean_box(0);
lean_inc(x_311);
x_333 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_325, x_311, x_332);
lean_ctor_set(x_2, 0, x_333);
x_1 = x_311;
goto _start;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_2);
x_335 = lean_box(0);
lean_inc(x_311);
x_336 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_325, x_311, x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_326);
x_1 = x_311;
x_2 = x_337;
goto _start;
}
}
else
{
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_311);
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
uint8_t x_4; 
x_4 = l_String_posOfAux___main___closed__2;
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_box(0);
lean_inc(x_2);
x_8 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_6, x_2, x_7);
lean_ctor_set(x_1, 0, x_8);
x_9 = l_Lean_CollectMVars_main___main(x_2, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
lean_inc(x_2);
x_13 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_10, x_2, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l_Lean_CollectMVars_main___main(x_2, x_14);
return x_15;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = l_HashMapImp_contains___at_Lean_CollectMVars_visit___spec__7(x_16, x_2);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_inc(x_2);
x_24 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_16, x_2, x_23);
lean_ctor_set(x_1, 0, x_24);
x_25 = l_Lean_CollectMVars_main___main(x_2, x_1);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_26 = lean_box(0);
lean_inc(x_2);
x_27 = l_HashMapImp_insert___at_Lean_CollectMVars_visit___spec__1(x_16, x_2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
x_29 = l_Lean_CollectMVars_main___main(x_2, x_28);
return x_29;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
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
