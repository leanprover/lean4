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
lean_object* l_mkHashSetImp___rarg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_elem___main___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__2;
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_inhabited___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_CollectFVars_visit___spec__6(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_CollectFVars_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectFVars_State_inhabited___spec__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectFVars_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectFVars_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectFVars_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_CollectFVars_State_inhabited___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
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
uint8_t l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_List_foldl___main___at_Lean_CollectFVars_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___main___at_Lean_CollectFVars_visit___spec__6(x_3, x_6);
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
lean_object* l_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashSetImp_moveEntries___main___at_Lean_CollectFVars_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(x_6, x_2, x_3);
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
x_12 = l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(x_10, x_2, x_3);
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
lean_object* l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_9);
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
x_16 = l_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(x_12, x_14);
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
x_17 = l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(x_9, x_2, x_2);
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
x_25 = l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(x_2, x_24);
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
x_31 = l_HashSetImp_expand___at_Lean_CollectFVars_visit___spec__4(x_27, x_29);
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
x_33 = l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(x_24, x_2, x_2);
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
x_7 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_5, x_2);
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
x_11 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_apply_2(x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_2);
x_13 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_5, x_2);
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
lean_object* l_List_elem___main___at_Lean_CollectFVars_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_CollectFVars_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_replace___main___at_Lean_CollectFVars_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___main___at_Lean_CollectFVars_visit___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Expr_hasFVar(x_13);
x_16 = l_Lean_Expr_hasFVar(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_14);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_17, x_14);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_2, 0);
lean_dec(x_22);
lean_inc(x_14);
x_23 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_17, x_14);
lean_ctor_set(x_2, 0, x_23);
x_1 = x_14;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
lean_inc(x_14);
x_25 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_17, x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_18);
x_1 = x_14;
x_2 = x_26;
goto _start;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
return x_2;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_28, x_13);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_2, 0);
lean_dec(x_33);
lean_inc(x_13);
x_34 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_28, x_13);
lean_ctor_set(x_2, 0, x_34);
x_35 = l_Lean_CollectFVars_main___main(x_13, x_2);
if (x_16 == 0)
{
lean_dec(x_14);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_36, x_14);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_35, 0);
lean_dec(x_41);
lean_inc(x_14);
x_42 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_36, x_14);
lean_ctor_set(x_35, 0, x_42);
x_1 = x_14;
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
lean_inc(x_14);
x_44 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_36, x_14);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_1 = x_14;
x_2 = x_45;
goto _start;
}
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_14);
return x_35;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_inc(x_13);
x_47 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_28, x_13);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_29);
x_49 = l_Lean_CollectFVars_main___main(x_13, x_48);
if (x_16 == 0)
{
lean_dec(x_14);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_50, x_14);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
lean_inc(x_14);
x_54 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_50, x_14);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_1 = x_14;
x_2 = x_55;
goto _start;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_14);
return x_49;
}
}
}
}
else
{
lean_dec(x_13);
if (x_16 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
return x_2;
}
else
{
uint8_t x_57; 
x_57 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_28, x_14);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_2, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_2, 0);
lean_dec(x_60);
lean_inc(x_14);
x_61 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_28, x_14);
lean_ctor_set(x_2, 0, x_61);
x_1 = x_14;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
lean_inc(x_14);
x_63 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_28, x_14);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_29);
x_1 = x_14;
x_2 = x_64;
goto _start;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
return x_2;
}
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc(x_67);
lean_dec(x_1);
x_68 = l_Lean_Expr_hasFVar(x_66);
x_69 = l_Lean_Expr_hasFVar(x_67);
if (x_68 == 0)
{
lean_dec(x_66);
if (x_69 == 0)
{
lean_dec(x_67);
return x_2;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
x_72 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_70, x_67);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_2, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 0);
lean_dec(x_75);
lean_inc(x_67);
x_76 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_70, x_67);
lean_ctor_set(x_2, 0, x_76);
x_1 = x_67;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
lean_inc(x_67);
x_78 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_70, x_67);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
x_1 = x_67;
x_2 = x_79;
goto _start;
}
}
else
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_67);
return x_2;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
x_83 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_81, x_66);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_2);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_2, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_2, 0);
lean_dec(x_86);
lean_inc(x_66);
x_87 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_81, x_66);
lean_ctor_set(x_2, 0, x_87);
x_88 = l_Lean_CollectFVars_main___main(x_66, x_2);
if (x_69 == 0)
{
lean_dec(x_67);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
x_91 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_89, x_67);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
lean_inc(x_67);
x_95 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_89, x_67);
lean_ctor_set(x_88, 0, x_95);
x_1 = x_67;
x_2 = x_88;
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_88);
lean_inc(x_67);
x_97 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_89, x_67);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_90);
x_1 = x_67;
x_2 = x_98;
goto _start;
}
}
else
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_67);
return x_88;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
lean_inc(x_66);
x_100 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_81, x_66);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_82);
x_102 = l_Lean_CollectFVars_main___main(x_66, x_101);
if (x_69 == 0)
{
lean_dec(x_67);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
x_105 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_103, x_67);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
lean_inc(x_67);
x_107 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_103, x_67);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
x_1 = x_67;
x_2 = x_108;
goto _start;
}
else
{
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_67);
return x_102;
}
}
}
}
else
{
lean_dec(x_66);
if (x_69 == 0)
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_67);
return x_2;
}
else
{
uint8_t x_110; 
x_110 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_81, x_67);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_2, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_2, 0);
lean_dec(x_113);
lean_inc(x_67);
x_114 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_81, x_67);
lean_ctor_set(x_2, 0, x_114);
x_1 = x_67;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_2);
lean_inc(x_67);
x_116 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_81, x_67);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_82);
x_1 = x_67;
x_2 = x_117;
goto _start;
}
}
else
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_67);
return x_2;
}
}
}
}
}
case 7:
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_119 = lean_ctor_get(x_1, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_1, 2);
lean_inc(x_120);
lean_dec(x_1);
x_121 = l_Lean_Expr_hasFVar(x_119);
x_122 = l_Lean_Expr_hasFVar(x_120);
if (x_121 == 0)
{
lean_dec(x_119);
if (x_122 == 0)
{
lean_dec(x_120);
return x_2;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_2, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 1);
lean_inc(x_124);
x_125 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_123, x_120);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_2);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_2, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_2, 0);
lean_dec(x_128);
lean_inc(x_120);
x_129 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_123, x_120);
lean_ctor_set(x_2, 0, x_129);
x_1 = x_120;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_2);
lean_inc(x_120);
x_131 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_123, x_120);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
x_1 = x_120;
x_2 = x_132;
goto _start;
}
}
else
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_120);
return x_2;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_2, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
x_136 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_134, x_119);
if (x_136 == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_2, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_2, 0);
lean_dec(x_139);
lean_inc(x_119);
x_140 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_134, x_119);
lean_ctor_set(x_2, 0, x_140);
x_141 = l_Lean_CollectFVars_main___main(x_119, x_2);
if (x_122 == 0)
{
lean_dec(x_120);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
x_144 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_142, x_120);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_141);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_141, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_141, 0);
lean_dec(x_147);
lean_inc(x_120);
x_148 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_142, x_120);
lean_ctor_set(x_141, 0, x_148);
x_1 = x_120;
x_2 = x_141;
goto _start;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_141);
lean_inc(x_120);
x_150 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_142, x_120);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
x_1 = x_120;
x_2 = x_151;
goto _start;
}
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_120);
return x_141;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_2);
lean_inc(x_119);
x_153 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_134, x_119);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_135);
x_155 = l_Lean_CollectFVars_main___main(x_119, x_154);
if (x_122 == 0)
{
lean_dec(x_120);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
x_158 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_156, x_120);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
lean_inc(x_120);
x_160 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_156, x_120);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_157);
x_1 = x_120;
x_2 = x_161;
goto _start;
}
else
{
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_120);
return x_155;
}
}
}
}
else
{
lean_dec(x_119);
if (x_122 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_120);
return x_2;
}
else
{
uint8_t x_163; 
x_163 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_134, x_120);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_2);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_2, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_2, 0);
lean_dec(x_166);
lean_inc(x_120);
x_167 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_134, x_120);
lean_ctor_set(x_2, 0, x_167);
x_1 = x_120;
goto _start;
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_2);
lean_inc(x_120);
x_169 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_134, x_120);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_135);
x_1 = x_120;
x_2 = x_170;
goto _start;
}
}
else
{
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_120);
return x_2;
}
}
}
}
}
case 8:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; lean_object* x_191; 
x_172 = lean_ctor_get(x_1, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_1, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_1, 3);
lean_inc(x_174);
lean_dec(x_1);
x_175 = l_Lean_Expr_hasFVar(x_172);
x_176 = l_Lean_Expr_hasFVar(x_173);
x_177 = l_Lean_Expr_hasFVar(x_174);
if (x_175 == 0)
{
lean_dec(x_172);
if (x_176 == 0)
{
lean_dec(x_173);
x_178 = x_2;
goto block_190;
}
else
{
x_191 = x_2;
goto block_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_2, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 1);
lean_inc(x_232);
x_233 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_231, x_172);
if (x_233 == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_2);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_2, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_2, 0);
lean_dec(x_236);
lean_inc(x_172);
x_237 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_231, x_172);
lean_ctor_set(x_2, 0, x_237);
x_238 = l_Lean_CollectFVars_main___main(x_172, x_2);
if (x_176 == 0)
{
lean_dec(x_173);
x_178 = x_238;
goto block_190;
}
else
{
x_191 = x_238;
goto block_230;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_2);
lean_inc(x_172);
x_239 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_231, x_172);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_232);
x_241 = l_Lean_CollectFVars_main___main(x_172, x_240);
if (x_176 == 0)
{
lean_dec(x_173);
x_178 = x_241;
goto block_190;
}
else
{
x_191 = x_241;
goto block_230;
}
}
}
else
{
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_172);
if (x_176 == 0)
{
lean_dec(x_173);
x_178 = x_2;
goto block_190;
}
else
{
x_191 = x_2;
goto block_230;
}
}
}
block_190:
{
if (x_177 == 0)
{
lean_dec(x_174);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
x_181 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_179, x_174);
if (x_181 == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_178);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_178, 1);
lean_dec(x_183);
x_184 = lean_ctor_get(x_178, 0);
lean_dec(x_184);
lean_inc(x_174);
x_185 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_179, x_174);
lean_ctor_set(x_178, 0, x_185);
x_1 = x_174;
x_2 = x_178;
goto _start;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_178);
lean_inc(x_174);
x_187 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_179, x_174);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
x_1 = x_174;
x_2 = x_188;
goto _start;
}
}
else
{
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_174);
return x_178;
}
}
}
block_230:
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
x_194 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_192, x_173);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_191, 1);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_inc(x_173);
x_198 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_192, x_173);
lean_ctor_set(x_191, 0, x_198);
x_199 = l_Lean_CollectFVars_main___main(x_173, x_191);
if (x_177 == 0)
{
lean_dec(x_174);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
x_202 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_200, x_174);
if (x_202 == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_199);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_199, 1);
lean_dec(x_204);
x_205 = lean_ctor_get(x_199, 0);
lean_dec(x_205);
lean_inc(x_174);
x_206 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_200, x_174);
lean_ctor_set(x_199, 0, x_206);
x_1 = x_174;
x_2 = x_199;
goto _start;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_199);
lean_inc(x_174);
x_208 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_200, x_174);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_201);
x_1 = x_174;
x_2 = x_209;
goto _start;
}
}
else
{
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_174);
return x_199;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_191);
lean_inc(x_173);
x_211 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_192, x_173);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_193);
x_213 = l_Lean_CollectFVars_main___main(x_173, x_212);
if (x_177 == 0)
{
lean_dec(x_174);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
x_216 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_214, x_174);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_217 = x_213;
} else {
 lean_dec_ref(x_213);
 x_217 = lean_box(0);
}
lean_inc(x_174);
x_218 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_214, x_174);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
x_1 = x_174;
x_2 = x_219;
goto _start;
}
else
{
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_174);
return x_213;
}
}
}
}
else
{
lean_dec(x_173);
if (x_177 == 0)
{
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_174);
return x_191;
}
else
{
uint8_t x_221; 
x_221 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_192, x_174);
if (x_221 == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_191);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_191, 1);
lean_dec(x_223);
x_224 = lean_ctor_get(x_191, 0);
lean_dec(x_224);
lean_inc(x_174);
x_225 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_192, x_174);
lean_ctor_set(x_191, 0, x_225);
x_1 = x_174;
x_2 = x_191;
goto _start;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_191);
lean_inc(x_174);
x_227 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_192, x_174);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_193);
x_1 = x_174;
x_2 = x_228;
goto _start;
}
}
else
{
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_174);
return x_191;
}
}
}
}
}
case 10:
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_1, 1);
lean_inc(x_242);
lean_dec(x_1);
x_243 = l_Lean_Expr_hasFVar(x_242);
if (x_243 == 0)
{
lean_dec(x_242);
return x_2;
}
else
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_244 = lean_ctor_get(x_2, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_2, 1);
lean_inc(x_245);
x_246 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_244, x_242);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_2);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_2, 1);
lean_dec(x_248);
x_249 = lean_ctor_get(x_2, 0);
lean_dec(x_249);
lean_inc(x_242);
x_250 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_244, x_242);
lean_ctor_set(x_2, 0, x_250);
x_1 = x_242;
goto _start;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
lean_inc(x_242);
x_252 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_244, x_242);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_245);
x_1 = x_242;
x_2 = x_253;
goto _start;
}
}
else
{
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_242);
return x_2;
}
}
}
case 11:
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_ctor_get(x_1, 2);
lean_inc(x_255);
lean_dec(x_1);
x_256 = l_Lean_Expr_hasFVar(x_255);
if (x_256 == 0)
{
lean_dec(x_255);
return x_2;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_2, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_2, 1);
lean_inc(x_258);
x_259 = l_HashSetImp_contains___at_Lean_CollectFVars_visit___spec__1(x_257, x_255);
if (x_259 == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_2);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_2, 1);
lean_dec(x_261);
x_262 = lean_ctor_get(x_2, 0);
lean_dec(x_262);
lean_inc(x_255);
x_263 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_257, x_255);
lean_ctor_set(x_2, 0, x_263);
x_1 = x_255;
goto _start;
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_2);
lean_inc(x_255);
x_265 = l_HashSetImp_insert___at_Lean_CollectFVars_visit___spec__3(x_257, x_255);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_258);
x_1 = x_255;
x_2 = x_266;
goto _start;
}
}
else
{
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_255);
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
