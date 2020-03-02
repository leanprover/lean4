// Lean compiler output
// Module: Init.Lean.Util.CollectLevelParams
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
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_mkHashSetImp___rarg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
size_t l_Lean_Level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect___main(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__1(lean_object*);
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__3;
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object*, lean_object*, lean_object*);
uint8_t l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited;
lean_object* l_HashSetImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__2;
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_visitExpr___spec__6(lean_object*, lean_object*);
lean_object* l_HashSetImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashSetImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_CollectLevelParams_State_inhabited___closed__1;
x_2 = l_Lean_CollectLevelParams_State_inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_CollectLevelParams_State_inhabited___closed__3;
return x_1;
}
}
uint8_t l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_level_eq(x_1, x_4);
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
uint8_t l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
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
x_15 = l_Lean_Level_hash(x_12);
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
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_3, x_6);
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
lean_object* l_HashSetImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_level_eq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_6, x_2, x_3);
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
x_11 = lean_level_eq(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_10, x_2, x_3);
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
lean_object* l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_2);
x_8 = lean_usize_modn(x_7, x_6);
x_9 = lean_array_uget(x_5, x_8);
x_10 = l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_9);
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
x_16 = l_HashSetImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(x_12, x_14);
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
x_17 = l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_9, x_2, x_2);
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
x_22 = l_Lean_Level_hash(x_2);
x_23 = lean_usize_modn(x_22, x_21);
x_24 = lean_array_uget(x_20, x_23);
x_25 = l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_24);
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
x_31 = l_HashSetImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(x_27, x_29);
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
x_33 = l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_24, x_2, x_2);
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
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasParam(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_inc(x_2);
x_13 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_2);
lean_ctor_set(x_3, 0, x_13);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_inc(x_2);
x_15 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_apply_2(x_1, x_2, x_16);
return x_17;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_CollectLevelParams_collect___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Level_hasParam(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
lean_inc(x_3);
x_13 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3);
lean_ctor_set(x_2, 0, x_13);
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
lean_inc(x_3);
x_15 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_7);
x_1 = x_3;
x_2 = x_16;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_35; uint8_t x_36; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_35 = l_Lean_Level_hasParam(x_18);
x_36 = l_Lean_Level_hasParam(x_19);
if (x_35 == 0)
{
lean_dec(x_18);
if (x_36 == 0)
{
lean_dec(x_19);
return x_2;
}
else
{
x_20 = x_2;
goto block_34;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_37, x_18);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_2, 2);
lean_dec(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
lean_inc(x_18);
x_45 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_37, x_18);
lean_ctor_set(x_2, 0, x_45);
x_46 = l_Lean_CollectLevelParams_collect___main(x_18, x_2);
if (x_36 == 0)
{
lean_dec(x_19);
return x_46;
}
else
{
x_20 = x_46;
goto block_34;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_inc(x_18);
x_47 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_37, x_18);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_39);
x_49 = l_Lean_CollectLevelParams_collect___main(x_18, x_48);
if (x_36 == 0)
{
lean_dec(x_19);
return x_49;
}
else
{
x_20 = x_49;
goto block_34;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_18);
if (x_36 == 0)
{
lean_dec(x_19);
return x_2;
}
else
{
x_20 = x_2;
goto block_34;
}
}
}
block_34:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
x_24 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_21, x_19);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_20, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
lean_inc(x_19);
x_29 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_21, x_19);
lean_ctor_set(x_20, 0, x_29);
x_1 = x_19;
x_2 = x_20;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
lean_inc(x_19);
x_31 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_21, x_19);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
x_1 = x_19;
x_2 = x_32;
goto _start;
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
return x_20;
}
}
}
case 3:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_67; uint8_t x_68; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_67 = l_Lean_Level_hasParam(x_50);
x_68 = l_Lean_Level_hasParam(x_51);
if (x_67 == 0)
{
lean_dec(x_50);
if (x_68 == 0)
{
lean_dec(x_51);
return x_2;
}
else
{
x_52 = x_2;
goto block_66;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
x_72 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_69, x_50);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_2, 2);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_2, 0);
lean_dec(x_76);
lean_inc(x_50);
x_77 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_69, x_50);
lean_ctor_set(x_2, 0, x_77);
x_78 = l_Lean_CollectLevelParams_collect___main(x_50, x_2);
if (x_68 == 0)
{
lean_dec(x_51);
return x_78;
}
else
{
x_52 = x_78;
goto block_66;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
lean_inc(x_50);
x_79 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_69, x_50);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
lean_ctor_set(x_80, 2, x_71);
x_81 = l_Lean_CollectLevelParams_collect___main(x_50, x_80);
if (x_68 == 0)
{
lean_dec(x_51);
return x_81;
}
else
{
x_52 = x_81;
goto block_66;
}
}
}
else
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_50);
if (x_68 == 0)
{
lean_dec(x_51);
return x_2;
}
else
{
x_52 = x_2;
goto block_66;
}
}
}
block_66:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_53, x_51);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_52, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_52, 0);
lean_dec(x_60);
lean_inc(x_51);
x_61 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_53, x_51);
lean_ctor_set(x_52, 0, x_61);
x_1 = x_51;
x_2 = x_52;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_52);
lean_inc(x_51);
x_63 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_53, x_51);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_55);
x_1 = x_51;
x_2 = x_64;
goto _start;
}
}
else
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
return x_52;
}
}
}
case 4:
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_2, 2);
x_85 = lean_array_push(x_84, x_82);
lean_ctor_set(x_2, 2, x_85);
return x_2;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_2, 0);
x_87 = lean_ctor_get(x_2, 1);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_2);
x_89 = lean_array_push(x_88, x_82);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_87);
lean_ctor_set(x_90, 2, x_89);
return x_90;
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
lean_object* l_Lean_CollectLevelParams_collect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectLevelParams_collect___main(x_1, x_2);
return x_3;
}
}
uint8_t l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_visitExpr___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___main___at_Lean_CollectLevelParams_visitExpr___spec__6(x_3, x_6);
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
lean_object* l_HashSetImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashSetImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_6, x_2, x_3);
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
x_12 = l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_10, x_2, x_3);
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
lean_object* l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_9);
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
x_16 = l_HashSetImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_12, x_14);
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
x_17 = l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_9, x_2, x_2);
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
x_25 = l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_24);
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
x_31 = l_HashSetImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_27, x_29);
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
x_33 = l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_24, x_2, x_2);
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
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasLevelParam(x_2);
if (x_4 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
x_8 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_6, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_inc(x_2);
x_13 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_6, x_2);
lean_ctor_set(x_3, 1, x_13);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_inc(x_2);
x_15 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_6, x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_apply_2(x_1, x_2, x_16);
return x_17;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
lean_inc(x_3);
x_15 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3);
lean_ctor_set(x_1, 0, x_15);
x_16 = l_Lean_CollectLevelParams_collect___main(x_3, x_1);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
lean_inc(x_3);
x_18 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_9);
x_20 = l_Lean_CollectLevelParams_collect___main(x_3, x_19);
x_1 = x_20;
x_2 = x_4;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
}
}
}
}
lean_object* l_Lean_CollectLevelParams_main___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Level_hasParam(x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
lean_inc(x_3);
x_13 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3);
lean_ctor_set(x_2, 0, x_13);
x_14 = l_Lean_CollectLevelParams_collect___main(x_3, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_inc(x_3);
x_15 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_7);
x_17 = l_Lean_CollectLevelParams_collect___main(x_3, x_16);
return x_17;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
}
case 4:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(x_2, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_37; uint8_t x_38; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_37 = l_Lean_Expr_hasLevelParam(x_20);
x_38 = l_Lean_Expr_hasLevelParam(x_21);
if (x_37 == 0)
{
lean_dec(x_20);
if (x_38 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
x_22 = x_2;
goto block_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
x_42 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_40, x_20);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_2, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
lean_inc(x_20);
x_47 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_40, x_20);
lean_ctor_set(x_2, 1, x_47);
x_48 = l_Lean_CollectLevelParams_main___main(x_20, x_2);
if (x_38 == 0)
{
lean_dec(x_21);
return x_48;
}
else
{
x_22 = x_48;
goto block_36;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_inc(x_20);
x_49 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_40, x_20);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_41);
x_51 = l_Lean_CollectLevelParams_main___main(x_20, x_50);
if (x_38 == 0)
{
lean_dec(x_21);
return x_51;
}
else
{
x_22 = x_51;
goto block_36;
}
}
}
else
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_20);
if (x_38 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
x_22 = x_2;
goto block_36;
}
}
}
block_36:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_24, x_21);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_inc(x_21);
x_31 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_24, x_21);
lean_ctor_set(x_22, 1, x_31);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
lean_inc(x_21);
x_33 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_24, x_21);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
x_1 = x_21;
x_2 = x_34;
goto _start;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
return x_22;
}
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_69; uint8_t x_70; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 2);
lean_inc(x_53);
lean_dec(x_1);
x_69 = l_Lean_Expr_hasLevelParam(x_52);
x_70 = l_Lean_Expr_hasLevelParam(x_53);
if (x_69 == 0)
{
lean_dec(x_52);
if (x_70 == 0)
{
lean_dec(x_53);
return x_2;
}
else
{
x_54 = x_2;
goto block_68;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 2);
lean_inc(x_73);
x_74 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_72, x_52);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_2, 2);
lean_dec(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_dec(x_77);
x_78 = lean_ctor_get(x_2, 0);
lean_dec(x_78);
lean_inc(x_52);
x_79 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_72, x_52);
lean_ctor_set(x_2, 1, x_79);
x_80 = l_Lean_CollectLevelParams_main___main(x_52, x_2);
if (x_70 == 0)
{
lean_dec(x_53);
return x_80;
}
else
{
x_54 = x_80;
goto block_68;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
lean_inc(x_52);
x_81 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_72, x_52);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_73);
x_83 = l_Lean_CollectLevelParams_main___main(x_52, x_82);
if (x_70 == 0)
{
lean_dec(x_53);
return x_83;
}
else
{
x_54 = x_83;
goto block_68;
}
}
}
else
{
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_52);
if (x_70 == 0)
{
lean_dec(x_53);
return x_2;
}
else
{
x_54 = x_2;
goto block_68;
}
}
}
block_68:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_56, x_53);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_54, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_54, 0);
lean_dec(x_62);
lean_inc(x_53);
x_63 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_56, x_53);
lean_ctor_set(x_54, 1, x_63);
x_1 = x_53;
x_2 = x_54;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
lean_inc(x_53);
x_65 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_56, x_53);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_57);
x_1 = x_53;
x_2 = x_66;
goto _start;
}
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
return x_54;
}
}
}
case 7:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_101; uint8_t x_102; 
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 2);
lean_inc(x_85);
lean_dec(x_1);
x_101 = l_Lean_Expr_hasLevelParam(x_84);
x_102 = l_Lean_Expr_hasLevelParam(x_85);
if (x_101 == 0)
{
lean_dec(x_84);
if (x_102 == 0)
{
lean_dec(x_85);
return x_2;
}
else
{
x_86 = x_2;
goto block_100;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 2);
lean_inc(x_105);
x_106 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_104, x_84);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_2);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_2, 2);
lean_dec(x_108);
x_109 = lean_ctor_get(x_2, 1);
lean_dec(x_109);
x_110 = lean_ctor_get(x_2, 0);
lean_dec(x_110);
lean_inc(x_84);
x_111 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_104, x_84);
lean_ctor_set(x_2, 1, x_111);
x_112 = l_Lean_CollectLevelParams_main___main(x_84, x_2);
if (x_102 == 0)
{
lean_dec(x_85);
return x_112;
}
else
{
x_86 = x_112;
goto block_100;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
lean_inc(x_84);
x_113 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_104, x_84);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_103);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_105);
x_115 = l_Lean_CollectLevelParams_main___main(x_84, x_114);
if (x_102 == 0)
{
lean_dec(x_85);
return x_115;
}
else
{
x_86 = x_115;
goto block_100;
}
}
}
else
{
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_84);
if (x_102 == 0)
{
lean_dec(x_85);
return x_2;
}
else
{
x_86 = x_2;
goto block_100;
}
}
}
block_100:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 2);
lean_inc(x_89);
x_90 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_88, x_85);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_86);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_86, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_86, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_86, 0);
lean_dec(x_94);
lean_inc(x_85);
x_95 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_88, x_85);
lean_ctor_set(x_86, 1, x_95);
x_1 = x_85;
x_2 = x_86;
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_86);
lean_inc(x_85);
x_97 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_88, x_85);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_89);
x_1 = x_85;
x_2 = x_98;
goto _start;
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
return x_86;
}
}
}
case 8:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; 
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_1, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 3);
lean_inc(x_118);
lean_dec(x_1);
x_134 = l_Lean_Expr_hasLevelParam(x_116);
x_135 = l_Lean_Expr_hasLevelParam(x_117);
x_136 = l_Lean_Expr_hasLevelParam(x_118);
if (x_134 == 0)
{
lean_dec(x_116);
if (x_135 == 0)
{
lean_dec(x_117);
if (x_136 == 0)
{
lean_dec(x_118);
return x_2;
}
else
{
x_119 = x_2;
goto block_133;
}
}
else
{
x_137 = x_2;
goto block_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 2);
lean_inc(x_154);
x_155 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_153, x_116);
if (x_155 == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_2);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_2, 2);
lean_dec(x_157);
x_158 = lean_ctor_get(x_2, 1);
lean_dec(x_158);
x_159 = lean_ctor_get(x_2, 0);
lean_dec(x_159);
lean_inc(x_116);
x_160 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_153, x_116);
lean_ctor_set(x_2, 1, x_160);
x_161 = l_Lean_CollectLevelParams_main___main(x_116, x_2);
if (x_135 == 0)
{
lean_dec(x_117);
if (x_136 == 0)
{
lean_dec(x_118);
return x_161;
}
else
{
x_119 = x_161;
goto block_133;
}
}
else
{
x_137 = x_161;
goto block_151;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
lean_inc(x_116);
x_162 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_153, x_116);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_154);
x_164 = l_Lean_CollectLevelParams_main___main(x_116, x_163);
if (x_135 == 0)
{
lean_dec(x_117);
if (x_136 == 0)
{
lean_dec(x_118);
return x_164;
}
else
{
x_119 = x_164;
goto block_133;
}
}
else
{
x_137 = x_164;
goto block_151;
}
}
}
else
{
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_116);
if (x_135 == 0)
{
lean_dec(x_117);
if (x_136 == 0)
{
lean_dec(x_118);
return x_2;
}
else
{
x_119 = x_2;
goto block_133;
}
}
else
{
x_137 = x_2;
goto block_151;
}
}
}
block_133:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 2);
lean_inc(x_122);
x_123 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_121, x_118);
if (x_123 == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_119);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_119, 2);
lean_dec(x_125);
x_126 = lean_ctor_get(x_119, 1);
lean_dec(x_126);
x_127 = lean_ctor_get(x_119, 0);
lean_dec(x_127);
lean_inc(x_118);
x_128 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_121, x_118);
lean_ctor_set(x_119, 1, x_128);
x_1 = x_118;
x_2 = x_119;
goto _start;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_119);
lean_inc(x_118);
x_130 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_121, x_118);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_120);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_122);
x_1 = x_118;
x_2 = x_131;
goto _start;
}
}
else
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
return x_119;
}
}
block_151:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
x_141 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_139, x_117);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_137);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_137, 2);
lean_dec(x_143);
x_144 = lean_ctor_get(x_137, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_137, 0);
lean_dec(x_145);
lean_inc(x_117);
x_146 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_139, x_117);
lean_ctor_set(x_137, 1, x_146);
x_147 = l_Lean_CollectLevelParams_main___main(x_117, x_137);
if (x_136 == 0)
{
lean_dec(x_118);
return x_147;
}
else
{
x_119 = x_147;
goto block_133;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_inc(x_117);
x_148 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_139, x_117);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_138);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_140);
x_150 = l_Lean_CollectLevelParams_main___main(x_117, x_149);
if (x_136 == 0)
{
lean_dec(x_118);
return x_150;
}
else
{
x_119 = x_150;
goto block_133;
}
}
}
else
{
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_117);
if (x_136 == 0)
{
lean_dec(x_118);
return x_137;
}
else
{
x_119 = x_137;
goto block_133;
}
}
}
}
case 10:
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_1, 1);
lean_inc(x_165);
lean_dec(x_1);
x_166 = l_Lean_Expr_hasLevelParam(x_165);
if (x_166 == 0)
{
lean_dec(x_165);
return x_2;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_2, 2);
lean_inc(x_169);
x_170 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_168, x_165);
if (x_170 == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_2);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_2, 2);
lean_dec(x_172);
x_173 = lean_ctor_get(x_2, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_2, 0);
lean_dec(x_174);
lean_inc(x_165);
x_175 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_168, x_165);
lean_ctor_set(x_2, 1, x_175);
x_1 = x_165;
goto _start;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
lean_inc(x_165);
x_177 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_168, x_165);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_167);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_169);
x_1 = x_165;
x_2 = x_178;
goto _start;
}
}
else
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_165);
return x_2;
}
}
}
case 11:
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_ctor_get(x_1, 2);
lean_inc(x_180);
lean_dec(x_1);
x_181 = l_Lean_Expr_hasLevelParam(x_180);
if (x_181 == 0)
{
lean_dec(x_180);
return x_2;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_2, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_2, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
x_185 = l_HashSetImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_183, x_180);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_2);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_2, 2);
lean_dec(x_187);
x_188 = lean_ctor_get(x_2, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_2, 0);
lean_dec(x_189);
lean_inc(x_180);
x_190 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_183, x_180);
lean_ctor_set(x_2, 1, x_190);
x_1 = x_180;
goto _start;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_2);
lean_inc(x_180);
x_192 = l_HashSetImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_183, x_180);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_182);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_184);
x_1 = x_180;
x_2 = x_193;
goto _start;
}
}
else
{
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_180);
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
lean_object* l_Lean_CollectLevelParams_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectLevelParams_main___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_collectLevelParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_CollectLevelParams_main___main(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_CollectLevelParams(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_CollectLevelParams_State_inhabited___closed__1 = _init_l_Lean_CollectLevelParams_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_CollectLevelParams_State_inhabited___closed__1);
l_Lean_CollectLevelParams_State_inhabited___closed__2 = _init_l_Lean_CollectLevelParams_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_CollectLevelParams_State_inhabited___closed__2);
l_Lean_CollectLevelParams_State_inhabited___closed__3 = _init_l_Lean_CollectLevelParams_State_inhabited___closed__3();
lean_mark_persistent(l_Lean_CollectLevelParams_State_inhabited___closed__3);
l_Lean_CollectLevelParams_State_inhabited = _init_l_Lean_CollectLevelParams_State_inhabited();
lean_mark_persistent(l_Lean_CollectLevelParams_State_inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
