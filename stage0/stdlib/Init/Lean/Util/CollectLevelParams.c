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
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
size_t l_Lean_Level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect___main(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitExpr___spec__6(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__3(lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__2(lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__1(lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__3;
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__1;
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__4(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited;
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__2;
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_CollectLevelParams_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
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
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_level_eq(x_4, x_1);
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
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Level_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_hash(x_4);
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
x_16 = l_Lean_Level_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_level_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_1, x_2, x_7);
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
x_13 = lean_level_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Level_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_2, x_3, x_10);
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
x_23 = l_Lean_Level_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
x_8 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_inc(x_2);
x_14 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_2, x_13);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_apply_2(x_1, x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_16 = lean_box(0);
lean_inc(x_2);
x_17 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_2, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
x_19 = lean_apply_2(x_1, x_2, x_18);
return x_19;
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
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
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
x_8 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_3);
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
x_13 = lean_box(0);
lean_inc(x_3);
x_14 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3, x_13);
lean_ctor_set(x_2, 0, x_14);
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_16 = lean_box(0);
lean_inc(x_3);
x_17 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
x_1 = x_3;
x_2 = x_18;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_39; uint8_t x_40; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_39 = l_Lean_Level_hasParam(x_20);
x_40 = l_Lean_Level_hasParam(x_21);
if (x_39 == 0)
{
lean_dec(x_20);
if (x_40 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
x_22 = x_2;
goto block_38;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_41, x_20);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_2, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_inc(x_20);
x_50 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_41, x_20, x_49);
lean_ctor_set(x_2, 0, x_50);
x_51 = l_Lean_CollectLevelParams_collect___main(x_20, x_2);
if (x_40 == 0)
{
lean_dec(x_21);
return x_51;
}
else
{
x_22 = x_51;
goto block_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_52 = lean_box(0);
lean_inc(x_20);
x_53 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_41, x_20, x_52);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
x_55 = l_Lean_CollectLevelParams_collect___main(x_20, x_54);
if (x_40 == 0)
{
lean_dec(x_21);
return x_55;
}
else
{
x_22 = x_55;
goto block_38;
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_20);
if (x_40 == 0)
{
lean_dec(x_21);
return x_2;
}
else
{
x_22 = x_2;
goto block_38;
}
}
}
block_38:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_23, x_21);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_22, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_inc(x_21);
x_32 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_23, x_21, x_31);
lean_ctor_set(x_22, 0, x_32);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = lean_box(0);
lean_inc(x_21);
x_35 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_23, x_21, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
x_1 = x_21;
x_2 = x_36;
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
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_75; uint8_t x_76; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_75 = l_Lean_Level_hasParam(x_56);
x_76 = l_Lean_Level_hasParam(x_57);
if (x_75 == 0)
{
lean_dec(x_56);
if (x_76 == 0)
{
lean_dec(x_57);
return x_2;
}
else
{
x_58 = x_2;
goto block_74;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
x_80 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_77, x_56);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_2);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_2, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 1);
lean_dec(x_83);
x_84 = lean_ctor_get(x_2, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_inc(x_56);
x_86 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_77, x_56, x_85);
lean_ctor_set(x_2, 0, x_86);
x_87 = l_Lean_CollectLevelParams_collect___main(x_56, x_2);
if (x_76 == 0)
{
lean_dec(x_57);
return x_87;
}
else
{
x_58 = x_87;
goto block_74;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
x_88 = lean_box(0);
lean_inc(x_56);
x_89 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_77, x_56, x_88);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
lean_ctor_set(x_90, 2, x_79);
x_91 = l_Lean_CollectLevelParams_collect___main(x_56, x_90);
if (x_76 == 0)
{
lean_dec(x_57);
return x_91;
}
else
{
x_58 = x_91;
goto block_74;
}
}
}
else
{
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_56);
if (x_76 == 0)
{
lean_dec(x_57);
return x_2;
}
else
{
x_58 = x_2;
goto block_74;
}
}
}
block_74:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_61);
x_62 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_59, x_57);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_58, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_58, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_inc(x_57);
x_68 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_59, x_57, x_67);
lean_ctor_set(x_58, 0, x_68);
x_1 = x_57;
x_2 = x_58;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_58);
x_70 = lean_box(0);
lean_inc(x_57);
x_71 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_59, x_57, x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_60);
lean_ctor_set(x_72, 2, x_61);
x_1 = x_57;
x_2 = x_72;
goto _start;
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
return x_58;
}
}
}
case 4:
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_1, 0);
lean_inc(x_92);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_2);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_2, 2);
x_95 = lean_array_push(x_94, x_92);
lean_ctor_set(x_2, 2, x_95);
return x_2;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_2, 0);
x_97 = lean_ctor_get(x_2, 1);
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_2);
x_99 = lean_array_push(x_98, x_92);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_99);
return x_100;
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
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitExpr___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitExpr___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_2, x_3, x_10);
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
x_26 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
x_8 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_6, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_inc(x_2);
x_14 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_6, x_2, x_13);
lean_ctor_set(x_3, 1, x_14);
x_15 = lean_apply_2(x_1, x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_16 = lean_box(0);
lean_inc(x_2);
x_17 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_6, x_2, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_7);
x_19 = lean_apply_2(x_1, x_2, x_18);
return x_19;
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
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
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
x_10 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_inc(x_3);
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_15);
lean_ctor_set(x_1, 0, x_16);
x_17 = l_Lean_CollectLevelParams_collect___main(x_3, x_1);
x_1 = x_17;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = lean_box(0);
lean_inc(x_3);
x_20 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set(x_21, 2, x_9);
x_22 = l_Lean_CollectLevelParams_collect___main(x_3, x_21);
x_1 = x_22;
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
x_8 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_5, x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_inc(x_3);
x_14 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = l_Lean_CollectLevelParams_collect___main(x_3, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_box(0);
lean_inc(x_3);
x_17 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_5, x_3, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 2, x_7);
x_19 = l_Lean_CollectLevelParams_collect___main(x_3, x_18);
return x_19;
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(x_2, x_20);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_41; uint8_t x_42; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_41 = l_Lean_Expr_hasLevelParam(x_22);
x_42 = l_Lean_Expr_hasLevelParam(x_23);
if (x_41 == 0)
{
lean_dec(x_22);
if (x_42 == 0)
{
lean_dec(x_23);
return x_2;
}
else
{
x_24 = x_2;
goto block_40;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
x_46 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_44, x_22);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_2, 2);
lean_dec(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_inc(x_22);
x_52 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_44, x_22, x_51);
lean_ctor_set(x_2, 1, x_52);
x_53 = l_Lean_CollectLevelParams_main___main(x_22, x_2);
if (x_42 == 0)
{
lean_dec(x_23);
return x_53;
}
else
{
x_24 = x_53;
goto block_40;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_2);
x_54 = lean_box(0);
lean_inc(x_22);
x_55 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_44, x_22, x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_45);
x_57 = l_Lean_CollectLevelParams_main___main(x_22, x_56);
if (x_42 == 0)
{
lean_dec(x_23);
return x_57;
}
else
{
x_24 = x_57;
goto block_40;
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_22);
if (x_42 == 0)
{
lean_dec(x_23);
return x_2;
}
else
{
x_24 = x_2;
goto block_40;
}
}
}
block_40:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 2);
lean_inc(x_27);
x_28 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_26, x_23);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_24, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_inc(x_23);
x_34 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_26, x_23, x_33);
lean_ctor_set(x_24, 1, x_34);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
x_36 = lean_box(0);
lean_inc(x_23);
x_37 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_26, x_23, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_27);
x_1 = x_23;
x_2 = x_38;
goto _start;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
return x_24;
}
}
}
case 6:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_77; uint8_t x_78; 
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
lean_dec(x_1);
x_77 = l_Lean_Expr_hasLevelParam(x_58);
x_78 = l_Lean_Expr_hasLevelParam(x_59);
if (x_77 == 0)
{
lean_dec(x_58);
if (x_78 == 0)
{
lean_dec(x_59);
return x_2;
}
else
{
x_60 = x_2;
goto block_76;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_80, x_58);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_2);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_2, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_2, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_inc(x_58);
x_88 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_80, x_58, x_87);
lean_ctor_set(x_2, 1, x_88);
x_89 = l_Lean_CollectLevelParams_main___main(x_58, x_2);
if (x_78 == 0)
{
lean_dec(x_59);
return x_89;
}
else
{
x_60 = x_89;
goto block_76;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_90 = lean_box(0);
lean_inc(x_58);
x_91 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_80, x_58, x_90);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_79);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_81);
x_93 = l_Lean_CollectLevelParams_main___main(x_58, x_92);
if (x_78 == 0)
{
lean_dec(x_59);
return x_93;
}
else
{
x_60 = x_93;
goto block_76;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_58);
if (x_78 == 0)
{
lean_dec(x_59);
return x_2;
}
else
{
x_60 = x_2;
goto block_76;
}
}
}
block_76:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_62, x_59);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_60, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_60, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_inc(x_59);
x_70 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_62, x_59, x_69);
lean_ctor_set(x_60, 1, x_70);
x_1 = x_59;
x_2 = x_60;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_60);
x_72 = lean_box(0);
lean_inc(x_59);
x_73 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_62, x_59, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_61);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_63);
x_1 = x_59;
x_2 = x_74;
goto _start;
}
}
else
{
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
return x_60;
}
}
}
case 7:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_113; uint8_t x_114; 
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_1, 2);
lean_inc(x_95);
lean_dec(x_1);
x_113 = l_Lean_Expr_hasLevelParam(x_94);
x_114 = l_Lean_Expr_hasLevelParam(x_95);
if (x_113 == 0)
{
lean_dec(x_94);
if (x_114 == 0)
{
lean_dec(x_95);
return x_2;
}
else
{
x_96 = x_2;
goto block_112;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_2, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_2, 2);
lean_inc(x_117);
x_118 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_116, x_94);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_2);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_2, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_2, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_2, 0);
lean_dec(x_122);
x_123 = lean_box(0);
lean_inc(x_94);
x_124 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_116, x_94, x_123);
lean_ctor_set(x_2, 1, x_124);
x_125 = l_Lean_CollectLevelParams_main___main(x_94, x_2);
if (x_114 == 0)
{
lean_dec(x_95);
return x_125;
}
else
{
x_96 = x_125;
goto block_112;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_2);
x_126 = lean_box(0);
lean_inc(x_94);
x_127 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_116, x_94, x_126);
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_115);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_117);
x_129 = l_Lean_CollectLevelParams_main___main(x_94, x_128);
if (x_114 == 0)
{
lean_dec(x_95);
return x_129;
}
else
{
x_96 = x_129;
goto block_112;
}
}
}
else
{
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_94);
if (x_114 == 0)
{
lean_dec(x_95);
return x_2;
}
else
{
x_96 = x_2;
goto block_112;
}
}
}
block_112:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 2);
lean_inc(x_99);
x_100 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_98, x_95);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_96, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_96, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_inc(x_95);
x_106 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_98, x_95, x_105);
lean_ctor_set(x_96, 1, x_106);
x_1 = x_95;
x_2 = x_96;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_96);
x_108 = lean_box(0);
lean_inc(x_95);
x_109 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_98, x_95, x_108);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_99);
x_1 = x_95;
x_2 = x_110;
goto _start;
}
}
else
{
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
return x_96;
}
}
}
case 8:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; 
x_130 = lean_ctor_get(x_1, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 3);
lean_inc(x_132);
lean_dec(x_1);
x_150 = l_Lean_Expr_hasLevelParam(x_130);
x_151 = l_Lean_Expr_hasLevelParam(x_131);
x_152 = l_Lean_Expr_hasLevelParam(x_132);
if (x_150 == 0)
{
lean_dec(x_130);
if (x_151 == 0)
{
lean_dec(x_131);
if (x_152 == 0)
{
lean_dec(x_132);
return x_2;
}
else
{
x_133 = x_2;
goto block_149;
}
}
else
{
x_153 = x_2;
goto block_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_2, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 2);
lean_inc(x_172);
x_173 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_171, x_130);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_2);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_2, 2);
lean_dec(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_dec(x_176);
x_177 = lean_ctor_get(x_2, 0);
lean_dec(x_177);
x_178 = lean_box(0);
lean_inc(x_130);
x_179 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_171, x_130, x_178);
lean_ctor_set(x_2, 1, x_179);
x_180 = l_Lean_CollectLevelParams_main___main(x_130, x_2);
if (x_151 == 0)
{
lean_dec(x_131);
if (x_152 == 0)
{
lean_dec(x_132);
return x_180;
}
else
{
x_133 = x_180;
goto block_149;
}
}
else
{
x_153 = x_180;
goto block_169;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_2);
x_181 = lean_box(0);
lean_inc(x_130);
x_182 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_171, x_130, x_181);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_170);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_172);
x_184 = l_Lean_CollectLevelParams_main___main(x_130, x_183);
if (x_151 == 0)
{
lean_dec(x_131);
if (x_152 == 0)
{
lean_dec(x_132);
return x_184;
}
else
{
x_133 = x_184;
goto block_149;
}
}
else
{
x_153 = x_184;
goto block_169;
}
}
}
else
{
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_130);
if (x_151 == 0)
{
lean_dec(x_131);
if (x_152 == 0)
{
lean_dec(x_132);
return x_2;
}
else
{
x_133 = x_2;
goto block_149;
}
}
else
{
x_153 = x_2;
goto block_169;
}
}
}
block_149:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 2);
lean_inc(x_136);
x_137 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_135, x_132);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_133);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_133, 2);
lean_dec(x_139);
x_140 = lean_ctor_get(x_133, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_133, 0);
lean_dec(x_141);
x_142 = lean_box(0);
lean_inc(x_132);
x_143 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_135, x_132, x_142);
lean_ctor_set(x_133, 1, x_143);
x_1 = x_132;
x_2 = x_133;
goto _start;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
x_145 = lean_box(0);
lean_inc(x_132);
x_146 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_135, x_132, x_145);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_134);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_136);
x_1 = x_132;
x_2 = x_147;
goto _start;
}
}
else
{
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
return x_133;
}
}
block_169:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 2);
lean_inc(x_156);
x_157 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_155, x_131);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_153);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_153, 2);
lean_dec(x_159);
x_160 = lean_ctor_get(x_153, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_153, 0);
lean_dec(x_161);
x_162 = lean_box(0);
lean_inc(x_131);
x_163 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_155, x_131, x_162);
lean_ctor_set(x_153, 1, x_163);
x_164 = l_Lean_CollectLevelParams_main___main(x_131, x_153);
if (x_152 == 0)
{
lean_dec(x_132);
return x_164;
}
else
{
x_133 = x_164;
goto block_149;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_153);
x_165 = lean_box(0);
lean_inc(x_131);
x_166 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_155, x_131, x_165);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_154);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_156);
x_168 = l_Lean_CollectLevelParams_main___main(x_131, x_167);
if (x_152 == 0)
{
lean_dec(x_132);
return x_168;
}
else
{
x_133 = x_168;
goto block_149;
}
}
}
else
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_131);
if (x_152 == 0)
{
lean_dec(x_132);
return x_153;
}
else
{
x_133 = x_153;
goto block_149;
}
}
}
}
case 10:
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_1, 1);
lean_inc(x_185);
lean_dec(x_1);
x_186 = l_Lean_Expr_hasLevelParam(x_185);
if (x_186 == 0)
{
lean_dec(x_185);
return x_2;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_2, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 2);
lean_inc(x_189);
x_190 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_188, x_185);
if (x_190 == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_2);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_2, 2);
lean_dec(x_192);
x_193 = lean_ctor_get(x_2, 1);
lean_dec(x_193);
x_194 = lean_ctor_get(x_2, 0);
lean_dec(x_194);
x_195 = lean_box(0);
lean_inc(x_185);
x_196 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_188, x_185, x_195);
lean_ctor_set(x_2, 1, x_196);
x_1 = x_185;
goto _start;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_2);
x_198 = lean_box(0);
lean_inc(x_185);
x_199 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_188, x_185, x_198);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_187);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_189);
x_1 = x_185;
x_2 = x_200;
goto _start;
}
}
else
{
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_185);
return x_2;
}
}
}
case 11:
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_1, 2);
lean_inc(x_202);
lean_dec(x_1);
x_203 = l_Lean_Expr_hasLevelParam(x_202);
if (x_203 == 0)
{
lean_dec(x_202);
return x_2;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_2, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_2, 2);
lean_inc(x_206);
x_207 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_205, x_202);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_2);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_2, 2);
lean_dec(x_209);
x_210 = lean_ctor_get(x_2, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_2, 0);
lean_dec(x_211);
x_212 = lean_box(0);
lean_inc(x_202);
x_213 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_205, x_202, x_212);
lean_ctor_set(x_2, 1, x_213);
x_1 = x_202;
goto _start;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_2);
x_215 = lean_box(0);
lean_inc(x_202);
x_216 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_205, x_202, x_215);
x_217 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_217, 0, x_204);
lean_ctor_set(x_217, 1, x_216);
lean_ctor_set(x_217, 2, x_206);
x_1 = x_202;
x_2 = x_217;
goto _start;
}
}
else
{
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_202);
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
