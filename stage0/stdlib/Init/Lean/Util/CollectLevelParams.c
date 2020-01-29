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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
size_t l_Lean_Level_hash(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitExpr___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect___main(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitExpr___spec__6(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__3(lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__2(lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_mkHashSet___at_Lean_CollectLevelParams_State_inhabited___spec__1(lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__3;
lean_object* l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__1;
lean_object* l_mkHashMap___at_Lean_CollectLevelParams_State_inhabited___spec__4(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_State_inhabited;
lean_object* l_Lean_CollectLevelParams_State_inhabited___closed__2;
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object*, lean_object*, lean_object*);
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
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Level_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_10);
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
x_18 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__3(x_14, x_16);
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
x_19 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_2, x_3, x_10);
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
x_24 = l_Lean_Level_hash(x_2);
x_25 = lean_usize_modn(x_24, x_23);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(x_2, x_26);
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
x_34 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__3(x_30, x_32);
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
x_36 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitLevel___spec__6(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Level_hasParam(x_2);
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
x_9 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_2, x_8);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_box(0);
lean_inc(x_2);
x_15 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_11, x_2, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
x_17 = lean_apply_2(x_1, x_2, x_16);
return x_17;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
x_21 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_18, x_2);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_3, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_inc(x_2);
x_28 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_2, x_27);
lean_ctor_set(x_3, 0, x_28);
x_29 = lean_apply_2(x_1, x_2, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_30 = lean_box(0);
lean_inc(x_2);
x_31 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_2, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
x_33 = lean_apply_2(x_1, x_2, x_32);
return x_33;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
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
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_1, x_2);
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
uint8_t x_5; 
x_5 = l_String_posOfAux___main___closed__2;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3, x_8);
lean_ctor_set(x_2, 0, x_9);
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_11, x_3, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
x_1 = x_3;
x_2 = x_16;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_18, x_3);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_inc(x_3);
x_28 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_3, x_27);
lean_ctor_set(x_2, 0, x_28);
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_box(0);
lean_inc(x_3);
x_31 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_3, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
x_1 = x_3;
x_2 = x_32;
goto _start;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
return x_2;
}
}
}
case 2:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_51; uint8_t x_69; uint8_t x_70; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_69 = l_Lean_Level_hasParam(x_34);
x_70 = l_Lean_Level_hasParam(x_35);
if (x_69 == 0)
{
uint8_t x_71; 
x_71 = l_String_posOfAux___main___closed__2;
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_box(0);
lean_inc(x_34);
x_75 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_73, x_34, x_74);
lean_ctor_set(x_2, 0, x_75);
x_76 = l_Lean_CollectLevelParams_collect___main(x_34, x_2);
if (x_70 == 0)
{
x_36 = x_76;
goto block_50;
}
else
{
x_51 = x_76;
goto block_68;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_2);
x_80 = lean_box(0);
lean_inc(x_34);
x_81 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_77, x_34, x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
x_83 = l_Lean_CollectLevelParams_collect___main(x_34, x_82);
if (x_70 == 0)
{
x_36 = x_83;
goto block_50;
}
else
{
x_51 = x_83;
goto block_68;
}
}
}
else
{
lean_dec(x_34);
if (x_70 == 0)
{
x_36 = x_2;
goto block_50;
}
else
{
x_51 = x_2;
goto block_68;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
x_87 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_84, x_34);
x_88 = l_coeDecidableEq(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_2);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_2, 2);
lean_dec(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_2, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_inc(x_34);
x_94 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_84, x_34, x_93);
lean_ctor_set(x_2, 0, x_94);
x_95 = l_Lean_CollectLevelParams_collect___main(x_34, x_2);
if (x_70 == 0)
{
x_36 = x_95;
goto block_50;
}
else
{
x_51 = x_95;
goto block_68;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_96 = lean_box(0);
lean_inc(x_34);
x_97 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_84, x_34, x_96);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_85);
lean_ctor_set(x_98, 2, x_86);
x_99 = l_Lean_CollectLevelParams_collect___main(x_34, x_98);
if (x_70 == 0)
{
x_36 = x_99;
goto block_50;
}
else
{
x_51 = x_99;
goto block_68;
}
}
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_34);
if (x_70 == 0)
{
x_36 = x_2;
goto block_50;
}
else
{
x_51 = x_2;
goto block_68;
}
}
}
block_50:
{
uint8_t x_37; 
x_37 = l_String_posOfAux___main___closed__2;
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_box(0);
lean_inc(x_35);
x_41 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_39, x_35, x_40);
lean_ctor_set(x_36, 0, x_41);
x_1 = x_35;
x_2 = x_36;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_46 = lean_box(0);
lean_inc(x_35);
x_47 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_43, x_35, x_46);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
x_1 = x_35;
x_2 = x_48;
goto _start;
}
}
else
{
lean_dec(x_35);
return x_36;
}
}
block_68:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 2);
lean_inc(x_54);
x_55 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_52, x_35);
x_56 = l_coeDecidableEq(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_51, 2);
lean_dec(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_dec(x_59);
x_60 = lean_ctor_get(x_51, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_inc(x_35);
x_62 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_52, x_35, x_61);
lean_ctor_set(x_51, 0, x_62);
x_1 = x_35;
x_2 = x_51;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
x_64 = lean_box(0);
lean_inc(x_35);
x_65 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_52, x_35, x_64);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_54);
x_1 = x_35;
x_2 = x_66;
goto _start;
}
}
else
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_35);
return x_51;
}
}
}
case 3:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_117; uint8_t x_135; uint8_t x_136; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec(x_1);
x_135 = l_Lean_Level_hasParam(x_100);
x_136 = l_Lean_Level_hasParam(x_101);
if (x_135 == 0)
{
uint8_t x_137; 
x_137 = l_String_posOfAux___main___closed__2;
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_2);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_2, 0);
x_140 = lean_box(0);
lean_inc(x_100);
x_141 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_139, x_100, x_140);
lean_ctor_set(x_2, 0, x_141);
x_142 = l_Lean_CollectLevelParams_collect___main(x_100, x_2);
if (x_136 == 0)
{
x_102 = x_142;
goto block_116;
}
else
{
x_117 = x_142;
goto block_134;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_2, 0);
x_144 = lean_ctor_get(x_2, 1);
x_145 = lean_ctor_get(x_2, 2);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_2);
x_146 = lean_box(0);
lean_inc(x_100);
x_147 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_143, x_100, x_146);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set(x_148, 2, x_145);
x_149 = l_Lean_CollectLevelParams_collect___main(x_100, x_148);
if (x_136 == 0)
{
x_102 = x_149;
goto block_116;
}
else
{
x_117 = x_149;
goto block_134;
}
}
}
else
{
lean_dec(x_100);
if (x_136 == 0)
{
x_102 = x_2;
goto block_116;
}
else
{
x_117 = x_2;
goto block_134;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 2);
lean_inc(x_152);
x_153 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_150, x_100);
x_154 = l_coeDecidableEq(x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_2);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_ctor_get(x_2, 2);
lean_dec(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_dec(x_157);
x_158 = lean_ctor_get(x_2, 0);
lean_dec(x_158);
x_159 = lean_box(0);
lean_inc(x_100);
x_160 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_150, x_100, x_159);
lean_ctor_set(x_2, 0, x_160);
x_161 = l_Lean_CollectLevelParams_collect___main(x_100, x_2);
if (x_136 == 0)
{
x_102 = x_161;
goto block_116;
}
else
{
x_117 = x_161;
goto block_134;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_2);
x_162 = lean_box(0);
lean_inc(x_100);
x_163 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_150, x_100, x_162);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_151);
lean_ctor_set(x_164, 2, x_152);
x_165 = l_Lean_CollectLevelParams_collect___main(x_100, x_164);
if (x_136 == 0)
{
x_102 = x_165;
goto block_116;
}
else
{
x_117 = x_165;
goto block_134;
}
}
}
else
{
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_100);
if (x_136 == 0)
{
x_102 = x_2;
goto block_116;
}
else
{
x_117 = x_2;
goto block_134;
}
}
}
block_116:
{
uint8_t x_103; 
x_103 = l_String_posOfAux___main___closed__2;
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_102, 0);
x_106 = lean_box(0);
lean_inc(x_101);
x_107 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_105, x_101, x_106);
lean_ctor_set(x_102, 0, x_107);
x_1 = x_101;
x_2 = x_102;
goto _start;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_102, 0);
x_110 = lean_ctor_get(x_102, 1);
x_111 = lean_ctor_get(x_102, 2);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_102);
x_112 = lean_box(0);
lean_inc(x_101);
x_113 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_109, x_101, x_112);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 2, x_111);
x_1 = x_101;
x_2 = x_114;
goto _start;
}
}
else
{
lean_dec(x_101);
return x_102;
}
}
block_134:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
x_121 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_118, x_101);
x_122 = l_coeDecidableEq(x_121);
if (x_122 == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_117);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_117, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_117, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_117, 0);
lean_dec(x_126);
x_127 = lean_box(0);
lean_inc(x_101);
x_128 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_118, x_101, x_127);
lean_ctor_set(x_117, 0, x_128);
x_1 = x_101;
x_2 = x_117;
goto _start;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_117);
x_130 = lean_box(0);
lean_inc(x_101);
x_131 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_118, x_101, x_130);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_119);
lean_ctor_set(x_132, 2, x_120);
x_1 = x_101;
x_2 = x_132;
goto _start;
}
}
else
{
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_101);
return x_117;
}
}
}
case 4:
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_2);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_2, 2);
x_169 = lean_array_push(x_168, x_166);
lean_ctor_set(x_2, 2, x_169);
return x_2;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_2, 0);
x_171 = lean_ctor_get(x_2, 1);
x_172 = lean_ctor_get(x_2, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_2);
x_173 = lean_array_push(x_172, x_166);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_170);
lean_ctor_set(x_174, 1, x_171);
lean_ctor_set(x_174, 2, x_173);
return x_174;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_10);
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
x_18 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_14, x_16);
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
x_19 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_2, x_3, x_10);
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
x_27 = l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2(x_2, x_26);
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
x_34 = l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(x_30, x_32);
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
x_36 = l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
uint8_t x_5; 
x_5 = l_String_posOfAux___main___closed__2;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_7, x_2);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_inc(x_2);
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_7, x_2, x_15);
lean_ctor_set(x_3, 1, x_16);
x_17 = lean_apply_2(x_1, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_7, x_2, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_8);
x_21 = lean_apply_2(x_1, x_2, x_20);
return x_21;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
uint8_t x_22; 
x_22 = l_String_posOfAux___main___closed__1;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_24, x_2);
x_27 = l_coeDecidableEq(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_3, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_3, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_inc(x_2);
x_33 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_24, x_2, x_32);
lean_ctor_set(x_3, 1, x_33);
x_34 = lean_apply_2(x_1, x_2, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_35 = lean_box(0);
lean_inc(x_2);
x_36 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_24, x_2, x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_25);
x_38 = lean_apply_2(x_1, x_2, x_37);
return x_38;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
else
{
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__2;
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_box(0);
lean_inc(x_3);
x_10 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_8, x_3, x_9);
lean_ctor_set(x_1, 0, x_10);
x_11 = l_Lean_CollectLevelParams_collect___main(x_3, x_1);
x_1 = x_11;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_16 = lean_box(0);
lean_inc(x_3);
x_17 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_13, x_3, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
x_19 = l_Lean_CollectLevelParams_collect___main(x_3, x_18);
x_1 = x_19;
x_2 = x_4;
goto _start;
}
}
else
{
lean_dec(x_3);
x_2 = x_4;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
x_25 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_22, x_3);
x_26 = l_coeDecidableEq(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_inc(x_3);
x_32 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_22, x_3, x_31);
lean_ctor_set(x_1, 0, x_32);
x_33 = l_Lean_CollectLevelParams_collect___main(x_3, x_1);
x_1 = x_33;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_35 = lean_box(0);
lean_inc(x_3);
x_36 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_22, x_3, x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
x_38 = l_Lean_CollectLevelParams_collect___main(x_3, x_37);
x_1 = x_38;
x_2 = x_4;
goto _start;
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
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
uint8_t x_5; 
x_5 = l_String_posOfAux___main___closed__2;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_box(0);
lean_inc(x_3);
x_9 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3, x_8);
lean_ctor_set(x_2, 0, x_9);
x_10 = l_Lean_CollectLevelParams_collect___main(x_3, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_box(0);
lean_inc(x_3);
x_15 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_11, x_3, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
x_17 = l_Lean_CollectLevelParams_collect___main(x_3, x_16);
return x_17;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__7(x_18, x_3);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_2, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_inc(x_3);
x_28 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_3, x_27);
lean_ctor_set(x_2, 0, x_28);
x_29 = l_Lean_CollectLevelParams_collect___main(x_3, x_2);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_30 = lean_box(0);
lean_inc(x_3);
x_31 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__1(x_18, x_3, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
x_33 = l_Lean_CollectLevelParams_collect___main(x_3, x_32);
return x_33;
}
}
else
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
return x_2;
}
}
}
case 4:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_List_foldl___main___at_Lean_CollectLevelParams_main___main___spec__1(x_2, x_34);
return x_35;
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_57; uint8_t x_76; uint8_t x_77; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_76 = l_Lean_Expr_hasLevelParam(x_36);
x_77 = l_Lean_Expr_hasLevelParam(x_37);
if (x_76 == 0)
{
uint8_t x_78; 
x_78 = l_String_posOfAux___main___closed__2;
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_80, x_36);
x_83 = l_coeDecidableEq(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_2);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_2, 2);
lean_dec(x_85);
x_86 = lean_ctor_get(x_2, 1);
lean_dec(x_86);
x_87 = lean_ctor_get(x_2, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_inc(x_36);
x_89 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_80, x_36, x_88);
lean_ctor_set(x_2, 1, x_89);
x_90 = l_Lean_CollectLevelParams_main___main(x_36, x_2);
if (x_77 == 0)
{
x_38 = x_90;
goto block_56;
}
else
{
x_57 = x_90;
goto block_75;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_2);
x_91 = lean_box(0);
lean_inc(x_36);
x_92 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_80, x_36, x_91);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_79);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_81);
x_94 = l_Lean_CollectLevelParams_main___main(x_36, x_93);
if (x_77 == 0)
{
x_38 = x_94;
goto block_56;
}
else
{
x_57 = x_94;
goto block_75;
}
}
}
else
{
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_36);
if (x_77 == 0)
{
x_38 = x_2;
goto block_56;
}
else
{
x_57 = x_2;
goto block_75;
}
}
}
else
{
lean_dec(x_36);
if (x_77 == 0)
{
x_38 = x_2;
goto block_56;
}
else
{
x_57 = x_2;
goto block_75;
}
}
}
else
{
uint8_t x_95; 
x_95 = l_String_posOfAux___main___closed__1;
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_2, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 2);
lean_inc(x_98);
x_99 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_97, x_36);
x_100 = l_coeDecidableEq(x_99);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_2);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_2, 2);
lean_dec(x_102);
x_103 = lean_ctor_get(x_2, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_2, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_inc(x_36);
x_106 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_97, x_36, x_105);
lean_ctor_set(x_2, 1, x_106);
x_107 = l_Lean_CollectLevelParams_main___main(x_36, x_2);
if (x_77 == 0)
{
x_38 = x_107;
goto block_56;
}
else
{
x_57 = x_107;
goto block_75;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_2);
x_108 = lean_box(0);
lean_inc(x_36);
x_109 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_97, x_36, x_108);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_96);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_98);
x_111 = l_Lean_CollectLevelParams_main___main(x_36, x_110);
if (x_77 == 0)
{
x_38 = x_111;
goto block_56;
}
else
{
x_57 = x_111;
goto block_75;
}
}
}
else
{
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_36);
if (x_77 == 0)
{
x_38 = x_2;
goto block_56;
}
else
{
x_57 = x_2;
goto block_75;
}
}
}
else
{
lean_dec(x_36);
if (x_77 == 0)
{
x_38 = x_2;
goto block_56;
}
else
{
x_57 = x_2;
goto block_75;
}
}
}
block_56:
{
uint8_t x_39; 
x_39 = l_String_posOfAux___main___closed__2;
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 2);
lean_inc(x_42);
x_43 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_41, x_37);
x_44 = l_coeDecidableEq(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_38, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_inc(x_37);
x_50 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_41, x_37, x_49);
lean_ctor_set(x_38, 1, x_50);
x_1 = x_37;
x_2 = x_38;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_38);
x_52 = lean_box(0);
lean_inc(x_37);
x_53 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_41, x_37, x_52);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_42);
x_1 = x_37;
x_2 = x_54;
goto _start;
}
}
else
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_37);
return x_38;
}
}
else
{
lean_dec(x_37);
return x_38;
}
}
block_75:
{
uint8_t x_58; 
x_58 = l_String_posOfAux___main___closed__1;
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_60, x_37);
x_63 = l_coeDecidableEq(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_57, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_57, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_inc(x_37);
x_69 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_60, x_37, x_68);
lean_ctor_set(x_57, 1, x_69);
x_1 = x_37;
x_2 = x_57;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_57);
x_71 = lean_box(0);
lean_inc(x_37);
x_72 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_60, x_37, x_71);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_61);
x_1 = x_37;
x_2 = x_73;
goto _start;
}
}
else
{
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_37);
return x_57;
}
}
else
{
lean_dec(x_37);
return x_57;
}
}
}
case 6:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_133; uint8_t x_152; uint8_t x_153; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 2);
lean_inc(x_113);
lean_dec(x_1);
x_152 = l_Lean_Expr_hasLevelParam(x_112);
x_153 = l_Lean_Expr_hasLevelParam(x_113);
if (x_152 == 0)
{
uint8_t x_154; 
x_154 = l_String_posOfAux___main___closed__2;
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 2);
lean_inc(x_157);
x_158 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_156, x_112);
x_159 = l_coeDecidableEq(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_2);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_2, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_2, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_2, 0);
lean_dec(x_163);
x_164 = lean_box(0);
lean_inc(x_112);
x_165 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_156, x_112, x_164);
lean_ctor_set(x_2, 1, x_165);
x_166 = l_Lean_CollectLevelParams_main___main(x_112, x_2);
if (x_153 == 0)
{
x_114 = x_166;
goto block_132;
}
else
{
x_133 = x_166;
goto block_151;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_2);
x_167 = lean_box(0);
lean_inc(x_112);
x_168 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_156, x_112, x_167);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_155);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_157);
x_170 = l_Lean_CollectLevelParams_main___main(x_112, x_169);
if (x_153 == 0)
{
x_114 = x_170;
goto block_132;
}
else
{
x_133 = x_170;
goto block_151;
}
}
}
else
{
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_112);
if (x_153 == 0)
{
x_114 = x_2;
goto block_132;
}
else
{
x_133 = x_2;
goto block_151;
}
}
}
else
{
lean_dec(x_112);
if (x_153 == 0)
{
x_114 = x_2;
goto block_132;
}
else
{
x_133 = x_2;
goto block_151;
}
}
}
else
{
uint8_t x_171; 
x_171 = l_String_posOfAux___main___closed__1;
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_2, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_2, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_2, 2);
lean_inc(x_174);
x_175 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_173, x_112);
x_176 = l_coeDecidableEq(x_175);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_2);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_2, 2);
lean_dec(x_178);
x_179 = lean_ctor_get(x_2, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_2, 0);
lean_dec(x_180);
x_181 = lean_box(0);
lean_inc(x_112);
x_182 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_173, x_112, x_181);
lean_ctor_set(x_2, 1, x_182);
x_183 = l_Lean_CollectLevelParams_main___main(x_112, x_2);
if (x_153 == 0)
{
x_114 = x_183;
goto block_132;
}
else
{
x_133 = x_183;
goto block_151;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_2);
x_184 = lean_box(0);
lean_inc(x_112);
x_185 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_173, x_112, x_184);
x_186 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_186, 0, x_172);
lean_ctor_set(x_186, 1, x_185);
lean_ctor_set(x_186, 2, x_174);
x_187 = l_Lean_CollectLevelParams_main___main(x_112, x_186);
if (x_153 == 0)
{
x_114 = x_187;
goto block_132;
}
else
{
x_133 = x_187;
goto block_151;
}
}
}
else
{
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_112);
if (x_153 == 0)
{
x_114 = x_2;
goto block_132;
}
else
{
x_133 = x_2;
goto block_151;
}
}
}
else
{
lean_dec(x_112);
if (x_153 == 0)
{
x_114 = x_2;
goto block_132;
}
else
{
x_133 = x_2;
goto block_151;
}
}
}
block_132:
{
uint8_t x_115; 
x_115 = l_String_posOfAux___main___closed__2;
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_117, x_113);
x_120 = l_coeDecidableEq(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_114);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_114, 2);
lean_dec(x_122);
x_123 = lean_ctor_get(x_114, 1);
lean_dec(x_123);
x_124 = lean_ctor_get(x_114, 0);
lean_dec(x_124);
x_125 = lean_box(0);
lean_inc(x_113);
x_126 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_117, x_113, x_125);
lean_ctor_set(x_114, 1, x_126);
x_1 = x_113;
x_2 = x_114;
goto _start;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_114);
x_128 = lean_box(0);
lean_inc(x_113);
x_129 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_117, x_113, x_128);
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_116);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_118);
x_1 = x_113;
x_2 = x_130;
goto _start;
}
}
else
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_113);
return x_114;
}
}
else
{
lean_dec(x_113);
return x_114;
}
}
block_151:
{
uint8_t x_134; 
x_134 = l_String_posOfAux___main___closed__1;
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_136, x_113);
x_139 = l_coeDecidableEq(x_138);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_133);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_133, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_133, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_133, 0);
lean_dec(x_143);
x_144 = lean_box(0);
lean_inc(x_113);
x_145 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_136, x_113, x_144);
lean_ctor_set(x_133, 1, x_145);
x_1 = x_113;
x_2 = x_133;
goto _start;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_133);
x_147 = lean_box(0);
lean_inc(x_113);
x_148 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_136, x_113, x_147);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_137);
x_1 = x_113;
x_2 = x_149;
goto _start;
}
}
else
{
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_113);
return x_133;
}
}
else
{
lean_dec(x_113);
return x_133;
}
}
}
case 7:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_209; uint8_t x_228; uint8_t x_229; 
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_1, 2);
lean_inc(x_189);
lean_dec(x_1);
x_228 = l_Lean_Expr_hasLevelParam(x_188);
x_229 = l_Lean_Expr_hasLevelParam(x_189);
if (x_228 == 0)
{
uint8_t x_230; 
x_230 = l_String_posOfAux___main___closed__2;
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_2, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_2, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_2, 2);
lean_inc(x_233);
x_234 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_232, x_188);
x_235 = l_coeDecidableEq(x_234);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_2);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_237 = lean_ctor_get(x_2, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_2, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_2, 0);
lean_dec(x_239);
x_240 = lean_box(0);
lean_inc(x_188);
x_241 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_232, x_188, x_240);
lean_ctor_set(x_2, 1, x_241);
x_242 = l_Lean_CollectLevelParams_main___main(x_188, x_2);
if (x_229 == 0)
{
x_190 = x_242;
goto block_208;
}
else
{
x_209 = x_242;
goto block_227;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
x_243 = lean_box(0);
lean_inc(x_188);
x_244 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_232, x_188, x_243);
x_245 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_245, 0, x_231);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_245, 2, x_233);
x_246 = l_Lean_CollectLevelParams_main___main(x_188, x_245);
if (x_229 == 0)
{
x_190 = x_246;
goto block_208;
}
else
{
x_209 = x_246;
goto block_227;
}
}
}
else
{
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_188);
if (x_229 == 0)
{
x_190 = x_2;
goto block_208;
}
else
{
x_209 = x_2;
goto block_227;
}
}
}
else
{
lean_dec(x_188);
if (x_229 == 0)
{
x_190 = x_2;
goto block_208;
}
else
{
x_209 = x_2;
goto block_227;
}
}
}
else
{
uint8_t x_247; 
x_247 = l_String_posOfAux___main___closed__1;
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_2, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_2, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_2, 2);
lean_inc(x_250);
x_251 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_249, x_188);
x_252 = l_coeDecidableEq(x_251);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_2);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_2, 2);
lean_dec(x_254);
x_255 = lean_ctor_get(x_2, 1);
lean_dec(x_255);
x_256 = lean_ctor_get(x_2, 0);
lean_dec(x_256);
x_257 = lean_box(0);
lean_inc(x_188);
x_258 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_249, x_188, x_257);
lean_ctor_set(x_2, 1, x_258);
x_259 = l_Lean_CollectLevelParams_main___main(x_188, x_2);
if (x_229 == 0)
{
x_190 = x_259;
goto block_208;
}
else
{
x_209 = x_259;
goto block_227;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_2);
x_260 = lean_box(0);
lean_inc(x_188);
x_261 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_249, x_188, x_260);
x_262 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_262, 0, x_248);
lean_ctor_set(x_262, 1, x_261);
lean_ctor_set(x_262, 2, x_250);
x_263 = l_Lean_CollectLevelParams_main___main(x_188, x_262);
if (x_229 == 0)
{
x_190 = x_263;
goto block_208;
}
else
{
x_209 = x_263;
goto block_227;
}
}
}
else
{
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_188);
if (x_229 == 0)
{
x_190 = x_2;
goto block_208;
}
else
{
x_209 = x_2;
goto block_227;
}
}
}
else
{
lean_dec(x_188);
if (x_229 == 0)
{
x_190 = x_2;
goto block_208;
}
else
{
x_209 = x_2;
goto block_227;
}
}
}
block_208:
{
uint8_t x_191; 
x_191 = l_String_posOfAux___main___closed__2;
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 2);
lean_inc(x_194);
x_195 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_193, x_189);
x_196 = l_coeDecidableEq(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_190);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_190, 2);
lean_dec(x_198);
x_199 = lean_ctor_get(x_190, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_190, 0);
lean_dec(x_200);
x_201 = lean_box(0);
lean_inc(x_189);
x_202 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_193, x_189, x_201);
lean_ctor_set(x_190, 1, x_202);
x_1 = x_189;
x_2 = x_190;
goto _start;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_190);
x_204 = lean_box(0);
lean_inc(x_189);
x_205 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_193, x_189, x_204);
x_206 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_206, 0, x_192);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set(x_206, 2, x_194);
x_1 = x_189;
x_2 = x_206;
goto _start;
}
}
else
{
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_189);
return x_190;
}
}
else
{
lean_dec(x_189);
return x_190;
}
}
block_227:
{
uint8_t x_210; 
x_210 = l_String_posOfAux___main___closed__1;
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_209, 2);
lean_inc(x_213);
x_214 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_212, x_189);
x_215 = l_coeDecidableEq(x_214);
if (x_215 == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_209);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_209, 2);
lean_dec(x_217);
x_218 = lean_ctor_get(x_209, 1);
lean_dec(x_218);
x_219 = lean_ctor_get(x_209, 0);
lean_dec(x_219);
x_220 = lean_box(0);
lean_inc(x_189);
x_221 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_212, x_189, x_220);
lean_ctor_set(x_209, 1, x_221);
x_1 = x_189;
x_2 = x_209;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_209);
x_223 = lean_box(0);
lean_inc(x_189);
x_224 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_212, x_189, x_223);
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_211);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_213);
x_1 = x_189;
x_2 = x_225;
goto _start;
}
}
else
{
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_189);
return x_209;
}
}
else
{
lean_dec(x_189);
return x_209;
}
}
}
case 8:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_286; uint8_t x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_327; 
x_264 = lean_ctor_get(x_1, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_1, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_1, 3);
lean_inc(x_266);
lean_dec(x_1);
x_305 = l_Lean_Expr_hasLevelParam(x_264);
x_306 = l_Lean_Expr_hasLevelParam(x_265);
x_307 = l_Lean_Expr_hasLevelParam(x_266);
if (x_305 == 0)
{
uint8_t x_346; 
x_346 = l_String_posOfAux___main___closed__2;
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_351; 
x_347 = lean_ctor_get(x_2, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_2, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_2, 2);
lean_inc(x_349);
x_350 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_348, x_264);
x_351 = l_coeDecidableEq(x_350);
if (x_351 == 0)
{
uint8_t x_352; 
x_352 = !lean_is_exclusive(x_2);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_2, 2);
lean_dec(x_353);
x_354 = lean_ctor_get(x_2, 1);
lean_dec(x_354);
x_355 = lean_ctor_get(x_2, 0);
lean_dec(x_355);
x_356 = lean_box(0);
lean_inc(x_264);
x_357 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_348, x_264, x_356);
lean_ctor_set(x_2, 1, x_357);
x_358 = l_Lean_CollectLevelParams_main___main(x_264, x_2);
if (x_306 == 0)
{
x_308 = x_358;
goto block_326;
}
else
{
x_327 = x_358;
goto block_345;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_2);
x_359 = lean_box(0);
lean_inc(x_264);
x_360 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_348, x_264, x_359);
x_361 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_361, 0, x_347);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_361, 2, x_349);
x_362 = l_Lean_CollectLevelParams_main___main(x_264, x_361);
if (x_306 == 0)
{
x_308 = x_362;
goto block_326;
}
else
{
x_327 = x_362;
goto block_345;
}
}
}
else
{
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_264);
if (x_306 == 0)
{
x_308 = x_2;
goto block_326;
}
else
{
x_327 = x_2;
goto block_345;
}
}
}
else
{
lean_dec(x_264);
if (x_306 == 0)
{
x_308 = x_2;
goto block_326;
}
else
{
x_327 = x_2;
goto block_345;
}
}
}
else
{
uint8_t x_363; 
x_363 = l_String_posOfAux___main___closed__1;
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; 
x_364 = lean_ctor_get(x_2, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_2, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_2, 2);
lean_inc(x_366);
x_367 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_365, x_264);
x_368 = l_coeDecidableEq(x_367);
if (x_368 == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_2);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_2, 2);
lean_dec(x_370);
x_371 = lean_ctor_get(x_2, 1);
lean_dec(x_371);
x_372 = lean_ctor_get(x_2, 0);
lean_dec(x_372);
x_373 = lean_box(0);
lean_inc(x_264);
x_374 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_365, x_264, x_373);
lean_ctor_set(x_2, 1, x_374);
x_375 = l_Lean_CollectLevelParams_main___main(x_264, x_2);
if (x_306 == 0)
{
x_308 = x_375;
goto block_326;
}
else
{
x_327 = x_375;
goto block_345;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_2);
x_376 = lean_box(0);
lean_inc(x_264);
x_377 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_365, x_264, x_376);
x_378 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_378, 0, x_364);
lean_ctor_set(x_378, 1, x_377);
lean_ctor_set(x_378, 2, x_366);
x_379 = l_Lean_CollectLevelParams_main___main(x_264, x_378);
if (x_306 == 0)
{
x_308 = x_379;
goto block_326;
}
else
{
x_327 = x_379;
goto block_345;
}
}
}
else
{
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_364);
lean_dec(x_264);
if (x_306 == 0)
{
x_308 = x_2;
goto block_326;
}
else
{
x_327 = x_2;
goto block_345;
}
}
}
else
{
lean_dec(x_264);
if (x_306 == 0)
{
x_308 = x_2;
goto block_326;
}
else
{
x_327 = x_2;
goto block_345;
}
}
}
block_285:
{
uint8_t x_268; 
x_268 = l_String_posOfAux___main___closed__2;
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 2);
lean_inc(x_271);
x_272 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_270, x_266);
x_273 = l_coeDecidableEq(x_272);
if (x_273 == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_267);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_275 = lean_ctor_get(x_267, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_267, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_267, 0);
lean_dec(x_277);
x_278 = lean_box(0);
lean_inc(x_266);
x_279 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_270, x_266, x_278);
lean_ctor_set(x_267, 1, x_279);
x_1 = x_266;
x_2 = x_267;
goto _start;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_267);
x_281 = lean_box(0);
lean_inc(x_266);
x_282 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_270, x_266, x_281);
x_283 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_283, 0, x_269);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_283, 2, x_271);
x_1 = x_266;
x_2 = x_283;
goto _start;
}
}
else
{
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_266);
return x_267;
}
}
else
{
lean_dec(x_266);
return x_267;
}
}
block_304:
{
uint8_t x_287; 
x_287 = l_String_posOfAux___main___closed__1;
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; 
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 2);
lean_inc(x_290);
x_291 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_289, x_266);
x_292 = l_coeDecidableEq(x_291);
if (x_292 == 0)
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_286);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_286, 2);
lean_dec(x_294);
x_295 = lean_ctor_get(x_286, 1);
lean_dec(x_295);
x_296 = lean_ctor_get(x_286, 0);
lean_dec(x_296);
x_297 = lean_box(0);
lean_inc(x_266);
x_298 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_289, x_266, x_297);
lean_ctor_set(x_286, 1, x_298);
x_1 = x_266;
x_2 = x_286;
goto _start;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_286);
x_300 = lean_box(0);
lean_inc(x_266);
x_301 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_289, x_266, x_300);
x_302 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_302, 0, x_288);
lean_ctor_set(x_302, 1, x_301);
lean_ctor_set(x_302, 2, x_290);
x_1 = x_266;
x_2 = x_302;
goto _start;
}
}
else
{
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_266);
return x_286;
}
}
else
{
lean_dec(x_266);
return x_286;
}
}
block_326:
{
uint8_t x_309; 
x_309 = l_String_posOfAux___main___closed__2;
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 2);
lean_inc(x_312);
x_313 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_311, x_265);
x_314 = l_coeDecidableEq(x_313);
if (x_314 == 0)
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_308);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_316 = lean_ctor_get(x_308, 2);
lean_dec(x_316);
x_317 = lean_ctor_get(x_308, 1);
lean_dec(x_317);
x_318 = lean_ctor_get(x_308, 0);
lean_dec(x_318);
x_319 = lean_box(0);
lean_inc(x_265);
x_320 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_311, x_265, x_319);
lean_ctor_set(x_308, 1, x_320);
x_321 = l_Lean_CollectLevelParams_main___main(x_265, x_308);
if (x_307 == 0)
{
x_267 = x_321;
goto block_285;
}
else
{
x_286 = x_321;
goto block_304;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_308);
x_322 = lean_box(0);
lean_inc(x_265);
x_323 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_311, x_265, x_322);
x_324 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_324, 0, x_310);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set(x_324, 2, x_312);
x_325 = l_Lean_CollectLevelParams_main___main(x_265, x_324);
if (x_307 == 0)
{
x_267 = x_325;
goto block_285;
}
else
{
x_286 = x_325;
goto block_304;
}
}
}
else
{
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_265);
if (x_307 == 0)
{
x_267 = x_308;
goto block_285;
}
else
{
x_286 = x_308;
goto block_304;
}
}
}
else
{
lean_dec(x_265);
if (x_307 == 0)
{
x_267 = x_308;
goto block_285;
}
else
{
x_286 = x_308;
goto block_304;
}
}
}
block_345:
{
uint8_t x_328; 
x_328 = l_String_posOfAux___main___closed__1;
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_333; 
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_327, 2);
lean_inc(x_331);
x_332 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_330, x_265);
x_333 = l_coeDecidableEq(x_332);
if (x_333 == 0)
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_327);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_335 = lean_ctor_get(x_327, 2);
lean_dec(x_335);
x_336 = lean_ctor_get(x_327, 1);
lean_dec(x_336);
x_337 = lean_ctor_get(x_327, 0);
lean_dec(x_337);
x_338 = lean_box(0);
lean_inc(x_265);
x_339 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_330, x_265, x_338);
lean_ctor_set(x_327, 1, x_339);
x_340 = l_Lean_CollectLevelParams_main___main(x_265, x_327);
if (x_307 == 0)
{
x_267 = x_340;
goto block_285;
}
else
{
x_286 = x_340;
goto block_304;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_327);
x_341 = lean_box(0);
lean_inc(x_265);
x_342 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_330, x_265, x_341);
x_343 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_343, 0, x_329);
lean_ctor_set(x_343, 1, x_342);
lean_ctor_set(x_343, 2, x_331);
x_344 = l_Lean_CollectLevelParams_main___main(x_265, x_343);
if (x_307 == 0)
{
x_267 = x_344;
goto block_285;
}
else
{
x_286 = x_344;
goto block_304;
}
}
}
else
{
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec(x_265);
if (x_307 == 0)
{
x_267 = x_327;
goto block_285;
}
else
{
x_286 = x_327;
goto block_304;
}
}
}
else
{
lean_dec(x_265);
if (x_307 == 0)
{
x_267 = x_327;
goto block_285;
}
else
{
x_286 = x_327;
goto block_304;
}
}
}
}
case 10:
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_1, 1);
lean_inc(x_380);
lean_dec(x_1);
x_381 = l_Lean_Expr_hasLevelParam(x_380);
if (x_381 == 0)
{
uint8_t x_382; 
x_382 = l_String_posOfAux___main___closed__2;
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; uint8_t x_387; 
x_383 = lean_ctor_get(x_2, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_2, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_2, 2);
lean_inc(x_385);
x_386 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_384, x_380);
x_387 = l_coeDecidableEq(x_386);
if (x_387 == 0)
{
uint8_t x_388; 
x_388 = !lean_is_exclusive(x_2);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_389 = lean_ctor_get(x_2, 2);
lean_dec(x_389);
x_390 = lean_ctor_get(x_2, 1);
lean_dec(x_390);
x_391 = lean_ctor_get(x_2, 0);
lean_dec(x_391);
x_392 = lean_box(0);
lean_inc(x_380);
x_393 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_384, x_380, x_392);
lean_ctor_set(x_2, 1, x_393);
x_1 = x_380;
goto _start;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_2);
x_395 = lean_box(0);
lean_inc(x_380);
x_396 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_384, x_380, x_395);
x_397 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_397, 0, x_383);
lean_ctor_set(x_397, 1, x_396);
lean_ctor_set(x_397, 2, x_385);
x_1 = x_380;
x_2 = x_397;
goto _start;
}
}
else
{
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_383);
lean_dec(x_380);
return x_2;
}
}
else
{
lean_dec(x_380);
return x_2;
}
}
else
{
uint8_t x_399; 
x_399 = l_String_posOfAux___main___closed__1;
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_2, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_2, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_2, 2);
lean_inc(x_402);
x_403 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_401, x_380);
x_404 = l_coeDecidableEq(x_403);
if (x_404 == 0)
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_2);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_ctor_get(x_2, 2);
lean_dec(x_406);
x_407 = lean_ctor_get(x_2, 1);
lean_dec(x_407);
x_408 = lean_ctor_get(x_2, 0);
lean_dec(x_408);
x_409 = lean_box(0);
lean_inc(x_380);
x_410 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_401, x_380, x_409);
lean_ctor_set(x_2, 1, x_410);
x_1 = x_380;
goto _start;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_2);
x_412 = lean_box(0);
lean_inc(x_380);
x_413 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_401, x_380, x_412);
x_414 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_414, 0, x_400);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set(x_414, 2, x_402);
x_1 = x_380;
x_2 = x_414;
goto _start;
}
}
else
{
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_380);
return x_2;
}
}
else
{
lean_dec(x_380);
return x_2;
}
}
}
case 11:
{
lean_object* x_416; uint8_t x_417; 
x_416 = lean_ctor_get(x_1, 2);
lean_inc(x_416);
lean_dec(x_1);
x_417 = l_Lean_Expr_hasLevelParam(x_416);
if (x_417 == 0)
{
uint8_t x_418; 
x_418 = l_String_posOfAux___main___closed__2;
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_2, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_2, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_2, 2);
lean_inc(x_421);
x_422 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_420, x_416);
x_423 = l_coeDecidableEq(x_422);
if (x_423 == 0)
{
uint8_t x_424; 
x_424 = !lean_is_exclusive(x_2);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_425 = lean_ctor_get(x_2, 2);
lean_dec(x_425);
x_426 = lean_ctor_get(x_2, 1);
lean_dec(x_426);
x_427 = lean_ctor_get(x_2, 0);
lean_dec(x_427);
x_428 = lean_box(0);
lean_inc(x_416);
x_429 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_420, x_416, x_428);
lean_ctor_set(x_2, 1, x_429);
x_1 = x_416;
goto _start;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_2);
x_431 = lean_box(0);
lean_inc(x_416);
x_432 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_420, x_416, x_431);
x_433 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_433, 0, x_419);
lean_ctor_set(x_433, 1, x_432);
lean_ctor_set(x_433, 2, x_421);
x_1 = x_416;
x_2 = x_433;
goto _start;
}
}
else
{
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_416);
return x_2;
}
}
else
{
lean_dec(x_416);
return x_2;
}
}
else
{
uint8_t x_435; 
x_435 = l_String_posOfAux___main___closed__1;
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_440; 
x_436 = lean_ctor_get(x_2, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_2, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_2, 2);
lean_inc(x_438);
x_439 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_437, x_416);
x_440 = l_coeDecidableEq(x_439);
if (x_440 == 0)
{
uint8_t x_441; 
x_441 = !lean_is_exclusive(x_2);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_442 = lean_ctor_get(x_2, 2);
lean_dec(x_442);
x_443 = lean_ctor_get(x_2, 1);
lean_dec(x_443);
x_444 = lean_ctor_get(x_2, 0);
lean_dec(x_444);
x_445 = lean_box(0);
lean_inc(x_416);
x_446 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_437, x_416, x_445);
lean_ctor_set(x_2, 1, x_446);
x_1 = x_416;
goto _start;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_2);
x_448 = lean_box(0);
lean_inc(x_416);
x_449 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_437, x_416, x_448);
x_450 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_450, 0, x_436);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_438);
x_1 = x_416;
x_2 = x_450;
goto _start;
}
}
else
{
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_416);
return x_2;
}
}
else
{
lean_dec(x_416);
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
