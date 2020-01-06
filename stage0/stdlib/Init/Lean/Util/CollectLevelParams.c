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
lean_object* l_mkHashMap___at_Lean_collectLevelParams___spec__2(lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_collect(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object*, lean_object*);
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
lean_object* l_mkHashSet___at_Lean_collectLevelParams___spec__3(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitLevel___spec__4(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_visitExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_CollectLevelParams_visitExpr___spec__4(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1___boxed(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_CollectLevelParams_visitLevel___spec__6(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_collectLevelParams___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_collectLevelParams___spec__4(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams___closed__3;
lean_object* l_AssocList_replace___main___at_Lean_CollectLevelParams_visitExpr___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_CollectLevelParams_visitLevel___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_CollectLevelParams_visitExpr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_collectLevelParams___spec__1(lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_CollectLevelParams_visitLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_2);
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
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_2, x_15);
lean_ctor_set(x_3, 0, x_16);
x_17 = lean_apply_2(x_1, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_2, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
x_21 = lean_apply_2(x_1, x_2, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_inc(x_3);
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_15);
lean_ctor_set(x_2, 0, x_16);
x_1 = x_3;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_18 = lean_box(0);
lean_inc(x_3);
x_19 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
x_1 = x_3;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_48; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_48 = l_Lean_Level_hasParam(x_24);
if (x_48 == 0)
{
lean_dec(x_24);
x_26 = x_2;
goto block_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 2);
lean_inc(x_51);
x_52 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_49, x_24);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_2, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_2, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_inc(x_24);
x_58 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_49, x_24, x_57);
lean_ctor_set(x_2, 0, x_58);
x_59 = l_Lean_CollectLevelParams_collect___main(x_24, x_2);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_26 = x_60;
goto block_47;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_61 = lean_box(0);
lean_inc(x_24);
x_62 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_49, x_24, x_61);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_63, 2, x_51);
x_64 = l_Lean_CollectLevelParams_collect___main(x_24, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_26 = x_65;
goto block_47;
}
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_24);
x_26 = x_2;
goto block_47;
}
}
block_47:
{
uint8_t x_27; 
x_27 = l_Lean_Level_hasParam(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 2);
lean_inc(x_32);
x_33 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_30, x_25);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_26, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_inc(x_25);
x_39 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_30, x_25, x_38);
lean_ctor_set(x_26, 0, x_39);
x_1 = x_25;
x_2 = x_26;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
x_41 = lean_box(0);
lean_inc(x_25);
x_42 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_30, x_25, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_32);
x_1 = x_25;
x_2 = x_43;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_26);
return x_46;
}
}
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_90; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
lean_dec(x_1);
x_90 = l_Lean_Level_hasParam(x_66);
if (x_90 == 0)
{
lean_dec(x_66);
x_68 = x_2;
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_2, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 2);
lean_inc(x_93);
x_94 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_91, x_66);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_2);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_2, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_2, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_2, 0);
lean_dec(x_98);
x_99 = lean_box(0);
lean_inc(x_66);
x_100 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_91, x_66, x_99);
lean_ctor_set(x_2, 0, x_100);
x_101 = l_Lean_CollectLevelParams_collect___main(x_66, x_2);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_68 = x_102;
goto block_89;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
x_103 = lean_box(0);
lean_inc(x_66);
x_104 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_91, x_66, x_103);
x_105 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_92);
lean_ctor_set(x_105, 2, x_93);
x_106 = l_Lean_CollectLevelParams_collect___main(x_66, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_68 = x_107;
goto block_89;
}
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_66);
x_68 = x_2;
goto block_89;
}
}
block_89:
{
uint8_t x_69; 
x_69 = l_Lean_Level_hasParam(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 2);
lean_inc(x_74);
x_75 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_72, x_67);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_68, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_68, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_68, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_inc(x_67);
x_81 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_72, x_67, x_80);
lean_ctor_set(x_68, 0, x_81);
x_1 = x_67;
x_2 = x_68;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_68);
x_83 = lean_box(0);
lean_inc(x_67);
x_84 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_72, x_67, x_83);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
lean_ctor_set(x_85, 2, x_74);
x_1 = x_67;
x_2 = x_85;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_67);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_68);
return x_88;
}
}
}
}
case 4:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_2, 2);
x_111 = lean_array_push(x_110, x_108);
lean_ctor_set(x_2, 2, x_111);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_2);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_2, 0);
x_115 = lean_ctor_get(x_2, 1);
x_116 = lean_ctor_get(x_2, 2);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_2);
x_117 = lean_array_push(x_116, x_108);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set(x_118, 2, x_117);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
default: 
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_1);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_2);
return x_122;
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_8, x_2);
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
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_8, x_2, x_15);
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
x_19 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_8, x_2, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_9);
x_21 = lean_apply_2(x_1, x_2, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
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
lean_object* l_List_forM___main___at_Lean_CollectLevelParams_main___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Level_hasParam(x_5);
if (x_7 == 0)
{
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_9, x_5);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_inc(x_5);
x_18 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_9, x_5, x_17);
lean_ctor_set(x_2, 0, x_18);
x_19 = l_Lean_CollectLevelParams_collect___main(x_5, x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_6;
x_2 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_22 = lean_box(0);
lean_inc(x_5);
x_23 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_9, x_5, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
lean_ctor_set(x_24, 2, x_11);
x_25 = l_Lean_CollectLevelParams_collect___main(x_5, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_1 = x_6;
x_2 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_1 = x_6;
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitLevel___spec__1(x_7, x_3);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_inc(x_3);
x_16 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_15);
lean_ctor_set(x_2, 0, x_16);
x_17 = l_Lean_CollectLevelParams_collect___main(x_3, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_box(0);
lean_inc(x_3);
x_19 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitLevel___spec__3(x_7, x_3, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_20, 2, x_9);
x_21 = l_Lean_CollectLevelParams_collect___main(x_3, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
}
case 4:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_List_forM___main___at_Lean_CollectLevelParams_main___main___spec__1(x_24, x_2);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_50; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_50 = l_Lean_Expr_hasLevelParam(x_26);
if (x_50 == 0)
{
lean_dec(x_26);
x_28 = x_2;
goto block_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_52, x_26);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_2, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_2, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_inc(x_26);
x_60 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_52, x_26, x_59);
lean_ctor_set(x_2, 1, x_60);
x_61 = l_Lean_CollectLevelParams_main___main(x_26, x_2);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_28 = x_62;
goto block_49;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_63 = lean_box(0);
lean_inc(x_26);
x_64 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_52, x_26, x_63);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_53);
x_66 = l_Lean_CollectLevelParams_main___main(x_26, x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_28 = x_67;
goto block_49;
}
}
else
{
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_26);
x_28 = x_2;
goto block_49;
}
}
block_49:
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasLevelParam(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 2);
lean_inc(x_34);
x_35 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_33, x_27);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_28, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_28, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_inc(x_27);
x_41 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_33, x_27, x_40);
lean_ctor_set(x_28, 1, x_41);
x_1 = x_27;
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_28);
x_43 = lean_box(0);
lean_inc(x_27);
x_44 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_33, x_27, x_43);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
x_1 = x_27;
x_2 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_28);
return x_48;
}
}
}
}
case 6:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_92; 
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
lean_dec(x_1);
x_92 = l_Lean_Expr_hasLevelParam(x_68);
if (x_92 == 0)
{
lean_dec(x_68);
x_70 = x_2;
goto block_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_2, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 2);
lean_inc(x_95);
x_96 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_94, x_68);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_2);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_2, 2);
lean_dec(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_2, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_inc(x_68);
x_102 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_94, x_68, x_101);
lean_ctor_set(x_2, 1, x_102);
x_103 = l_Lean_CollectLevelParams_main___main(x_68, x_2);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_70 = x_104;
goto block_91;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
x_105 = lean_box(0);
lean_inc(x_68);
x_106 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_94, x_68, x_105);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_93);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_95);
x_108 = l_Lean_CollectLevelParams_main___main(x_68, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_70 = x_109;
goto block_91;
}
}
else
{
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_68);
x_70 = x_2;
goto block_91;
}
}
block_91:
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasLevelParam(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 2);
lean_inc(x_76);
x_77 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_75, x_69);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_70, 2);
lean_dec(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_dec(x_80);
x_81 = lean_ctor_get(x_70, 0);
lean_dec(x_81);
x_82 = lean_box(0);
lean_inc(x_69);
x_83 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_75, x_69, x_82);
lean_ctor_set(x_70, 1, x_83);
x_1 = x_69;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_70);
x_85 = lean_box(0);
lean_inc(x_69);
x_86 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_75, x_69, x_85);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_76);
x_1 = x_69;
x_2 = x_87;
goto _start;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_69);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_70);
return x_90;
}
}
}
}
case 7:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_134; 
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 2);
lean_inc(x_111);
lean_dec(x_1);
x_134 = l_Lean_Expr_hasLevelParam(x_110);
if (x_134 == 0)
{
lean_dec(x_110);
x_112 = x_2;
goto block_133;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
x_138 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_136, x_110);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_2);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_2, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_2, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_2, 0);
lean_dec(x_142);
x_143 = lean_box(0);
lean_inc(x_110);
x_144 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_136, x_110, x_143);
lean_ctor_set(x_2, 1, x_144);
x_145 = l_Lean_CollectLevelParams_main___main(x_110, x_2);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_112 = x_146;
goto block_133;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
x_147 = lean_box(0);
lean_inc(x_110);
x_148 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_136, x_110, x_147);
x_149 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_137);
x_150 = l_Lean_CollectLevelParams_main___main(x_110, x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_112 = x_151;
goto block_133;
}
}
else
{
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_110);
x_112 = x_2;
goto block_133;
}
}
block_133:
{
uint8_t x_113; 
x_113 = l_Lean_Expr_hasLevelParam(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 2);
lean_inc(x_118);
x_119 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_117, x_111);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_112, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_112, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_112, 0);
lean_dec(x_123);
x_124 = lean_box(0);
lean_inc(x_111);
x_125 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_117, x_111, x_124);
lean_ctor_set(x_112, 1, x_125);
x_1 = x_111;
x_2 = x_112;
goto _start;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_112);
x_127 = lean_box(0);
lean_inc(x_111);
x_128 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_117, x_111, x_127);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_116);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_118);
x_1 = x_111;
x_2 = x_129;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_111);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_112);
return x_132;
}
}
}
}
case 8:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_177; uint8_t x_197; 
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 3);
lean_inc(x_154);
lean_dec(x_1);
x_197 = l_Lean_Expr_hasLevelParam(x_152);
if (x_197 == 0)
{
lean_dec(x_152);
x_177 = x_2;
goto block_196;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_2, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_2, 2);
lean_inc(x_200);
x_201 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_199, x_152);
if (x_201 == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_2);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_2, 2);
lean_dec(x_203);
x_204 = lean_ctor_get(x_2, 1);
lean_dec(x_204);
x_205 = lean_ctor_get(x_2, 0);
lean_dec(x_205);
x_206 = lean_box(0);
lean_inc(x_152);
x_207 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_199, x_152, x_206);
lean_ctor_set(x_2, 1, x_207);
x_208 = l_Lean_CollectLevelParams_main___main(x_152, x_2);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_177 = x_209;
goto block_196;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_2);
x_210 = lean_box(0);
lean_inc(x_152);
x_211 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_199, x_152, x_210);
x_212 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_212, 0, x_198);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_200);
x_213 = l_Lean_CollectLevelParams_main___main(x_152, x_212);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_177 = x_214;
goto block_196;
}
}
else
{
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_152);
x_177 = x_2;
goto block_196;
}
}
block_176:
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasLevelParam(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_154);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 2);
lean_inc(x_161);
x_162 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_160, x_154);
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_155);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_155, 2);
lean_dec(x_164);
x_165 = lean_ctor_get(x_155, 1);
lean_dec(x_165);
x_166 = lean_ctor_get(x_155, 0);
lean_dec(x_166);
x_167 = lean_box(0);
lean_inc(x_154);
x_168 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_160, x_154, x_167);
lean_ctor_set(x_155, 1, x_168);
x_1 = x_154;
x_2 = x_155;
goto _start;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_155);
x_170 = lean_box(0);
lean_inc(x_154);
x_171 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_160, x_154, x_170);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_159);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_161);
x_1 = x_154;
x_2 = x_172;
goto _start;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_154);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_155);
return x_175;
}
}
}
block_196:
{
uint8_t x_178; 
x_178 = l_Lean_Expr_hasLevelParam(x_153);
if (x_178 == 0)
{
lean_dec(x_153);
x_155 = x_177;
goto block_176;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 2);
lean_inc(x_181);
x_182 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_180, x_153);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_177);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_177, 2);
lean_dec(x_184);
x_185 = lean_ctor_get(x_177, 1);
lean_dec(x_185);
x_186 = lean_ctor_get(x_177, 0);
lean_dec(x_186);
x_187 = lean_box(0);
lean_inc(x_153);
x_188 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_180, x_153, x_187);
lean_ctor_set(x_177, 1, x_188);
x_189 = l_Lean_CollectLevelParams_main___main(x_153, x_177);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_155 = x_190;
goto block_176;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_177);
x_191 = lean_box(0);
lean_inc(x_153);
x_192 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_180, x_153, x_191);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_179);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_181);
x_194 = l_Lean_CollectLevelParams_main___main(x_153, x_193);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_155 = x_195;
goto block_176;
}
}
else
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_153);
x_155 = x_177;
goto block_176;
}
}
}
}
case 10:
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_1, 1);
lean_inc(x_215);
lean_dec(x_1);
x_216 = l_Lean_Expr_hasLevelParam(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_215);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_2);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_2, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_2, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_2, 2);
lean_inc(x_221);
x_222 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_220, x_215);
if (x_222 == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_2);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_2, 2);
lean_dec(x_224);
x_225 = lean_ctor_get(x_2, 1);
lean_dec(x_225);
x_226 = lean_ctor_get(x_2, 0);
lean_dec(x_226);
x_227 = lean_box(0);
lean_inc(x_215);
x_228 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_220, x_215, x_227);
lean_ctor_set(x_2, 1, x_228);
x_1 = x_215;
goto _start;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_2);
x_230 = lean_box(0);
lean_inc(x_215);
x_231 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_220, x_215, x_230);
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_219);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_221);
x_1 = x_215;
x_2 = x_232;
goto _start;
}
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_215);
x_234 = lean_box(0);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_2);
return x_235;
}
}
}
case 11:
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_ctor_get(x_1, 2);
lean_inc(x_236);
lean_dec(x_1);
x_237 = l_Lean_Expr_hasLevelParam(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_236);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_2);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_2, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_2, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_2, 2);
lean_inc(x_242);
x_243 = l_HashMapImp_contains___at_Lean_CollectLevelParams_visitExpr___spec__1(x_241, x_236);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_2);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_2, 2);
lean_dec(x_245);
x_246 = lean_ctor_get(x_2, 1);
lean_dec(x_246);
x_247 = lean_ctor_get(x_2, 0);
lean_dec(x_247);
x_248 = lean_box(0);
lean_inc(x_236);
x_249 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_241, x_236, x_248);
lean_ctor_set(x_2, 1, x_249);
x_1 = x_236;
goto _start;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
x_251 = lean_box(0);
lean_inc(x_236);
x_252 = l_HashMapImp_insert___at_Lean_CollectLevelParams_visitExpr___spec__3(x_241, x_236, x_251);
x_253 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_253, 0, x_240);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_242);
x_1 = x_236;
x_2 = x_253;
goto _start;
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_236);
x_255 = lean_box(0);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_2);
return x_256;
}
}
}
default: 
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_1);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_2);
return x_258;
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
lean_object* l_mkHashMap___at_Lean_collectLevelParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_collectLevelParams___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_collectLevelParams___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_collectLevelParams___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_collectLevelParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_collectLevelParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_collectLevelParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_collectLevelParams___closed__1;
x_2 = l_Lean_collectLevelParams___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_collectLevelParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_collectLevelParams___closed__3;
x_3 = l_Lean_CollectLevelParams_main___main(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
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
l_Lean_collectLevelParams___closed__1 = _init_l_Lean_collectLevelParams___closed__1();
lean_mark_persistent(l_Lean_collectLevelParams___closed__1);
l_Lean_collectLevelParams___closed__2 = _init_l_Lean_collectLevelParams___closed__2();
lean_mark_persistent(l_Lean_collectLevelParams___closed__2);
l_Lean_collectLevelParams___closed__3 = _init_l_Lean_collectLevelParams___closed__3();
lean_mark_persistent(l_Lean_collectLevelParams___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
