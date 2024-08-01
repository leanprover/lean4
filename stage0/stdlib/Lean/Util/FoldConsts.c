// Lean compiler output
// Module: Lean.Util.FoldConsts
// Imports: Lean.Expr Lean.Environment
#include <lean/lean.h>
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
static lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_getUsedConstantsAsSet___closed__1;
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1;
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getUsedConstants___closed__2;
lean_object* l_Lean_NameSet_append___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
lean_object* l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_State_visited___default;
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
static lean_object* l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__5___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lambda__1(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getUsedConstants___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__3(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_State_visited___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ptr_addr(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__5___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_hashset_mk_idx(x_6, x_10);
x_12 = lean_array_uget(x_1, x_11);
lean_ctor_set(x_2, 1, x_12);
x_13 = lean_array_uset(x_1, x_11, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_array_get_size(x_1);
x_18 = lean_ptr_addr(x_15);
x_19 = lean_usize_to_uint64(x_18);
x_20 = 11;
x_21 = lean_uint64_mix_hash(x_19, x_20);
x_22 = lean_hashset_mk_idx(x_17, x_21);
x_23 = lean_array_uget(x_1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_uset(x_1, x_22, x_24);
x_1 = x_25;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__5___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ptr_addr(x_2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ptr_addr(x_2);
x_15 = lean_ptr_addr(x_12);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(x_13, x_2, x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
lean_inc(x_6);
x_11 = lean_hashset_mk_idx(x_6, x_10);
x_12 = lean_array_uget(x_5, x_11);
x_13 = l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_array_uset(x_5, x_11, x_16);
x_18 = lean_nat_dec_le(x_15, x_6);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Lean_HashSetImp_expand___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__3(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_5, x_11, x_20);
lean_inc(x_2);
x_22 = l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(x_12, x_2, x_2);
lean_dec(x_2);
x_23 = lean_array_uset(x_21, x_11, x_22);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_array_get_size(x_25);
x_27 = lean_ptr_addr(x_2);
x_28 = lean_usize_to_uint64(x_27);
x_29 = 11;
x_30 = lean_uint64_mix_hash(x_28, x_29);
lean_inc(x_26);
x_31 = lean_hashset_mk_idx(x_26, x_30);
x_32 = lean_array_uget(x_25, x_31);
x_33 = l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_24, x_34);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_array_uset(x_25, x_31, x_36);
x_38 = lean_nat_dec_le(x_35, x_26);
lean_dec(x_26);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_HashSetImp_expand___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__3(x_35, x_37);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = lean_array_uset(x_25, x_31, x_41);
lean_inc(x_2);
x_43 = l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(x_32, x_2, x_2);
lean_dec(x_2);
x_44 = lean_array_uset(x_42, x_31, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_to_uint64(x_5);
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_hashset_mk_idx(x_4, x_8);
x_10 = lean_array_uget(x_3, x_9);
x_11 = l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(x_2, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_9 = l_Lean_HashSetImp_insert___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__1(x_7, x_1);
lean_inc(x_8);
lean_inc(x_9);
lean_ctor_set(x_5, 0, x_9);
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_inc(x_10);
x_12 = l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_8, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_apply_2(x_3, x_10, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_3);
x_19 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_17, x_2, x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_18, x_20, x_21);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
lean_inc(x_3);
x_25 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_23, x_2, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_24, x_26, x_27);
return x_28;
}
case 7:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_dec(x_1);
lean_inc(x_3);
x_31 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_29, x_2, x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_30, x_32, x_33);
return x_34;
}
case 8:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_8);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec(x_1);
lean_inc(x_3);
x_38 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_35, x_2, x_5);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_3);
x_41 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_36, x_39, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_37, x_42, x_43);
return x_44;
}
case 10:
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
lean_dec(x_8);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_45, x_2, x_5);
return x_46;
}
case 11:
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_47, x_2, x_5);
return x_48;
}
default: 
{
lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_5);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_5, 0);
x_51 = lean_ctor_get(x_5, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_5);
lean_inc(x_1);
x_52 = l_Lean_HashSetImp_insert___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__1(x_50, x_1);
lean_inc(x_51);
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
lean_inc(x_54);
x_56 = l_Lean_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_51, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_apply_2(x_3, x_54, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
case 5:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
lean_dec(x_51);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
lean_inc(x_3);
x_63 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_61, x_2, x_53);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_62, x_64, x_65);
return x_66;
}
case 6:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_52);
lean_dec(x_51);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
lean_dec(x_1);
lean_inc(x_3);
x_69 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_67, x_2, x_53);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_68, x_70, x_71);
return x_72;
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_52);
lean_dec(x_51);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_dec(x_1);
lean_inc(x_3);
x_75 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_73, x_2, x_53);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_74, x_76, x_77);
return x_78;
}
case 8:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_52);
lean_dec(x_51);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
lean_dec(x_1);
lean_inc(x_3);
x_82 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_79, x_2, x_53);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_3);
x_85 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_80, x_83, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_81, x_86, x_87);
return x_88;
}
case 10:
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_52);
lean_dec(x_51);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_dec(x_1);
x_90 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_89, x_2, x_53);
return x_90;
}
case 11:
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_52);
lean_dec(x_51);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_91, x_2, x_53);
return x_92;
}
default: 
{
lean_object* x_93; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_53);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8(x_5, x_2);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1(x_2, x_3, x_1, x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold_visit___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_Expr_FoldConstsImpl_fold_visit___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_fold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_fold___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1;
x_2 = l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_1, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FoldConstsImpl_foldUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstants___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstants___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstants___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstants(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Expr_getUsedConstants___closed__2;
x_3 = l_Lean_Expr_getUsedConstants___closed__1;
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_2, x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_getUsedConstantsAsSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_getUsedConstantsAsSet___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Expr_getUsedConstantsAsSet___closed__1;
x_3 = l_Lean_NameSet_empty;
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1;
x_5 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_2, x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_5, x_3, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_NameSet_append___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_getUsedConstantsAsSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_ConstantInfo_type(x_1);
x_3 = l_Lean_Expr_getUsedConstantsAsSet(x_2);
lean_inc(x_1);
x_4 = l_Lean_ConstantInfo_value_x3f(x_1);
if (lean_obj_tag(x_4) == 0)
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Expr_getUsedConstantsAsSet(x_6);
x_8 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_9 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_10 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_8, x_9, x_3, x_7);
return x_10;
}
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_12);
x_14 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_15 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_16 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_14, x_15, x_3, x_13);
return x_16;
}
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_NameSet_empty;
x_21 = lean_box(0);
x_22 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_20, x_19, x_21);
x_23 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_24 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_25 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_23, x_24, x_3, x_22);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_RBTree_ofList___at_Lean_ConstantInfo_getUsedConstantsAsSet___spec__1(x_27);
x_29 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_30 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_31 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_29, x_30, x_3, x_28);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_32 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_33 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_34 = l_Lean_NameSet_empty;
x_35 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_32, x_33, x_3, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_Expr_getUsedConstantsAsSet(x_36);
x_38 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1;
x_39 = l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2;
x_40 = l_Lean_RBNode_fold___at_Lean_RBMap_mergeBy___spec__1___rarg(x_38, x_39, x_3, x_37);
return x_40;
}
}
}
LEAN_EXPORT uint32_t l_Lean_getMaxHeight___lambda__1(lean_object* x_1, lean_object* x_2, uint32_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 2)
{
uint32_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint32(x_7, 0);
lean_dec(x_7);
x_9 = lean_uint32_dec_lt(x_3, x_8);
if (x_9 == 0)
{
return x_3;
}
else
{
return x_8;
}
}
else
{
lean_dec(x_7);
return x_3;
}
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
static lean_object* _init_l_Lean_getMaxHeight___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_getMaxHeight___lambda__1___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1;
x_5 = l_Lean_getMaxHeight___boxed__const__1;
x_6 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_3, x_2, x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMaxHeight___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_5 = l_Lean_getMaxHeight___lambda__1(x_1, x_2, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_State_visited___default___closed__1);
l_Lean_Expr_FoldConstsImpl_State_visited___default = _init_l_Lean_Expr_FoldConstsImpl_State_visited___default();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_State_visited___default);
l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default___closed__1);
l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default = _init_l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_State_visitedConsts___default);
l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1 = _init_l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_FoldConstsImpl_foldUnsafe___rarg___closed__1);
l_Lean_Expr_getUsedConstants___closed__1 = _init_l_Lean_Expr_getUsedConstants___closed__1();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__1);
l_Lean_Expr_getUsedConstants___closed__2 = _init_l_Lean_Expr_getUsedConstants___closed__2();
lean_mark_persistent(l_Lean_Expr_getUsedConstants___closed__2);
l_Lean_Expr_getUsedConstantsAsSet___closed__1 = _init_l_Lean_Expr_getUsedConstantsAsSet___closed__1();
lean_mark_persistent(l_Lean_Expr_getUsedConstantsAsSet___closed__1);
l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1 = _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1();
lean_mark_persistent(l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__1);
l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2 = _init_l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2();
lean_mark_persistent(l_Lean_ConstantInfo_getUsedConstantsAsSet___closed__2);
l_Lean_getMaxHeight___boxed__const__1 = _init_l_Lean_getMaxHeight___boxed__const__1();
lean_mark_persistent(l_Lean_getMaxHeight___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
