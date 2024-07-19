// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Lean.Expr Lean.Util.PtrSet
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Expr_ReplaceImpl_cache___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Expr_ReplaceImpl_cache___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_is_exclusive_obj(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Expr_ReplaceImpl_cache___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_ReplaceImpl_cache___spec__5___at_Lean_Expr_ReplaceImpl_cache___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_instBEqPtr___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_ReplaceImpl_cache___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instHashablePtr___rarg___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_ReplaceImpl_cache___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_ReplaceImpl_cache___spec__5___at_Lean_Expr_ReplaceImpl_cache___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_hashmap_mk_idx(x_6, x_10);
x_12 = lean_array_uget(x_1, x_11);
lean_ctor_set(x_2, 2, x_12);
x_13 = lean_array_uset(x_1, x_11, x_2);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_ptr_addr(x_15);
x_20 = lean_usize_to_uint64(x_19);
x_21 = 11;
x_22 = lean_uint64_mix_hash(x_20, x_21);
x_23 = lean_hashmap_mk_idx(x_18, x_22);
x_24 = lean_array_uget(x_1, x_23);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_uset(x_1, x_23, x_25);
x_1 = x_26;
x_2 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Expr_ReplaceImpl_cache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Expr_ReplaceImpl_cache___spec__5___at_Lean_Expr_ReplaceImpl_cache___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Expr_ReplaceImpl_cache___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Expr_ReplaceImpl_cache___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_ptr_addr(x_1);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = lean_ptr_addr(x_13);
x_17 = lean_ptr_addr(x_1);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(x_1, x_2, x_15);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_15);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Expr_ReplaceImpl_cache___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ptr_addr(x_2);
x_9 = lean_usize_to_uint64(x_8);
x_10 = 11;
x_11 = lean_uint64_mix_hash(x_9, x_10);
lean_inc(x_7);
x_12 = lean_hashmap_mk_idx(x_7, x_11);
x_13 = lean_array_uget(x_6, x_12);
x_14 = l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_13);
x_18 = lean_array_uset(x_6, x_12, x_17);
x_19 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_16);
x_20 = lean_nat_dec_le(x_19, x_7);
lean_dec(x_7);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_1);
x_21 = l_Lean_HashMapImp_expand___at_Lean_Expr_ReplaceImpl_cache___spec__3(x_16, x_18);
return x_21;
}
else
{
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_array_uset(x_6, x_12, x_22);
x_24 = l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(x_2, x_3, x_13);
x_25 = lean_array_uset(x_23, x_12, x_24);
lean_ctor_set(x_1, 1, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = lean_array_get_size(x_27);
x_29 = lean_ptr_addr(x_2);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
lean_inc(x_28);
x_33 = lean_hashmap_mk_idx(x_28, x_32);
x_34 = lean_array_uget(x_27, x_33);
x_35 = l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_26, x_36);
lean_dec(x_26);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_34);
x_39 = lean_array_uset(x_27, x_33, x_38);
x_40 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_37);
x_41 = lean_nat_dec_le(x_40, x_28);
lean_dec(x_28);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_HashMapImp_expand___at_Lean_Expr_ReplaceImpl_cache___spec__3(x_37, x_39);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_28);
x_44 = lean_box(0);
x_45 = lean_array_uset(x_27, x_33, x_44);
x_46 = l_Lean_AssocList_replace___at_Lean_Expr_ReplaceImpl_cache___spec__7(x_2, x_3, x_34);
x_47 = lean_array_uset(x_45, x_33, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = l_Lean_HashMap_insert___at_Lean_Expr_ReplaceImpl_cache___spec__1(x_4, x_1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Expr_ReplaceImpl_cache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_cache___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_8);
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_16 = lean_ptr_addr(x_10);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_18 = l_Lean_Expr_app___override(x_10, x_13);
x_19 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_18, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_app___override(x_10, x_13);
x_24 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_23, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_inc(x_2);
x_25 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_2, x_14);
return x_25;
}
}
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_27);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_27, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_28);
x_33 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_28, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_36 = l_Lean_Expr_lam___override(x_26, x_27, x_28, x_29);
x_37 = lean_ptr_addr(x_27);
lean_dec(x_27);
x_38 = lean_ptr_addr(x_31);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_28);
x_40 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_41 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_40, x_35);
return x_41;
}
else
{
size_t x_42; size_t x_43; uint8_t x_44; 
x_42 = lean_ptr_addr(x_28);
lean_dec(x_28);
x_43 = lean_ptr_addr(x_34);
x_44 = lean_usize_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
x_45 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_46 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_45, x_35);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_29, x_29);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_36);
x_48 = l_Lean_Expr_lam___override(x_26, x_31, x_34, x_29);
x_49 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_48, x_35);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_26);
x_50 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_36, x_35);
return x_50;
}
}
}
}
case 7:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; uint8_t x_64; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_52, x_5);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_53);
x_58 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_53, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_61 = l_Lean_Expr_forallE___override(x_51, x_52, x_53, x_54);
x_62 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_63 = lean_ptr_addr(x_56);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_53);
x_65 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_66 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_65, x_60);
return x_66;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; 
x_67 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_68 = lean_ptr_addr(x_59);
x_69 = lean_usize_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_61);
x_70 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_71 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_70, x_60);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_54, x_54);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
x_73 = l_Lean_Expr_forallE___override(x_51, x_56, x_59, x_54);
x_74 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_73, x_60);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_51);
x_75 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_61, x_60);
return x_75;
}
}
}
}
case 8:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 3);
lean_inc(x_79);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_77);
lean_inc(x_1);
x_81 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_77, x_5);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_78);
lean_inc(x_1);
x_84 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_78, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_79);
x_87 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_79, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ptr_addr(x_77);
lean_dec(x_77);
x_91 = lean_ptr_addr(x_82);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
lean_dec(x_78);
x_93 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_94 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_93, x_89);
return x_94;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_78);
lean_dec(x_78);
x_96 = lean_ptr_addr(x_85);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_79);
x_98 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_99 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_98, x_89);
return x_99;
}
else
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_101 = lean_ptr_addr(x_88);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_Expr_letE___override(x_76, x_82, x_85, x_88, x_80);
x_104 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_103, x_89);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_76);
lean_inc(x_2);
x_105 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_2, x_89);
return x_105;
}
}
}
}
case 10:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; uint8_t x_113; 
x_106 = lean_ctor_get(x_2, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 1);
lean_inc(x_107);
lean_inc(x_107);
x_108 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_107, x_5);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_112 = lean_ptr_addr(x_109);
x_113 = lean_usize_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Expr_mdata___override(x_106, x_109);
x_115 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_114, x_110);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_106);
lean_inc(x_2);
x_116 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_2, x_110);
return x_116;
}
}
case 11:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; size_t x_123; size_t x_124; uint8_t x_125; 
x_117 = lean_ctor_get(x_2, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_2, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_2, 2);
lean_inc(x_119);
lean_inc(x_119);
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_119, x_5);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ptr_addr(x_119);
lean_dec(x_119);
x_124 = lean_ptr_addr(x_121);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Lean_Expr_proj___override(x_117, x_118, x_121);
x_127 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_126, x_122);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_117);
lean_inc(x_2);
x_128 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_2, x_122);
return x_128;
}
}
default: 
{
lean_object* x_129; 
lean_dec(x_1);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_2);
lean_ctor_set(x_129, 1, x_5);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_1);
x_130 = lean_ctor_get(x_6, 0);
lean_inc(x_130);
lean_dec(x_6);
x_131 = l_Lean_Expr_ReplaceImpl_cache(x_2, x_3, x_130, x_5);
return x_131;
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_is_exclusive_obj(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1;
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2;
lean_inc(x_2);
x_7 = l_Lean_HashMapImp_find_x3f___rarg(x_5, x_6, x_3, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1(x_1, x_2, x_4, x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1(x_1, x_2, x_4, x_12, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1;
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_Expr_replaceNoCache(x_1, x_4);
lean_inc(x_5);
x_7 = l_Lean_Expr_replaceNoCache(x_1, x_5);
x_8 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_9 = lean_ptr_addr(x_6);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Expr_app___override(x_6, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_13 = lean_ptr_addr(x_7);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = l_Lean_Expr_app___override(x_6, x_7);
return x_15;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_2;
}
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_17);
lean_inc(x_1);
x_20 = l_Lean_Expr_replaceNoCache(x_1, x_17);
lean_inc(x_18);
x_21 = l_Lean_Expr_replaceNoCache(x_1, x_18);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_22 = l_Lean_Expr_lam___override(x_16, x_17, x_18, x_19);
x_23 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_24 = lean_ptr_addr(x_20);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_18);
x_26 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_26;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_28 = lean_ptr_addr(x_21);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
x_30 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_19, x_19);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
x_32 = l_Lean_Expr_lam___override(x_16, x_20, x_21, x_19);
return x_32;
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
return x_22;
}
}
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; uint8_t x_42; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_34);
lean_inc(x_1);
x_37 = l_Lean_Expr_replaceNoCache(x_1, x_34);
lean_inc(x_35);
x_38 = l_Lean_Expr_replaceNoCache(x_1, x_35);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_39 = l_Lean_Expr_forallE___override(x_33, x_34, x_35, x_36);
x_40 = lean_ptr_addr(x_34);
lean_dec(x_34);
x_41 = lean_ptr_addr(x_37);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_35);
x_43 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_43;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_35);
lean_dec(x_35);
x_45 = lean_ptr_addr(x_38);
x_46 = lean_usize_dec_eq(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
x_47 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_412_(x_36, x_36);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_39);
x_49 = l_Lean_Expr_forallE___override(x_33, x_37, x_38, x_36);
return x_49;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_33);
return x_39;
}
}
}
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_51);
lean_inc(x_1);
x_55 = l_Lean_Expr_replaceNoCache(x_1, x_51);
lean_inc(x_52);
lean_inc(x_1);
x_56 = l_Lean_Expr_replaceNoCache(x_1, x_52);
lean_inc(x_53);
x_57 = l_Lean_Expr_replaceNoCache(x_1, x_53);
x_58 = lean_ptr_addr(x_51);
lean_dec(x_51);
x_59 = lean_ptr_addr(x_55);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_61 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_61;
}
else
{
size_t x_62; size_t x_63; uint8_t x_64; 
x_62 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_63 = lean_ptr_addr(x_56);
x_64 = lean_usize_dec_eq(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_53);
lean_dec(x_2);
x_65 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_65;
}
else
{
size_t x_66; size_t x_67; uint8_t x_68; 
x_66 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_67 = lean_ptr_addr(x_57);
x_68 = lean_usize_dec_eq(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = l_Lean_Expr_letE___override(x_50, x_55, x_56, x_57, x_54);
return x_69;
}
else
{
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_50);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
lean_inc(x_71);
x_72 = l_Lean_Expr_replaceNoCache(x_1, x_71);
x_73 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_74 = lean_ptr_addr(x_72);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = l_Lean_Expr_mdata___override(x_70, x_72);
return x_76;
}
else
{
lean_dec(x_72);
lean_dec(x_70);
return x_2;
}
}
case 11:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_inc(x_79);
x_80 = l_Lean_Expr_replaceNoCache(x_1, x_79);
x_81 = lean_ptr_addr(x_79);
lean_dec(x_79);
x_82 = lean_ptr_addr(x_80);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_2);
x_84 = l_Lean_Expr_proj___override(x_77, x_78, x_80);
return x_84;
}
else
{
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
return x_2;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
return x_85;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ReplaceExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__2);
l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafe___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
