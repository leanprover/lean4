// Lean compiler output
// Module: Lean.Util.FindExpr
// Imports: Init Lean.Expr Lean.Util.PtrSet
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
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1;
size_t lean_ptr_addr(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FindImpl_checkVisited___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FindImpl_checkVisited___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Expr_FindImpl_checkVisited___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Expr_FindImpl_checkVisited___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FindImpl_checkVisited___spec__5___at_Lean_Expr_FindImpl_checkVisited___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lambda__1(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FindImpl_checkVisited___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_FindImpl_checkVisited___spec__5___at_Lean_Expr_FindImpl_checkVisited___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FindImpl_checkVisited___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_Expr_FindImpl_checkVisited___spec__5___at_Lean_Expr_FindImpl_checkVisited___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_Expr_FindImpl_checkVisited___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lean_Expr_FindImpl_checkVisited___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ptr_addr(x_6);
x_9 = lean_ptr_addr(x_2);
x_10 = lean_usize_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(x_7, x_2, x_3);
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
x_14 = lean_ptr_addr(x_12);
x_15 = lean_ptr_addr(x_2);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(x_13, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_Expr_FindImpl_checkVisited___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_13 = l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(x_2, x_12);
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
x_19 = l_Lean_HashSetImp_expand___at_Lean_Expr_FindImpl_checkVisited___spec__3(x_15, x_17);
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
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_inc(x_2);
x_20 = l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(x_12, x_2, x_2);
lean_dec(x_2);
x_21 = lean_array_uset(x_5, x_11, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_ptr_addr(x_2);
x_26 = lean_usize_to_uint64(x_25);
x_27 = 11;
x_28 = lean_uint64_mix_hash(x_26, x_27);
lean_inc(x_24);
x_29 = lean_hashset_mk_idx(x_24, x_28);
x_30 = lean_array_uget(x_23, x_29);
x_31 = l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(x_2, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_22, x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_array_uset(x_23, x_29, x_34);
x_36 = lean_nat_dec_le(x_33, x_24);
lean_dec(x_24);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_HashSetImp_expand___at_Lean_Expr_FindImpl_checkVisited___spec__3(x_33, x_35);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_24);
lean_inc(x_2);
x_39 = l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(x_30, x_2, x_2);
lean_dec(x_2);
x_40 = lean_array_uset(x_23, x_29, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_to_uint64(x_5);
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_hashset_mk_idx(x_4, x_8);
x_10 = lean_array_uget(x_3, x_9);
lean_dec(x_3);
x_11 = l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(x_2, x_10);
lean_dec(x_10);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_HashSetImp_insert___at_Lean_Expr_FindImpl_checkVisited___spec__1(x_3, x_1);
x_5 = l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_Expr_FindImpl_checkVisited___lambda__1(x_1, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Expr_FindImpl_checkVisited___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_Expr_FindImpl_checkVisited___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_checkVisited___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_FindImpl_checkVisited___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_166; 
lean_inc(x_2);
lean_inc(x_3);
x_166 = l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(x_3, x_2);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_box(0);
lean_inc(x_2);
x_168 = l_Lean_Expr_FindImpl_checkVisited___lambda__1(x_2, x_167, x_3);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_4 = x_169;
x_5 = x_170;
goto block_165;
}
else
{
lean_object* x_171; 
x_171 = lean_box(0);
x_4 = x_171;
x_5 = x_3;
goto block_165;
}
block_165:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_10 = lean_apply_1(x_1, x_2);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_free_object(x_4);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_12, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_25 = x_15;
} else {
 lean_dec_ref(x_15);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_28, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_2 = x_29;
x_3 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_30, 0, x_38);
return x_30;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
case 7:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
lean_dec(x_2);
lean_inc(x_1);
x_46 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_44, x_5);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_2 = x_45;
x_3 = x_48;
goto _start;
}
else
{
uint8_t x_50; 
lean_dec(x_45);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_46;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_46, 0, x_54);
return x_46;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_57 = x_47;
} else {
 lean_dec_ref(x_47);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
}
case 8:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_dec(x_2);
lean_inc(x_1);
x_63 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_60, x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_1);
x_66 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_61, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_2 = x_62;
x_3 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_62);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_66, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_66;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_66, 0, x_74);
return x_66;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_dec(x_66);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_63);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_63, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_64);
if (x_82 == 0)
{
return x_63;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_64, 0);
lean_inc(x_83);
lean_dec(x_64);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_63, 0, x_84);
return x_63;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_63, 1);
lean_inc(x_85);
lean_dec(x_63);
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_87 = x_64;
} else {
 lean_dec_ref(x_64);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
}
case 10:
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
lean_dec(x_2);
x_2 = x_90;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_2, 2);
lean_inc(x_92);
lean_dec(x_2);
x_2 = x_92;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_97 = lean_apply_1(x_1, x_2);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_2, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
lean_dec(x_2);
lean_inc(x_1);
x_101 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_99, x_5);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_2 = x_100;
x_3 = x_103;
goto _start;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
lean_dec(x_1);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_106 = x_101;
} else {
 lean_dec_ref(x_101);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_108 = x_102;
} else {
 lean_dec_ref(x_102);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_107);
if (lean_is_scalar(x_106)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_106;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_105);
return x_110;
}
}
case 6:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 2);
lean_inc(x_112);
lean_dec(x_2);
lean_inc(x_1);
x_113 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_111, x_5);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_2 = x_112;
x_3 = x_115;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_112);
lean_dec(x_1);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_118 = x_113;
} else {
 lean_dec_ref(x_113);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_114, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
if (lean_is_scalar(x_118)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_118;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
case 7:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 2);
lean_inc(x_124);
lean_dec(x_2);
lean_inc(x_1);
x_125 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_123, x_5);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_2 = x_124;
x_3 = x_127;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_124);
lean_dec(x_1);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
case 8:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 3);
lean_inc(x_137);
lean_dec(x_2);
lean_inc(x_1);
x_138 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_135, x_5);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_1);
x_141 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_136, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_2 = x_137;
x_3 = x_143;
goto _start;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_dec(x_1);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_146 = x_141;
} else {
 lean_dec_ref(x_141);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
if (lean_is_scalar(x_146)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_146;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_145);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_1);
x_151 = lean_ctor_get(x_138, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_152 = x_138;
} else {
 lean_dec_ref(x_138);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_139, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_154 = x_139;
} else {
 lean_dec_ref(x_139);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
if (lean_is_scalar(x_152)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_152;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_151);
return x_156;
}
}
case 10:
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_dec(x_2);
x_2 = x_157;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_2, 2);
lean_inc(x_159);
lean_dec(x_2);
x_2 = x_159;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_5);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_1);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_2);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_5);
return x_164;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1;
x_4 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_occurs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_occurs___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_occurs___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_occurs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_occurs(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_FindStep_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_FindStep_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_FindStep_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_FindStep_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_FindStep_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindStep_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindStep_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_5, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_17 = x_7;
} else {
 lean_dec_ref(x_7);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(1, 1, 0);
} else {
 x_18 = x_17;
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_3);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_144; 
lean_inc(x_2);
lean_inc(x_3);
x_144 = l_Lean_HashSetImp_contains___at_Lean_Expr_FindImpl_checkVisited___spec__8(x_3, x_2);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_box(0);
lean_inc(x_2);
x_146 = l_Lean_Expr_FindImpl_checkVisited___lambda__1(x_2, x_145, x_3);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_4 = x_147;
x_5 = x_148;
goto block_143;
}
else
{
lean_object* x_149; 
x_149 = lean_box(0);
x_4 = x_149;
x_5 = x_3;
goto block_143;
}
block_143:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_10 = lean_apply_1(x_1, x_2);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
switch (x_11) {
case 0:
{
lean_object* x_12; 
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
case 1:
{
lean_free_object(x_4);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_2, x_5);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_14, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_2 = x_15;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
case 7:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_1);
x_32 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_30, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_2 = x_31;
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_31);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_43 = x_33;
} else {
 lean_dec_ref(x_33);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 3);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_1);
x_49 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_46, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_47, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_2 = x_48;
x_3 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_48);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_52, 0, x_60);
return x_52;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_49, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_50);
if (x_68 == 0)
{
return x_49;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
lean_dec(x_50);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_49, 0, x_70);
return x_49;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_49, 1);
lean_inc(x_71);
lean_dec(x_49);
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_73 = x_50;
} else {
 lean_dec_ref(x_50);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
case 10:
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
lean_dec(x_2);
x_2 = x_76;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
lean_dec(x_2);
x_2 = x_78;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_5);
return x_81;
}
}
}
default: 
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_5);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_84 = lean_apply_1(x_1, x_2);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
switch (x_85) {
case 0:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_2);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_5);
return x_87;
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_88; 
x_88 = l_Lean_Expr_FindExtImpl_findM_x3f_visitApp(x_1, x_2, x_5);
return x_88;
}
case 6:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
lean_dec(x_2);
lean_inc(x_1);
x_91 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_89, x_5);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_2 = x_90;
x_3 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
lean_dec(x_1);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 2);
lean_inc(x_102);
lean_dec(x_2);
lean_inc(x_1);
x_103 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_101, x_5);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_2 = x_102;
x_3 = x_105;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_102);
lean_dec(x_1);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_108 = x_103;
} else {
 lean_dec_ref(x_103);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_109);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
}
case 8:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_2, 3);
lean_inc(x_115);
lean_dec(x_2);
lean_inc(x_1);
x_116 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_113, x_5);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_1);
x_119 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_114, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_2 = x_115;
x_3 = x_121;
goto _start;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
lean_dec(x_1);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 x_126 = x_120;
} else {
 lean_dec_ref(x_120);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_123);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_129 = lean_ctor_get(x_116, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_130 = x_116;
} else {
 lean_dec_ref(x_116);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_132 = x_117;
} else {
 lean_dec_ref(x_117);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
case 10:
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
lean_dec(x_2);
x_2 = x_135;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
lean_dec(x_2);
x_2 = x_137;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_5);
return x_140;
}
}
}
default: 
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
return x_142;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_FindExtImpl_findUnsafe_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1;
x_4 = l_Lean_Expr_FindExtImpl_findM_x3f_visit(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PtrSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1 = _init_l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_FindImpl_checkVisited___lambda__1___closed__1);
l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1 = _init_l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_FindImpl_findUnsafe_x3f___closed__1);
l_Lean_Expr_FindStep_noConfusion___rarg___closed__1 = _init_l_Lean_Expr_FindStep_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_FindStep_noConfusion___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
