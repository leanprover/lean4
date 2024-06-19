// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: Init.Data.Hashable Lean.Data.HashSet
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_insert___spec__2(lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___rarg(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_contains___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___rarg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___rarg(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_ptr_addr(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = 11;
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___rarg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashablePtr___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqPtr___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkPtrSet___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at_Lean_mkPtrSet___spec__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrSet___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_PtrSet_insert___spec__5___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at_Lean_PtrSet_insert___spec__5___at_Lean_PtrSet_insert___spec__6___rarg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at_Lean_PtrSet_insert___spec__4___rarg(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(x_7, x_2, x_3);
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
x_17 = l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(x_13, x_2, x_3);
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
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_13 = l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg(x_2, x_12);
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
x_19 = l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3___rarg(x_15, x_17);
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
x_22 = l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(x_12, x_2, x_2);
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
x_33 = l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg(x_2, x_32);
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
x_39 = l_Lean_HashSetImp_expand___at_Lean_PtrSet_insert___spec__3___rarg(x_35, x_37);
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
x_43 = l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(x_32, x_2, x_2);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashSetImp_insert___at_Lean_PtrSet_insert___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PtrSet_insert___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_PtrSet_insert___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at_Lean_PtrSet_insert___spec__7___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_contains___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg(x_2, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PtrSet_contains___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_PtrSet_contains___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at_Lean_PtrSet_contains___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrSet_contains___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_HashSet(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_HashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
