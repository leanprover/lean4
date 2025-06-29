// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: Init.Data.Hashable Std.Data.HashSet.Basic Std.Data.HashMap.Basic
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
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_PtrSet_insert___redArg___closed__1;
static lean_object* l_Lean_PtrSet_insert___redArg___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object* x_1) {
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
x_2 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_instHashablePtr___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object* x_1, lean_object* x_2) {
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
x_2 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqPtr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrSet___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkPtrSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PtrSet_insert___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PtrSet_insert___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashablePtr___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_PtrSet_insert___redArg___closed__0;
x_6 = lean_array_get_size(x_4);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_4, x_21);
lean_inc(x_22);
lean_inc(x_2);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_5, x_2, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_22);
x_31 = lean_array_uset(x_4, x_21, x_30);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_mul(x_29, x_32);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = lean_array_get_size(x_31);
x_37 = lean_nat_dec_le(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_PtrSet_insert___redArg___closed__1;
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_38, x_31);
lean_ctor_set(x_1, 1, x_39);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_3, x_41);
lean_dec(x_3);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_22);
x_44 = lean_array_uset(x_4, x_21, x_43);
x_45 = lean_unsigned_to_nat(4u);
x_46 = lean_nat_mul(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lean_PtrSet_insert___redArg___closed__1;
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_51, x_44);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Lean_PtrSet_insert___redArg___closed__0;
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_3);
x_9 = lean_usize_to_uint64(x_8);
x_10 = 11;
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_5, x_22);
lean_inc(x_23);
lean_inc(x_3);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_6, x_3, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_26 = lean_ctor_get(x_2, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_4, x_29);
lean_dec(x_4);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_23);
x_32 = lean_array_uset(x_5, x_22, x_31);
x_33 = lean_unsigned_to_nat(4u);
x_34 = lean_nat_mul(x_30, x_33);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_div(x_34, x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_32);
x_38 = lean_nat_dec_le(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_PtrSet_insert___redArg___closed__1;
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_39, x_32);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_4, x_42);
lean_dec(x_4);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_23);
x_45 = lean_array_uset(x_5, x_22, x_44);
x_46 = lean_unsigned_to_nat(4u);
x_47 = lean_nat_mul(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Lean_PtrSet_insert___redArg___closed__1;
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_52, x_45);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = 11;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_2, x_21);
return x_22;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PtrSet_insert___redArg___closed__0;
x_6 = lean_array_get_size(x_4);
x_7 = lean_ptr_addr(x_3);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_4, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_5, x_3, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrSet_contains___redArg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PtrSet_contains(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(4u);
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkPtrMap___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkPtrMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_PtrSet_insert___redArg___closed__0;
x_8 = lean_array_get_size(x_6);
x_9 = lean_ptr_addr(x_2);
x_10 = lean_usize_to_uint64(x_9);
x_11 = 11;
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_6, x_23);
lean_inc(x_24);
lean_inc(x_2);
x_25 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_7, x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_24);
x_29 = lean_array_uset(x_6, x_23, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_mul(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_PtrSet_insert___redArg___closed__1;
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_36, x_29);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_6, x_23, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_7, x_2, x_3, x_24);
x_41 = lean_array_uset(x_39, x_23, x_40);
lean_ctor_set(x_1, 1, x_41);
return x_1;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_44 = l_Lean_PtrSet_insert___redArg___closed__0;
x_45 = lean_array_get_size(x_43);
x_46 = lean_ptr_addr(x_2);
x_47 = lean_usize_to_uint64(x_46);
x_48 = 11;
x_49 = lean_uint64_mix_hash(x_47, x_48);
x_50 = 32;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = 16;
x_54 = lean_uint64_shift_right(x_52, x_53);
x_55 = lean_uint64_xor(x_52, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_58 = 1;
x_59 = lean_usize_sub(x_57, x_58);
x_60 = lean_usize_land(x_56, x_59);
x_61 = lean_array_uget(x_43, x_60);
lean_inc(x_61);
lean_inc(x_2);
x_62 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_44, x_2, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_42, x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_61);
x_66 = lean_array_uset(x_43, x_60, x_65);
x_67 = lean_unsigned_to_nat(4u);
x_68 = lean_nat_mul(x_64, x_67);
x_69 = lean_unsigned_to_nat(3u);
x_70 = lean_nat_div(x_68, x_69);
lean_dec(x_68);
x_71 = lean_array_get_size(x_66);
x_72 = lean_nat_dec_le(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = l_Lean_PtrSet_insert___redArg___closed__1;
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_73, x_66);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_64);
lean_ctor_set(x_76, 1, x_66);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_box(0);
x_78 = lean_array_uset(x_43, x_60, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_44, x_2, x_3, x_61);
x_80 = lean_array_uset(x_78, x_60, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_42);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_PtrSet_insert___redArg___closed__0;
x_10 = lean_array_get_size(x_8);
x_11 = lean_ptr_addr(x_4);
x_12 = lean_usize_to_uint64(x_11);
x_13 = 11;
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = 32;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = 16;
x_19 = lean_uint64_shift_right(x_17, x_18);
x_20 = lean_uint64_xor(x_17, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_23 = 1;
x_24 = lean_usize_sub(x_22, x_23);
x_25 = lean_usize_land(x_21, x_24);
x_26 = lean_array_uget(x_8, x_25);
lean_inc(x_26);
lean_inc(x_4);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_9, x_4, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_8, x_25, x_30);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_nat_mul(x_29, x_32);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = lean_array_get_size(x_31);
x_37 = lean_nat_dec_le(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_PtrSet_insert___redArg___closed__1;
x_39 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_38, x_31);
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_box(0);
x_41 = lean_array_uset(x_8, x_25, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_9, x_4, x_5, x_26);
x_43 = lean_array_uset(x_41, x_25, x_42);
lean_ctor_set(x_3, 1, x_43);
return x_3;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = l_Lean_PtrSet_insert___redArg___closed__0;
x_47 = lean_array_get_size(x_45);
x_48 = lean_ptr_addr(x_4);
x_49 = lean_usize_to_uint64(x_48);
x_50 = 11;
x_51 = lean_uint64_mix_hash(x_49, x_50);
x_52 = 32;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = 16;
x_56 = lean_uint64_shift_right(x_54, x_55);
x_57 = lean_uint64_xor(x_54, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_60 = 1;
x_61 = lean_usize_sub(x_59, x_60);
x_62 = lean_usize_land(x_58, x_61);
x_63 = lean_array_uget(x_45, x_62);
lean_inc(x_63);
lean_inc(x_4);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_46, x_4, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_44, x_65);
lean_dec(x_44);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_5);
lean_ctor_set(x_67, 2, x_63);
x_68 = lean_array_uset(x_45, x_62, x_67);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_mul(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Lean_PtrSet_insert___redArg___closed__1;
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_75, x_68);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_68);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_box(0);
x_80 = lean_array_uset(x_45, x_62, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_46, x_4, x_5, x_63);
x_82 = lean_array_uset(x_80, x_62, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_44);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = 11;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_4, x_2, x_21);
return x_22;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PtrSet_insert___redArg___closed__0;
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_4);
x_9 = lean_usize_to_uint64(x_8);
x_10 = 11;
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_6, x_4, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PtrMap_contains___redArg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_PtrMap_contains(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PtrSet_insert___redArg___closed__0;
x_5 = lean_array_get_size(x_3);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_to_uint64(x_6);
x_8 = 11;
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_3, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_4, x_2, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_PtrSet_insert___redArg___closed__0;
x_7 = lean_array_get_size(x_5);
x_8 = lean_ptr_addr(x_4);
x_9 = lean_usize_to_uint64(x_8);
x_10 = 11;
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_5, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_6, x_4, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PtrMap_find_x3f___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PtrMap_find_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PtrSet_insert___redArg___closed__0 = _init_l_Lean_PtrSet_insert___redArg___closed__0();
lean_mark_persistent(l_Lean_PtrSet_insert___redArg___closed__0);
l_Lean_PtrSet_insert___redArg___closed__1 = _init_l_Lean_PtrSet_insert___redArg___closed__1();
lean_mark_persistent(l_Lean_PtrSet_insert___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
