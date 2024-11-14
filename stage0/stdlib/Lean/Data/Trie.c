// Lean compiler output
// Module: Lean.Data.Trie
// Imports: Lean.Data.Format
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_List_zipWithTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty(lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Data_Trie_empty___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1(uint8_t, lean_object*);
static lean_object* l_Lean_Data_Trie_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___rarg(lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___rarg(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_values___rarg___closed__1;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop(lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
static lean_object* l_Lean_Data_Trie_findPrefix_go___rarg___closed__1;
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go(lean_object*);
static lean_object* _init_l_Lean_Data_Trie_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Data_Trie_empty___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Data_Trie_instEmptyCollection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Data_Trie_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_3);
x_10 = lean_string_get_byte_fast(x_1, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_upsert_insertEmpty___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_byte_array_get(x_2, x_3);
x_8 = lean_uint8_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_string_utf8_byte_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_apply_1(x_2, x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
lean_inc(x_3);
x_11 = lean_string_get_byte_fast(x_1, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_14 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_13);
x_15 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_string_utf8_byte_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_19 = lean_apply_1(x_2, x_16);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
x_22 = lean_string_get_byte_fast(x_1, x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_25 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_24);
x_26 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_22);
return x_26;
}
}
}
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_string_utf8_byte_size(x_1);
x_32 = lean_nat_dec_lt(x_3, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_33 = lean_apply_1(x_2, x_28);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_4, 0, x_34);
return x_4;
}
else
{
uint8_t x_35; uint8_t x_36; 
lean_inc(x_3);
x_35 = lean_string_get_byte_fast(x_1, x_3);
x_36 = lean_uint8_dec_eq(x_35, x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_4);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_3, x_37);
lean_dec(x_3);
x_39 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_38);
x_40 = lean_box(0);
x_41 = lean_box(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_box(x_35);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_array_mk(x_44);
x_46 = lean_byte_array_mk(x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_mk(x_48);
x_50 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_3, x_51);
lean_dec(x_3);
x_53 = l_Lean_Data_Trie_upsert_loop___rarg(x_1, x_2, x_52, x_30);
lean_ctor_set(x_4, 1, x_53);
return x_4;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
lean_inc(x_54);
lean_dec(x_4);
x_57 = lean_string_utf8_byte_size(x_1);
x_58 = lean_nat_dec_lt(x_3, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
x_59 = lean_apply_1(x_2, x_54);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_55);
return x_61;
}
else
{
uint8_t x_62; uint8_t x_63; 
lean_inc(x_3);
x_62 = lean_string_get_byte_fast(x_1, x_3);
x_63 = lean_uint8_dec_eq(x_62, x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_3, x_64);
lean_dec(x_3);
x_66 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_65);
x_67 = lean_box(0);
x_68 = lean_box(x_55);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box(x_62);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_mk(x_71);
x_73 = lean_byte_array_mk(x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_array_mk(x_75);
x_77 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_77, 0, x_54);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_3, x_78);
lean_dec(x_3);
x_80 = l_Lean_Data_Trie_upsert_loop___rarg(x_1, x_2, x_79, x_56);
x_81 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_81, 0, x_54);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_55);
return x_81;
}
}
}
}
default: 
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_4);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_4, 0);
x_84 = lean_ctor_get(x_4, 1);
x_85 = lean_ctor_get(x_4, 2);
x_86 = lean_string_utf8_byte_size(x_1);
x_87 = lean_nat_dec_lt(x_3, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_88 = lean_apply_1(x_2, x_83);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_4, 0, x_89);
return x_4;
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_inc(x_3);
x_90 = lean_string_get_byte_fast(x_1, x_3);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1(x_90, x_84, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_3, x_93);
lean_dec(x_3);
x_95 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_94);
x_96 = lean_byte_array_push(x_84, x_90);
x_97 = lean_array_push(x_85, x_95);
lean_ctor_set(x_4, 2, x_97);
lean_ctor_set(x_4, 1, x_96);
return x_4;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_3, x_99);
lean_dec(x_3);
x_101 = lean_array_get_size(x_85);
x_102 = lean_nat_dec_lt(x_98, x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_array_fget(x_85, x_98);
x_104 = lean_box(0);
x_105 = lean_array_fset(x_85, x_98, x_104);
x_106 = l_Lean_Data_Trie_upsert_loop___rarg(x_1, x_2, x_100, x_103);
x_107 = lean_array_fset(x_105, x_98, x_106);
lean_dec(x_98);
lean_ctor_set(x_4, 2, x_107);
return x_4;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_4, 0);
x_109 = lean_ctor_get(x_4, 1);
x_110 = lean_ctor_get(x_4, 2);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_4);
x_111 = lean_string_utf8_byte_size(x_1);
x_112 = lean_nat_dec_lt(x_3, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_3);
x_113 = lean_apply_1(x_2, x_108);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; 
lean_inc(x_3);
x_116 = lean_string_get_byte_fast(x_1, x_3);
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1(x_116, x_109, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_3, x_119);
lean_dec(x_3);
x_121 = l_Lean_Data_Trie_upsert_insertEmpty___rarg(x_1, x_2, x_120);
x_122 = lean_byte_array_push(x_109, x_116);
x_123 = lean_array_push(x_110, x_121);
x_124 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_124, 0, x_108);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_123);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
lean_dec(x_118);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_add(x_3, x_126);
lean_dec(x_3);
x_128 = lean_array_get_size(x_110);
x_129 = lean_nat_dec_lt(x_125, x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_2);
x_130 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_130, 0, x_108);
lean_ctor_set(x_130, 1, x_109);
lean_ctor_set(x_130, 2, x_110);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_array_fget(x_110, x_125);
x_132 = lean_box(0);
x_133 = lean_array_fset(x_110, x_125, x_132);
x_134 = l_Lean_Data_Trie_upsert_loop___rarg(x_1, x_2, x_127, x_131);
x_135 = lean_array_fset(x_133, x_125, x_134);
lean_dec(x_125);
x_136 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_136, 0, x_108);
lean_ctor_set(x_136, 1, x_109);
lean_ctor_set(x_136, 2, x_135);
return x_136;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_upsert_loop___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_upsert_loop___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert_loop___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Data_Trie_upsert_loop___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_upsert___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_upsert___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Data_Trie_upsert_loop___rarg(x_2, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_insert___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_insert___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_byte_array_get(x_2, x_3);
x_8 = lean_uint8_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
if (x_6 == 0)
{
return x_4;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
}
case 1:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_string_utf8_byte_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_13; uint8_t x_14; 
lean_dec(x_8);
lean_inc(x_2);
x_13 = lean_string_get_byte_fast(x_1, x_2);
x_14 = lean_uint8_dec_eq(x_13, x_9);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_10;
goto _start;
}
}
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_string_utf8_byte_size(x_1);
x_23 = lean_nat_dec_lt(x_2, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_inc(x_2);
x_24 = lean_string_get_byte_fast(x_1, x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1(x_24, x_20, x_25);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_2);
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_31 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
x_32 = lean_array_get(x_31, x_21, x_28);
lean_dec(x_28);
lean_dec(x_21);
x_2 = x_30;
x_3 = x_32;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_find_x3f_loop___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_find_x3f_loop___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_find_x3f_loop___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Data_Trie_find_x3f_loop___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_find_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_find_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Data_Trie_values_go___rarg(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_values_go___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg(x_1, x_12, x_13, x_14, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_array_push(x_2, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
case 1:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_1 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_array_push(x_2, x_14);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
default: 
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_Lean_Data_Trie_values_go___rarg___lambda__2(x_18, x_19, x_2);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_array_push(x_2, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Data_Trie_values_go___rarg___lambda__2(x_21, x_24, x_23);
lean_dec(x_21);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_values_go___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Data_Trie_values_go___spec__1___rarg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_values_go___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_values_go___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Data_Trie_values___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Data_Trie_values___rarg___closed__1;
x_3 = l_Lean_Data_Trie_values_go___rarg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_values___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_byte_array_get(x_2, x_3);
x_8 = lean_uint8_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Data_Trie_findPrefix_go___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lean_Data_Trie_values___rarg(x_2);
return x_6;
}
else
{
uint8_t x_7; 
lean_inc(x_3);
x_7 = lean_string_get_byte_fast(x_1, x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Data_Trie_findPrefix_go___rarg___closed__1;
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_uint8_dec_eq(x_7, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_3);
x_12 = l_Lean_Data_Trie_findPrefix_go___rarg___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1(x_7, x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_3);
x_20 = l_Lean_Data_Trie_findPrefix_go___rarg___closed__1;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
x_23 = lean_array_get(x_22, x_17, x_21);
lean_dec(x_21);
lean_dec(x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_2 = x_23;
x_3 = x_25;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_findPrefix_go___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_findPrefix_go___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_findPrefix_go___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Data_Trie_findPrefix_go___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_findPrefix___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_findPrefix___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_byte_array_get(x_2, x_3);
x_8 = lean_uint8_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_byte_array_get(x_2, x_3);
x_8 = lean_uint8_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
lean_dec(x_4);
return x_5;
}
}
case 1:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_6) == 0)
{
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_11; uint8_t x_12; 
lean_inc(x_3);
x_11 = lean_string_get_byte_fast(x_1, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_7);
if (x_12 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_2 = x_8;
x_3 = x_14;
goto _start;
}
}
}
else
{
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_6;
}
else
{
uint8_t x_16; uint8_t x_17; 
lean_inc(x_3);
x_16 = lean_string_get_byte_fast(x_1, x_3);
x_17 = lean_uint8_dec_eq(x_16, x_7);
if (x_17 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_2 = x_8;
x_3 = x_19;
x_4 = x_6;
goto _start;
}
}
}
}
default: 
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_string_utf8_byte_size(x_1);
x_25 = lean_nat_dec_lt(x_3, x_24);
lean_dec(x_24);
if (lean_obj_tag(x_21) == 0)
{
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_3);
x_26 = lean_string_get_byte_fast(x_1, x_3);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1(x_26, x_22, x_27);
lean_dec(x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_23);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
x_31 = lean_array_get(x_30, x_23, x_29);
lean_dec(x_29);
lean_dec(x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_3, x_32);
lean_dec(x_3);
x_2 = x_31;
x_3 = x_33;
goto _start;
}
}
}
else
{
lean_dec(x_4);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_3);
x_35 = lean_string_get_byte_fast(x_1, x_3);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2(x_35, x_22, x_36);
lean_dec(x_22);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_23);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Data_Trie_instEmptyCollection___closed__1;
x_40 = lean_array_get(x_39, x_23, x_38);
lean_dec(x_38);
lean_dec(x_23);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_3, x_41);
lean_dec(x_3);
x_2 = x_40;
x_3 = x_42;
x_4 = x_21;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_matchPrefix_loop___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at_Lean_Data_Trie_matchPrefix_loop___spec__2(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_matchPrefix_loop___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_Data_Trie_matchPrefix_loop___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_matchPrefix___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_matchPrefix___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_uint8_to_nat(x_1);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg(x_2);
x_7 = lean_box(1);
x_8 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_6, x_7);
x_9 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(0);
return x_2;
}
case 1:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_uint8_to_nat(x_3);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg(x_4);
x_9 = lean_box(1);
x_10 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_8, x_9);
x_11 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_ByteArray_toList(x_18);
lean_dec(x_18);
x_21 = lean_array_to_list(x_19);
x_22 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1;
x_23 = l_Lean_Data_Trie_values___rarg___closed__1;
x_24 = l_List_zipWithTR_go___rarg(x_22, x_20, x_21, x_23);
x_25 = l_List_flatMapTR_go___at___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___spec__1(x_24, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg(x_1);
x_3 = lean_box(1);
x_4 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_2, x_3);
x_5 = l_Std_Format_defWidth;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_format_pretty(x_4, x_5, x_6, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Data_Trie_instToString___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Trie(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Data_Trie_empty___closed__1 = _init_l_Lean_Data_Trie_empty___closed__1();
lean_mark_persistent(l_Lean_Data_Trie_empty___closed__1);
l_Lean_Data_Trie_instEmptyCollection___closed__1 = _init_l_Lean_Data_Trie_instEmptyCollection___closed__1();
lean_mark_persistent(l_Lean_Data_Trie_instEmptyCollection___closed__1);
l_Lean_Data_Trie_values___rarg___closed__1 = _init_l_Lean_Data_Trie_values___rarg___closed__1();
lean_mark_persistent(l_Lean_Data_Trie_values___rarg___closed__1);
l_Lean_Data_Trie_findPrefix_go___rarg___closed__1 = _init_l_Lean_Data_Trie_findPrefix_go___rarg___closed__1();
lean_mark_persistent(l_Lean_Data_Trie_findPrefix_go___rarg___closed__1);
l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1 = _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___lambda__1___closed__1);
l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1 = _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
