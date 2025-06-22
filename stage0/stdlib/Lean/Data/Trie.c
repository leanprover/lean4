// Lean compiler output
// Module: Lean.Data.Trie
// Imports: Lean.Data.Format Init.Data.Option.Coe
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
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___lam__0(lean_object*, lean_object*);
lean_object* l_List_foldl___at___Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object*, lean_object*);
lean_object* l_ByteArray_toList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_instToFormatFormat___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_findPrefix_go___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_empty___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Data_Trie_upsert_loop___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Data_Trie_values___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(uint8_t, lean_object*, lean_object*);
lean_object* l_List_zipWithTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Data_Trie_empty___closed__0() {
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
x_2 = l_Lean_Data_Trie_empty___closed__0;
return x_2;
}
}
static lean_object* _init_l_Lean_Data_Trie_instEmptyCollection___closed__0() {
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
x_2 = l_Lean_Data_Trie_instEmptyCollection___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Data_Trie_instEmptyCollection___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_insertEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert_insertEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_byte_array_fget(x_2, x_3);
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
static lean_object* _init_l_Lean_Data_Trie_upsert_loop___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_13);
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
x_25 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_24);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_4);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_3, x_37);
lean_dec(x_3);
x_39 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_38);
x_40 = l_Lean_Data_Trie_upsert_loop___redArg___closed__0;
x_41 = lean_box(x_35);
x_42 = lean_array_push(x_40, x_41);
x_43 = lean_box(x_29);
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_byte_array_mk(x_44);
x_46 = lean_array_push(x_40, x_39);
x_47 = lean_array_push(x_46, x_30);
x_48 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_48, 0, x_28);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_3, x_49);
lean_dec(x_3);
x_51 = l_Lean_Data_Trie_upsert_loop___redArg(x_1, x_2, x_50, x_30);
lean_ctor_set(x_4, 1, x_51);
return x_4;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_52);
lean_dec(x_4);
x_55 = lean_string_utf8_byte_size(x_1);
x_56 = lean_nat_dec_lt(x_3, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_3);
x_57 = lean_apply_1(x_2, x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_53);
return x_59;
}
else
{
uint8_t x_60; uint8_t x_61; 
lean_inc(x_3);
x_60 = lean_string_get_byte_fast(x_1, x_3);
x_61 = lean_uint8_dec_eq(x_60, x_53);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_3, x_62);
lean_dec(x_3);
x_64 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_63);
x_65 = l_Lean_Data_Trie_upsert_loop___redArg___closed__0;
x_66 = lean_box(x_60);
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_box(x_53);
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_byte_array_mk(x_69);
x_71 = lean_array_push(x_65, x_64);
x_72 = lean_array_push(x_71, x_54);
x_73 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_73, 0, x_52);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_add(x_3, x_74);
lean_dec(x_3);
x_76 = l_Lean_Data_Trie_upsert_loop___redArg(x_1, x_2, x_75, x_54);
x_77 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_77, 0, x_52);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_53);
return x_77;
}
}
}
}
default: 
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
x_81 = lean_string_utf8_byte_size(x_1);
x_82 = lean_nat_dec_lt(x_3, x_81);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_4, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_4, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_4, 0);
lean_dec(x_86);
x_87 = lean_apply_1(x_2, x_78);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_4, 0, x_88);
return x_4;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_4);
x_89 = lean_apply_1(x_2, x_78);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_79);
lean_ctor_set(x_91, 2, x_80);
return x_91;
}
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_3);
x_92 = lean_string_get_byte_fast(x_1, x_3);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(x_92, x_79, x_93);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_4);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_4, 2);
lean_dec(x_96);
x_97 = lean_ctor_get(x_4, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_4, 0);
lean_dec(x_98);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_3, x_99);
lean_dec(x_3);
x_101 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_100);
x_102 = lean_byte_array_push(x_79, x_92);
x_103 = lean_array_push(x_80, x_101);
lean_ctor_set(x_4, 2, x_103);
lean_ctor_set(x_4, 1, x_102);
return x_4;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_4);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_3, x_104);
lean_dec(x_3);
x_106 = l_Lean_Data_Trie_upsert_insertEmpty___redArg(x_1, x_2, x_105);
x_107 = lean_byte_array_push(x_79, x_92);
x_108 = lean_array_push(x_80, x_106);
x_109 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_109, 0, x_78);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_108);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_94, 0);
lean_inc(x_110);
lean_dec(x_94);
x_111 = lean_array_get_size(x_80);
x_112 = lean_nat_dec_lt(x_110, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_4);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_4, 2);
lean_dec(x_114);
x_115 = lean_ctor_get(x_4, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_4, 0);
lean_dec(x_116);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_3, x_117);
lean_dec(x_3);
x_119 = lean_array_fget(x_80, x_110);
x_120 = lean_box(0);
x_121 = lean_array_fset(x_80, x_110, x_120);
x_122 = l_Lean_Data_Trie_upsert_loop___redArg(x_1, x_2, x_118, x_119);
x_123 = lean_array_fset(x_121, x_110, x_122);
lean_dec(x_110);
lean_ctor_set(x_4, 2, x_123);
return x_4;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_4);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_add(x_3, x_124);
lean_dec(x_3);
x_126 = lean_array_fget(x_80, x_110);
x_127 = lean_box(0);
x_128 = lean_array_fset(x_80, x_110, x_127);
x_129 = l_Lean_Data_Trie_upsert_loop___redArg(x_1, x_2, x_125, x_126);
x_130 = lean_array_fset(x_128, x_110, x_129);
lean_dec(x_110);
x_131 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_131, 0, x_78);
lean_ctor_set(x_131, 1, x_79);
lean_ctor_set(x_131, 2, x_130);
return x_131;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Data_Trie_upsert_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert_loop___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Data_Trie_upsert_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Data_Trie_upsert_loop___redArg(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_upsert___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_upsert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_upsert(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Data_Trie_insert___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Data_Trie_upsert___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_insert___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_insert___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_insert___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_insert(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_26 = l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(x_24, x_20, x_25);
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
x_31 = l_Lean_Data_Trie_instEmptyCollection___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_find_x3f_loop___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_find_x3f_loop___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_find_x3f_loop(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Data_Trie_find_x3f_loop___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_find_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_find_x3f___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_find_x3f(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Data_Trie_values_go___redArg(x_7, x_5);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_box(0);
x_8 = lean_array_push(x_2, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
x_19 = x_2;
goto block_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_array_push(x_2, x_31);
x_19 = x_32;
goto block_30;
}
block_30:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_18);
x_22 = lean_box(0);
x_23 = lean_nat_dec_lt(x_20, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg(x_18, x_27, x_28, x_22, x_19);
lean_dec(x_18);
return x_29;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_values_go___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Data_Trie_values_go_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Data_Trie_values___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Data_Trie_values___redArg___closed__0;
x_3 = l_Lean_Data_Trie_values_go___redArg(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_values(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_values___redArg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Data_Trie_findPrefix_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_Data_Trie_values___redArg(x_2);
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
x_8 = l_Lean_Data_Trie_findPrefix_go___redArg___closed__0;
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
x_12 = l_Lean_Data_Trie_findPrefix_go___redArg___closed__0;
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
x_19 = l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(x_7, x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_3);
x_20 = l_Lean_Data_Trie_findPrefix_go___redArg___closed__0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Data_Trie_instEmptyCollection___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_findPrefix_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_findPrefix_go___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_findPrefix_go(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Data_Trie_findPrefix_go___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_findPrefix___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Data_Trie_findPrefix___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_findPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_findPrefix(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
x_9 = x_4;
goto block_17;
}
else
{
lean_dec(x_4);
x_9 = x_6;
goto block_17;
}
block_17:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_string_utf8_byte_size(x_1);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_9;
}
else
{
uint8_t x_12; uint8_t x_13; 
lean_inc(x_3);
x_12 = lean_string_get_byte_fast(x_1, x_3);
x_13 = lean_uint8_dec_eq(x_12, x_7);
if (x_13 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_2 = x_8;
x_3 = x_15;
x_4 = x_9;
goto _start;
}
}
}
}
default: 
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_dec(x_2);
if (lean_obj_tag(x_18) == 0)
{
x_21 = x_4;
goto block_33;
}
else
{
lean_dec(x_4);
x_21 = x_18;
goto block_33;
}
block_33:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_string_utf8_byte_size(x_1);
x_23 = lean_nat_dec_lt(x_3, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
x_24 = lean_string_get_byte_fast(x_1, x_3);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_ByteArray_findIdx_x3f_loop___at___Lean_Data_Trie_upsert_loop_spec__0(x_24, x_19, x_25);
lean_dec(x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_20);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Data_Trie_instEmptyCollection___closed__0;
x_29 = lean_array_get(x_28, x_20, x_27);
lean_dec(x_27);
lean_dec(x_20);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_2 = x_29;
x_3 = x_31;
x_4 = x_21;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Data_Trie_matchPrefix_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_matchPrefix_loop___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Data_Trie_matchPrefix_loop(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_Data_Trie_matchPrefix_loop___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_matchPrefix___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Data_Trie_matchPrefix___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_matchPrefix___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Data_Trie_matchPrefix(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_flatMapTR_go___at_____private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_foldl___at___Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_uint8_to_nat(x_1);
x_4 = l_Nat_reprFast(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0;
x_7 = lean_box(1);
x_8 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(x_2);
x_9 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_8, x_7);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(lean_object* x_1) {
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
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_uint8_to_nat(x_3);
x_6 = l_Nat_reprFast(x_5);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0;
x_9 = lean_box(1);
x_10 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(x_4);
x_11 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_10, x_9);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed), 2, 0);
x_22 = l_ByteArray_toList(x_19);
lean_dec(x_19);
x_23 = lean_array_to_list(x_20);
x_24 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0;
x_25 = l_List_zipWithTR_go___redArg(x_21, x_22, x_23, x_24);
x_26 = l_List_flatMapTR_go___at_____private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(x_25, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(1);
x_4 = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(x_2);
x_5 = l_Std_Format_joinSep___redArg(x_1, x_4, x_3);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Data_Trie_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_instToFormatFormat___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Data_Trie_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Data_Trie_instToString___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_Data_Trie_instToString___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Trie(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Data_Trie_empty___closed__0 = _init_l_Lean_Data_Trie_empty___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_empty___closed__0);
l_Lean_Data_Trie_instEmptyCollection___closed__0 = _init_l_Lean_Data_Trie_instEmptyCollection___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_instEmptyCollection___closed__0);
l_Lean_Data_Trie_upsert_loop___redArg___closed__0 = _init_l_Lean_Data_Trie_upsert_loop___redArg___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_upsert_loop___redArg___closed__0);
l_Lean_Data_Trie_values___redArg___closed__0 = _init_l_Lean_Data_Trie_values___redArg___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_values___redArg___closed__0);
l_Lean_Data_Trie_findPrefix_go___redArg___closed__0 = _init_l_Lean_Data_Trie_findPrefix_go___redArg___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_findPrefix_go___redArg___closed__0);
l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0 = _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0 = _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0);
l_Lean_Data_Trie_instToString___closed__0 = _init_l_Lean_Data_Trie_instToString___closed__0();
lean_mark_persistent(l_Lean_Data_Trie_instToString___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
