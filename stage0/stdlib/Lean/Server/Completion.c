// Lean compiler output
// Module: Lean.Server.Completion
// Imports: public import Lean.Server.Completion.CompletionCollectors public import Std.Data.HashMap
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
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2;
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t l_Lean_Lsp_instBEqInsertReplaceEdit_beq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_errorNameCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_endSectionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint64_t l_Lean_Lsp_instHashableInsertReplaceEdit_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Server_CancellableM_checkCancelled(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_Lsp_instBEqInsertReplaceEdit_beq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_string_dec_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0_spec__0(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_array_get_size(x_1);
x_10 = lean_string_hash(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_29; 
x_29 = 11;
x_11 = x_29;
goto block_28;
}
else
{
lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(x_30);
x_32 = 13;
x_33 = lean_uint64_mix_hash(x_31, x_32);
x_11 = x_33;
goto block_28;
}
block_28:
{
uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_1, x_23);
if (lean_is_scalar(x_6)) {
 x_25 = lean_alloc_ctor(1, 3, 0);
} else {
 x_25 = x_6;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_uset(x_1, x_23, x_25);
x_1 = x_26;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_array_uget(x_1, x_3);
x_24 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_16, 4);
lean_inc(x_25);
lean_inc(x_25);
lean_inc_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_array_get_size(x_15);
x_28 = lean_string_hash(x_24);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint64_t x_79; 
x_79 = 11;
x_29 = x_79;
goto block_78;
}
else
{
lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; 
x_80 = lean_ctor_get(x_25, 0);
lean_inc(x_80);
lean_dec_ref(x_25);
x_81 = l_Lean_Lsp_instHashableInsertReplaceEdit_hash(x_80);
lean_dec(x_80);
x_82 = 13;
x_83 = lean_uint64_mix_hash(x_81, x_82);
x_29 = x_83;
goto block_78;
}
block_23:
{
uint8_t x_19; 
x_19 = lean_unbox(x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_push(x_12, x_16);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_5 = x_21;
goto block_9;
}
else
{
lean_object* x_22; 
lean_dec(x_16);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_13;
}
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_12);
x_5 = x_22;
goto block_9;
}
}
block_78:
{
uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_uint64_mix_hash(x_28, x_29);
x_31 = 32;
x_32 = lean_uint64_shift_right(x_30, x_31);
x_33 = lean_uint64_xor(x_30, x_32);
x_34 = 16;
x_35 = lean_uint64_shift_right(x_33, x_34);
x_36 = lean_uint64_xor(x_33, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
x_39 = 1;
x_40 = lean_usize_sub(x_38, x_39);
x_41 = lean_usize_land(x_37, x_40);
x_42 = lean_array_uget(x_15, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_26, x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc_ref(x_15);
lean_inc(x_14);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_45 = lean_ctor_get(x_11, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_11, 0);
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_14, x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_42);
x_51 = lean_array_uset(x_15, x_41, x_50);
x_52 = lean_unsigned_to_nat(4u);
x_53 = lean_nat_mul(x_49, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = lean_array_get_size(x_51);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_51);
lean_ctor_set(x_11, 1, x_58);
lean_ctor_set(x_11, 0, x_49);
x_59 = lean_box(x_43);
x_17 = x_59;
x_18 = x_11;
goto block_23;
}
else
{
lean_object* x_60; 
lean_ctor_set(x_11, 1, x_51);
lean_ctor_set(x_11, 0, x_49);
x_60 = lean_box(x_43);
x_17 = x_60;
x_18 = x_11;
goto block_23;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_11);
x_61 = lean_box(0);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_14, x_62);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_26);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_42);
x_65 = lean_array_uset(x_15, x_41, x_64);
x_66 = lean_unsigned_to_nat(4u);
x_67 = lean_nat_mul(x_63, x_66);
x_68 = lean_unsigned_to_nat(3u);
x_69 = lean_nat_div(x_67, x_68);
lean_dec(x_67);
x_70 = lean_array_get_size(x_65);
x_71 = lean_nat_dec_le(x_69, x_70);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_65);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_box(x_43);
x_17 = x_74;
x_18 = x_73;
goto block_23;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_65);
x_76 = lean_box(x_43);
x_17 = x_76;
x_18 = x_75;
goto block_23;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_42);
lean_dec_ref(x_26);
x_77 = lean_box(x_43);
x_17 = x_77;
x_18 = x_11;
goto block_23;
}
}
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_3, x_6);
x_3 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3;
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg(x_1, x_3, x_4, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems_spec__1_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_7, x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_8);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_array_uget(x_5, x_7);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Server_CancellableM_checkCancelled(x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_11 = x_32;
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_33; 
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_28, 2);
switch (lean_obj_tag(x_33)) {
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
x_39 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_33);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_1);
x_40 = l_Lean_Server_Completion_idCompletion(x_1, x_2, x_29, x_35, x_39, x_36, x_37, x_34, x_38, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_11 = x_42;
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec_ref(x_41);
x_16 = x_8;
x_17 = x_43;
x_18 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_40;
}
}
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_33);
x_44 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_44);
lean_dec(x_28);
x_45 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_45);
lean_dec_ref(x_33);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_1);
x_46 = l_Lean_Server_Completion_dotCompletion(x_1, x_2, x_29, x_44, x_45, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_11 = x_48;
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec_ref(x_47);
x_16 = x_8;
x_17 = x_49;
x_18 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_46;
}
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_inc_ref(x_33);
x_50 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_50);
lean_dec(x_28);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_33, 3);
lean_inc(x_53);
lean_dec_ref(x_33);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_1);
x_54 = l_Lean_Server_Completion_dotIdCompletion(x_1, x_2, x_29, x_50, x_52, x_51, x_53, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_11 = x_56;
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec_ref(x_55);
x_16 = x_8;
x_17 = x_57;
x_18 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_54;
}
}
case 3:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc_ref(x_33);
x_58 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_58);
lean_dec(x_28);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_33, 3);
lean_inc(x_61);
lean_dec_ref(x_33);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
lean_inc(x_1);
x_62 = l_Lean_Server_Completion_fieldIdCompletion(x_1, x_2, x_29, x_58, x_60, x_59, x_61, x_9);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_11 = x_64;
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec_ref(x_63);
x_16 = x_8;
x_17 = x_65;
x_18 = lean_box(0);
goto block_23;
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_62;
}
}
case 5:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc_ref(x_33);
x_66 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_66);
lean_dec(x_28);
x_67 = lean_ctor_get(x_33, 0);
lean_inc(x_67);
lean_dec_ref(x_33);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_68 = l_Lean_Server_Completion_optionCompletion(x_1, x_2, x_29, x_66, x_67, x_3);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_16 = x_8;
x_17 = x_69;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_70; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
case 6:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_inc_ref(x_33);
x_73 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_73);
lean_dec(x_28);
x_74 = lean_ctor_get(x_33, 1);
lean_inc(x_74);
lean_dec_ref(x_33);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_75 = l_Lean_Server_Completion_errorNameCompletion(x_1, x_2, x_29, x_73, x_74, x_3);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_16 = x_8;
x_17 = x_76;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_77; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
case 7:
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
lean_inc_ref(x_33);
lean_dec(x_28);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
x_82 = lean_ctor_get(x_33, 2);
lean_inc(x_82);
lean_dec_ref(x_33);
lean_inc_ref(x_2);
lean_inc(x_1);
x_83 = l_Lean_Server_Completion_endSectionCompletion(x_1, x_2, x_29, x_80, x_81, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_16 = x_8;
x_17 = x_84;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_85; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
case 8:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_88);
lean_dec(x_28);
lean_inc_ref(x_2);
lean_inc(x_1);
x_89 = l_Lean_Server_Completion_tacticCompletion(x_1, x_2, x_29, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_16 = x_8;
x_17 = x_90;
x_18 = lean_box(0);
goto block_23;
}
else
{
uint8_t x_91; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
default: 
{
lean_dec(x_29);
lean_dec(x_28);
lean_inc_ref(x_4);
x_16 = x_8;
x_17 = x_4;
x_18 = lean_box(0);
goto block_23;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_30);
if (x_94 == 0)
{
return x_30;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_30, 0);
lean_inc(x_95);
lean_dec(x_30);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = l_Array_append___redArg(x_16, x_17);
lean_dec_ref(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_7 = x_21;
x_8 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_7, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_5, x_7);
x_15 = lean_array_size(x_14);
x_16 = 0;
lean_inc_ref(x_9);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__0(x_1, x_2, x_3, x_4, x_14, x_15, x_16, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Array_isEmpty___redArg(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
else
{
size_t x_21; size_t x_22; 
lean_dec_ref(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_7, x_21);
x_7 = x_22;
x_8 = x_19;
goto _start;
}
}
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_11, x_12, x_8, x_9);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0;
x_14 = lean_array_size(x_11);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_Completion_find_x3f_spec__1(x_1, x_2, x_7, x_13, x_11, x_14, x_15, x_13, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_is_scalar(x_18)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_18;
}
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
x_26 = l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems(x_24);
lean_dec(x_24);
x_32 = lean_unbox(x_12);
lean_dec(x_12);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 1;
x_27 = x_33;
goto block_31;
}
else
{
uint8_t x_34; 
x_34 = 0;
x_27 = x_34;
goto block_31;
}
block_31:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_18)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_18;
}
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_find_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_Completion_find_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionCollectors(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__0);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__1);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__2);
l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3 = _init_l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_0__Lean_Server_Completion_filterDuplicateCompletionItems___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
