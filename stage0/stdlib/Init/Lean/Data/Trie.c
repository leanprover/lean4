// Lean compiler output
// Module: Init.Lean.Data.Trie
// Imports: Init.Data.RBMap Init.Lean.Data.Format
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
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(lean_object*, uint32_t, lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_HasEmptyc(lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7(lean_object*);
lean_object* l_Lean_Parser_Trie_HasToString___rarg(lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_empty(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_find___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main(lean_object*);
lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l___private_Init_Lean_Data_Trie_3__findAux(lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg(lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main(lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___main(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___rarg(lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5(lean_object*);
lean_object* l_Lean_Parser_Trie_find___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6(lean_object*);
lean_object* l_Lean_Parser_Trie_find(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_HasToString(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1(lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_Parser_Trie_Inhabited(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2(lean_object*);
lean_object* l_Lean_Parser_Trie_insert___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux(lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Parser_Trie_empty___closed__1;
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main(lean_object*);
lean_object* l_Char_quoteCore(uint32_t);
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l_Lean_Parser_Trie_insert(lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux(lean_object*);
lean_object* l_RBNode_singleton___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Parser_Trie_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Parser_Trie_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Trie_empty___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_Parser_Trie_HasEmptyc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_Trie_empty(lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Parser_Trie_HasEmptyc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Trie_HasEmptyc___closed__1;
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Parser_Trie_empty___closed__1;
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_box_uint32(x_5);
x_10 = l_RBNode_singleton___rarg(x_9, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_box_uint32(x_2);
x_9 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_9, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 7, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_unbox_uint32(x_13);
x_17 = x_2 < x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = lean_unbox_uint32(x_13);
x_19 = x_18 < x_2;
if (x_19 == 0)
{
uint32_t x_20; uint16_t x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = 0;
x_21 = 0;
x_22 = 0;
x_23 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_20);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_22);
return x_1;
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_15, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 3, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; 
x_28 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_12, x_2, x_3);
x_29 = 0;
x_30 = 0;
x_31 = 0;
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_29);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_36 = lean_unbox_uint32(x_33);
x_37 = x_2 < x_36;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = lean_unbox_uint32(x_33);
x_39 = x_38 < x_2;
if (x_39 == 0)
{
uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_33);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_box_uint32(x_2);
x_44 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_44, sizeof(void*)*4, x_40);
lean_ctor_set_uint16(x_44, sizeof(void*)*4 + 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 7, x_42);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint16_t x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_35, x_2, x_3);
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_49, sizeof(void*)*4, x_46);
lean_ctor_set_uint16(x_49, sizeof(void*)*4 + 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 7, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint32_t x_51; uint16_t x_52; uint8_t x_53; lean_object* x_54; 
x_50 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_32, x_2, x_3);
x_51 = 0;
x_52 = 0;
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_34);
lean_ctor_set(x_54, 3, x_35);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_54, sizeof(void*)*4, x_51);
lean_ctor_set_uint16(x_54, sizeof(void*)*4 + 4, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 7, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
x_60 = lean_unbox_uint32(x_57);
x_61 = x_2 < x_60;
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = lean_unbox_uint32(x_57);
x_63 = x_62 < x_2;
if (x_63 == 0)
{
uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_64);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_66);
return x_1;
}
else
{
uint8_t x_68; 
x_68 = l_RBNode_isRed___rarg(x_59);
if (x_68 == 0)
{
lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; 
x_69 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_59, x_2, x_3);
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_1, 3, x_69);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_72);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_59, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; uint8_t x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; 
x_77 = lean_ctor_get(x_73, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
lean_ctor_set(x_73, 0, x_75);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_82);
x_83 = 1;
x_84 = 0;
x_85 = 0;
x_86 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_83);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_84);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_86);
return x_1;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint32_t x_90; uint16_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint32_t x_95; uint16_t x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_73, 1);
x_88 = lean_ctor_get(x_73, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = 0;
x_90 = 0;
x_91 = 0;
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_75);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 6, x_89);
lean_ctor_set_uint32(x_93, sizeof(void*)*4, x_90);
lean_ctor_set_uint16(x_93, sizeof(void*)*4 + 4, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 7, x_92);
x_94 = 1;
x_95 = 0;
x_96 = 0;
x_97 = 0;
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_94);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_95);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_97);
return x_1;
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_75, sizeof(void*)*4 + 6);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_73);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_73, 1);
x_101 = lean_ctor_get(x_73, 2);
x_102 = lean_ctor_get(x_73, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_73, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_75);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint32_t x_110; uint16_t x_111; uint8_t x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; uint32_t x_116; uint16_t x_117; uint8_t x_118; 
x_105 = lean_ctor_get(x_75, 0);
x_106 = lean_ctor_get(x_75, 1);
x_107 = lean_ctor_get(x_75, 2);
x_108 = lean_ctor_get(x_75, 3);
x_109 = 1;
x_110 = 0;
x_111 = 0;
x_112 = 0;
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_75, sizeof(void*)*4, x_110);
lean_ctor_set_uint16(x_75, sizeof(void*)*4 + 4, x_111);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 7, x_112);
x_113 = 0;
x_114 = 0;
x_115 = 0;
lean_ctor_set(x_73, 3, x_108);
lean_ctor_set(x_73, 2, x_107);
lean_ctor_set(x_73, 1, x_106);
lean_ctor_set(x_73, 0, x_105);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_113);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_114);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_115);
x_116 = 0;
x_117 = 0;
x_118 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_116);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_118);
return x_1;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; uint32_t x_128; uint16_t x_129; uint8_t x_130; uint32_t x_131; uint16_t x_132; uint8_t x_133; 
x_119 = lean_ctor_get(x_75, 0);
x_120 = lean_ctor_get(x_75, 1);
x_121 = lean_ctor_get(x_75, 2);
x_122 = lean_ctor_get(x_75, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_75);
x_123 = 1;
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_127, 0, x_56);
lean_ctor_set(x_127, 1, x_57);
lean_ctor_set(x_127, 2, x_58);
lean_ctor_set(x_127, 3, x_74);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_127, sizeof(void*)*4, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*4 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 7, x_126);
x_128 = 0;
x_129 = 0;
x_130 = 0;
lean_ctor_set(x_73, 3, x_122);
lean_ctor_set(x_73, 2, x_121);
lean_ctor_set(x_73, 1, x_120);
lean_ctor_set(x_73, 0, x_119);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_128);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_129);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_130);
x_131 = 0;
x_132 = 0;
x_133 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_131);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_133);
return x_1;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint32_t x_142; uint16_t x_143; uint8_t x_144; lean_object* x_145; uint32_t x_146; uint16_t x_147; uint8_t x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_73, 1);
x_135 = lean_ctor_get(x_73, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_73);
x_136 = lean_ctor_get(x_75, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_75, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_75, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_75, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_140 = x_75;
} else {
 lean_dec_ref(x_75);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = 0;
x_143 = 0;
x_144 = 0;
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(1, 4, 8);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_56);
lean_ctor_set(x_145, 1, x_57);
lean_ctor_set(x_145, 2, x_58);
lean_ctor_set(x_145, 3, x_74);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_145, sizeof(void*)*4, x_142);
lean_ctor_set_uint16(x_145, sizeof(void*)*4 + 4, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 7, x_144);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_149, sizeof(void*)*4, x_146);
lean_ctor_set_uint16(x_149, sizeof(void*)*4 + 4, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 7, x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_149);
lean_ctor_set(x_1, 2, x_135);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_145);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_73);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint32_t x_157; uint16_t x_158; uint8_t x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_73, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_73, 0);
lean_dec(x_155);
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_156);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_157);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_158);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_159);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; uint32_t x_170; uint16_t x_171; uint8_t x_172; 
x_163 = lean_ctor_get(x_73, 1);
x_164 = lean_ctor_get(x_73, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_73);
x_165 = 0;
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_169, 0, x_74);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 3, x_75);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 6, x_165);
lean_ctor_set_uint32(x_169, sizeof(void*)*4, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*4 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 7, x_168);
x_170 = 0;
x_171 = 0;
x_172 = 0;
lean_ctor_set(x_1, 3, x_169);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_170);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_171);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_172);
return x_1;
}
}
}
}
else
{
uint8_t x_173; 
x_173 = lean_ctor_get_uint8(x_74, sizeof(void*)*4 + 6);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_73);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_73, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_74);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint32_t x_182; uint16_t x_183; uint8_t x_184; uint32_t x_185; uint16_t x_186; uint8_t x_187; uint32_t x_188; uint16_t x_189; uint8_t x_190; 
x_177 = lean_ctor_get(x_74, 0);
x_178 = lean_ctor_get(x_74, 1);
x_179 = lean_ctor_get(x_74, 2);
x_180 = lean_ctor_get(x_74, 3);
x_181 = 1;
x_182 = 0;
x_183 = 0;
x_184 = 0;
lean_ctor_set(x_74, 3, x_177);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_182);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_183);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_184);
x_185 = 0;
x_186 = 0;
x_187 = 0;
lean_ctor_set(x_73, 0, x_180);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_185);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_186);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_187);
x_188 = 0;
x_189 = 0;
x_190 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_179);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_188);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_190);
return x_1;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint32_t x_196; uint16_t x_197; uint8_t x_198; lean_object* x_199; uint32_t x_200; uint16_t x_201; uint8_t x_202; uint32_t x_203; uint16_t x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_74, 0);
x_192 = lean_ctor_get(x_74, 1);
x_193 = lean_ctor_get(x_74, 2);
x_194 = lean_ctor_get(x_74, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_74);
x_195 = 1;
x_196 = 0;
x_197 = 0;
x_198 = 0;
x_199 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_199, 0, x_56);
lean_ctor_set(x_199, 1, x_57);
lean_ctor_set(x_199, 2, x_58);
lean_ctor_set(x_199, 3, x_191);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_199, sizeof(void*)*4, x_196);
lean_ctor_set_uint16(x_199, sizeof(void*)*4 + 4, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 7, x_198);
x_200 = 0;
x_201 = 0;
x_202 = 0;
lean_ctor_set(x_73, 0, x_194);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_200);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_201);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_202);
x_203 = 0;
x_204 = 0;
x_205 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_193);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_203);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_205);
return x_1;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint32_t x_215; uint16_t x_216; uint8_t x_217; lean_object* x_218; uint32_t x_219; uint16_t x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; 
x_206 = lean_ctor_get(x_73, 1);
x_207 = lean_ctor_get(x_73, 2);
x_208 = lean_ctor_get(x_73, 3);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_73);
x_209 = lean_ctor_get(x_74, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_74, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_74, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_74, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_213 = x_74;
} else {
 lean_dec_ref(x_74);
 x_213 = lean_box(0);
}
x_214 = 1;
x_215 = 0;
x_216 = 0;
x_217 = 0;
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(1, 4, 8);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_56);
lean_ctor_set(x_218, 1, x_57);
lean_ctor_set(x_218, 2, x_58);
lean_ctor_set(x_218, 3, x_209);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_218, sizeof(void*)*4, x_215);
lean_ctor_set_uint16(x_218, sizeof(void*)*4 + 4, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 7, x_217);
x_219 = 0;
x_220 = 0;
x_221 = 0;
x_222 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_206);
lean_ctor_set(x_222, 2, x_207);
lean_ctor_set(x_222, 3, x_208);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_222, sizeof(void*)*4, x_219);
lean_ctor_set_uint16(x_222, sizeof(void*)*4 + 4, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 7, x_221);
x_223 = 0;
x_224 = 0;
x_225 = 0;
lean_ctor_set(x_1, 3, x_222);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_218);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_223);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_225);
return x_1;
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_73, 3);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_73);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint32_t x_231; uint16_t x_232; uint8_t x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_228 = lean_ctor_get(x_73, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_73, 0);
lean_dec(x_229);
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_230);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_231);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_232);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_233);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; uint32_t x_244; uint16_t x_245; uint8_t x_246; 
x_237 = lean_ctor_get(x_73, 1);
x_238 = lean_ctor_get(x_73, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_73);
x_239 = 0;
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_243, 0, x_74);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_226);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 6, x_239);
lean_ctor_set_uint32(x_243, sizeof(void*)*4, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*4 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 7, x_242);
x_244 = 0;
x_245 = 0;
x_246 = 0;
lean_ctor_set(x_1, 3, x_243);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_244);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_246);
return x_1;
}
}
else
{
uint8_t x_247; 
x_247 = lean_ctor_get_uint8(x_226, sizeof(void*)*4 + 6);
if (x_247 == 0)
{
uint8_t x_248; 
lean_free_object(x_1);
x_248 = !lean_is_exclusive(x_73);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_73, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_73, 0);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_226);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint32_t x_256; uint16_t x_257; uint8_t x_258; uint8_t x_259; 
x_252 = lean_ctor_get(x_226, 0);
x_253 = lean_ctor_get(x_226, 1);
x_254 = lean_ctor_get(x_226, 2);
x_255 = lean_ctor_get(x_226, 3);
x_256 = 0;
x_257 = 0;
x_258 = 0;
lean_inc(x_74);
lean_ctor_set(x_226, 3, x_74);
lean_ctor_set(x_226, 2, x_58);
lean_ctor_set(x_226, 1, x_57);
lean_ctor_set(x_226, 0, x_56);
x_259 = !lean_is_exclusive(x_74);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; 
x_260 = lean_ctor_get(x_74, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_74, 2);
lean_dec(x_261);
x_262 = lean_ctor_get(x_74, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_74, 3, x_255);
lean_ctor_set(x_74, 2, x_254);
lean_ctor_set(x_74, 1, x_253);
lean_ctor_set(x_74, 0, x_252);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_266);
x_267 = 0;
x_268 = 0;
x_269 = 0;
lean_ctor_set(x_73, 3, x_74);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_267);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_268);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_269);
return x_73;
}
else
{
uint32_t x_270; uint16_t x_271; uint8_t x_272; lean_object* x_273; uint32_t x_274; uint16_t x_275; uint8_t x_276; 
lean_dec(x_74);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_270 = 0;
x_271 = 0;
x_272 = 0;
x_273 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_273, 0, x_252);
lean_ctor_set(x_273, 1, x_253);
lean_ctor_set(x_273, 2, x_254);
lean_ctor_set(x_273, 3, x_255);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_273, sizeof(void*)*4, x_270);
lean_ctor_set_uint16(x_273, sizeof(void*)*4 + 4, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 7, x_272);
x_274 = 0;
x_275 = 0;
x_276 = 0;
lean_ctor_set(x_73, 3, x_273);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_274);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_275);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_276);
return x_73;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint32_t x_281; uint16_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint32_t x_286; uint16_t x_287; uint8_t x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; 
x_277 = lean_ctor_get(x_226, 0);
x_278 = lean_ctor_get(x_226, 1);
x_279 = lean_ctor_get(x_226, 2);
x_280 = lean_ctor_get(x_226, 3);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_226);
x_281 = 0;
x_282 = 0;
x_283 = 0;
lean_inc(x_74);
x_284 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_284, 0, x_56);
lean_ctor_set(x_284, 1, x_57);
lean_ctor_set(x_284, 2, x_58);
lean_ctor_set(x_284, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_285 = x_74;
} else {
 lean_dec_ref(x_74);
 x_285 = lean_box(0);
}
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_284, sizeof(void*)*4, x_281);
lean_ctor_set_uint16(x_284, sizeof(void*)*4 + 4, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 7, x_283);
x_286 = 0;
x_287 = 0;
x_288 = 0;
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(1, 4, 8);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_278);
lean_ctor_set(x_289, 2, x_279);
lean_ctor_set(x_289, 3, x_280);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_289, sizeof(void*)*4, x_286);
lean_ctor_set_uint16(x_289, sizeof(void*)*4 + 4, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 7, x_288);
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_ctor_set(x_73, 3, x_289);
lean_ctor_set(x_73, 0, x_284);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_292);
return x_73;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint32_t x_300; uint16_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint32_t x_305; uint16_t x_306; uint8_t x_307; lean_object* x_308; uint32_t x_309; uint16_t x_310; uint8_t x_311; lean_object* x_312; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_73);
x_295 = lean_ctor_get(x_226, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_226, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_226, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_226, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 x_299 = x_226;
} else {
 lean_dec_ref(x_226);
 x_299 = lean_box(0);
}
x_300 = 0;
x_301 = 0;
x_302 = 0;
lean_inc(x_74);
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(1, 4, 8);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_56);
lean_ctor_set(x_303, 1, x_57);
lean_ctor_set(x_303, 2, x_58);
lean_ctor_set(x_303, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_304 = x_74;
} else {
 lean_dec_ref(x_74);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_303, sizeof(void*)*4, x_300);
lean_ctor_set_uint16(x_303, sizeof(void*)*4 + 4, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 7, x_302);
x_305 = 0;
x_306 = 0;
x_307 = 0;
if (lean_is_scalar(x_304)) {
 x_308 = lean_alloc_ctor(1, 4, 8);
} else {
 x_308 = x_304;
}
lean_ctor_set(x_308, 0, x_295);
lean_ctor_set(x_308, 1, x_296);
lean_ctor_set(x_308, 2, x_297);
lean_ctor_set(x_308, 3, x_298);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_308, sizeof(void*)*4, x_305);
lean_ctor_set_uint16(x_308, sizeof(void*)*4 + 4, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 7, x_307);
x_309 = 0;
x_310 = 0;
x_311 = 0;
x_312 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_293);
lean_ctor_set(x_312, 2, x_294);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_312, sizeof(void*)*4, x_309);
lean_ctor_set_uint16(x_312, sizeof(void*)*4 + 4, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 7, x_311);
return x_312;
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_73);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_73, 3);
lean_dec(x_314);
x_315 = lean_ctor_get(x_73, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_74);
if (x_316 == 0)
{
uint32_t x_317; uint16_t x_318; uint8_t x_319; uint8_t x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; uint32_t x_324; uint16_t x_325; uint8_t x_326; 
x_317 = 0;
x_318 = 0;
x_319 = 0;
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_317);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_318);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_319);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_320);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_323);
x_324 = 0;
x_325 = 0;
x_326 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_324);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_326);
return x_1;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; uint32_t x_336; uint16_t x_337; uint8_t x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; 
x_327 = lean_ctor_get(x_74, 0);
x_328 = lean_ctor_get(x_74, 1);
x_329 = lean_ctor_get(x_74, 2);
x_330 = lean_ctor_get(x_74, 3);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_74);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_334, 2, x_329);
lean_ctor_set(x_334, 3, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_334, sizeof(void*)*4, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*4 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 7, x_333);
x_335 = 0;
x_336 = 0;
x_337 = 0;
x_338 = 0;
lean_ctor_set(x_73, 0, x_334);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_335);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_336);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_337);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_338);
x_339 = 0;
x_340 = 0;
x_341 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_341);
return x_1;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint32_t x_349; uint16_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; uint32_t x_354; uint16_t x_355; uint8_t x_356; lean_object* x_357; uint32_t x_358; uint16_t x_359; uint8_t x_360; 
x_342 = lean_ctor_get(x_73, 1);
x_343 = lean_ctor_get(x_73, 2);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_73);
x_344 = lean_ctor_get(x_74, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_74, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_74, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_74, 3);
lean_inc(x_347);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_348 = x_74;
} else {
 lean_dec_ref(x_74);
 x_348 = lean_box(0);
}
x_349 = 0;
x_350 = 0;
x_351 = 0;
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(1, 4, 8);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_345);
lean_ctor_set(x_352, 2, x_346);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_352, sizeof(void*)*4, x_349);
lean_ctor_set_uint16(x_352, sizeof(void*)*4 + 4, x_350);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 7, x_351);
x_353 = 0;
x_354 = 0;
x_355 = 0;
x_356 = 0;
x_357 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_342);
lean_ctor_set(x_357, 2, x_343);
lean_ctor_set(x_357, 3, x_226);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_353);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_354);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_356);
x_358 = 0;
x_359 = 0;
x_360 = 0;
lean_ctor_set(x_1, 3, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_358);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_359);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_360);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_361; 
x_361 = l_RBNode_isRed___rarg(x_56);
if (x_361 == 0)
{
lean_object* x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; 
x_362 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_56, x_2, x_3);
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_1, 0, x_362);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_365);
return x_1;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_56, x_2, x_3);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_366);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; uint8_t x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; 
x_370 = lean_ctor_get(x_366, 3);
lean_dec(x_370);
x_371 = lean_ctor_get(x_366, 0);
lean_dec(x_371);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
lean_ctor_set(x_366, 0, x_368);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_375);
x_376 = 1;
x_377 = 0;
x_378 = 0;
x_379 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_376);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_377);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_378);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_379);
return x_1;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; uint8_t x_387; uint32_t x_388; uint16_t x_389; uint8_t x_390; 
x_380 = lean_ctor_get(x_366, 1);
x_381 = lean_ctor_get(x_366, 2);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_366);
x_382 = 0;
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_386, 0, x_368);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_368);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 6, x_382);
lean_ctor_set_uint32(x_386, sizeof(void*)*4, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*4 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 7, x_385);
x_387 = 1;
x_388 = 0;
x_389 = 0;
x_390 = 0;
lean_ctor_set(x_1, 0, x_386);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_387);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_388);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_389);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_390);
return x_1;
}
}
else
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_368, sizeof(void*)*4 + 6);
if (x_391 == 0)
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_366);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_393 = lean_ctor_get(x_366, 1);
x_394 = lean_ctor_get(x_366, 2);
x_395 = lean_ctor_get(x_366, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_366, 0);
lean_dec(x_396);
x_397 = !lean_is_exclusive(x_368);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint32_t x_403; uint16_t x_404; uint8_t x_405; uint32_t x_406; uint16_t x_407; uint8_t x_408; uint32_t x_409; uint16_t x_410; uint8_t x_411; 
x_398 = lean_ctor_get(x_368, 0);
x_399 = lean_ctor_get(x_368, 1);
x_400 = lean_ctor_get(x_368, 2);
x_401 = lean_ctor_get(x_368, 3);
x_402 = 1;
x_403 = 0;
x_404 = 0;
x_405 = 0;
lean_ctor_set(x_368, 3, x_398);
lean_ctor_set(x_368, 2, x_394);
lean_ctor_set(x_368, 1, x_393);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_368, sizeof(void*)*4, x_403);
lean_ctor_set_uint16(x_368, sizeof(void*)*4 + 4, x_404);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 7, x_405);
x_406 = 0;
x_407 = 0;
x_408 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_401);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_406);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_407);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_408);
x_409 = 0;
x_410 = 0;
x_411 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_400);
lean_ctor_set(x_1, 1, x_399);
lean_ctor_set(x_1, 0, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_409);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_411);
return x_1;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; uint32_t x_417; uint16_t x_418; uint8_t x_419; lean_object* x_420; uint32_t x_421; uint16_t x_422; uint8_t x_423; uint32_t x_424; uint16_t x_425; uint8_t x_426; 
x_412 = lean_ctor_get(x_368, 0);
x_413 = lean_ctor_get(x_368, 1);
x_414 = lean_ctor_get(x_368, 2);
x_415 = lean_ctor_get(x_368, 3);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_368);
x_416 = 1;
x_417 = 0;
x_418 = 0;
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_420, 0, x_367);
lean_ctor_set(x_420, 1, x_393);
lean_ctor_set(x_420, 2, x_394);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_420, sizeof(void*)*4, x_417);
lean_ctor_set_uint16(x_420, sizeof(void*)*4 + 4, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 7, x_419);
x_421 = 0;
x_422 = 0;
x_423 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_415);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_421);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_422);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_423);
x_424 = 0;
x_425 = 0;
x_426 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_414);
lean_ctor_set(x_1, 1, x_413);
lean_ctor_set(x_1, 0, x_420);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_424);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_425);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_426);
return x_1;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_427 = lean_ctor_get(x_366, 1);
x_428 = lean_ctor_get(x_366, 2);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_366);
x_429 = lean_ctor_get(x_368, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_368, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_368, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_368, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_433 = x_368;
} else {
 lean_dec_ref(x_368);
 x_433 = lean_box(0);
}
x_434 = 1;
x_435 = 0;
x_436 = 0;
x_437 = 0;
if (lean_is_scalar(x_433)) {
 x_438 = lean_alloc_ctor(1, 4, 8);
} else {
 x_438 = x_433;
}
lean_ctor_set(x_438, 0, x_367);
lean_ctor_set(x_438, 1, x_427);
lean_ctor_set(x_438, 2, x_428);
lean_ctor_set(x_438, 3, x_429);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_438, sizeof(void*)*4, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*4 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_442, 0, x_432);
lean_ctor_set(x_442, 1, x_57);
lean_ctor_set(x_442, 2, x_58);
lean_ctor_set(x_442, 3, x_59);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_442, sizeof(void*)*4, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*4 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 7, x_441);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 3, x_442);
lean_ctor_set(x_1, 2, x_431);
lean_ctor_set(x_1, 1, x_430);
lean_ctor_set(x_1, 0, x_438);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
}
else
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_366);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint32_t x_450; uint16_t x_451; uint8_t x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_447 = lean_ctor_get(x_366, 3);
lean_dec(x_447);
x_448 = lean_ctor_get(x_366, 0);
lean_dec(x_448);
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_449);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_450);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_451);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_452);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; 
x_456 = lean_ctor_get(x_366, 1);
x_457 = lean_ctor_get(x_366, 2);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_366);
x_458 = 0;
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_462, 0, x_367);
lean_ctor_set(x_462, 1, x_456);
lean_ctor_set(x_462, 2, x_457);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 6, x_458);
lean_ctor_set_uint32(x_462, sizeof(void*)*4, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*4 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
lean_ctor_set(x_1, 0, x_462);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_463);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_464);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_465);
return x_1;
}
}
}
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_367, sizeof(void*)*4 + 6);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_366);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_468 = lean_ctor_get(x_366, 1);
x_469 = lean_ctor_get(x_366, 2);
x_470 = lean_ctor_get(x_366, 3);
x_471 = lean_ctor_get(x_366, 0);
lean_dec(x_471);
x_472 = !lean_is_exclusive(x_367);
if (x_472 == 0)
{
uint8_t x_473; uint32_t x_474; uint16_t x_475; uint8_t x_476; uint32_t x_477; uint16_t x_478; uint8_t x_479; uint32_t x_480; uint16_t x_481; uint8_t x_482; 
x_473 = 1;
x_474 = 0;
x_475 = 0;
x_476 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_474);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_475);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_476);
x_477 = 0;
x_478 = 0;
x_479 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_477);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_478);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_479);
x_480 = 0;
x_481 = 0;
x_482 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_367);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_480);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_482);
return x_1;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; uint32_t x_488; uint16_t x_489; uint8_t x_490; lean_object* x_491; uint32_t x_492; uint16_t x_493; uint8_t x_494; uint32_t x_495; uint16_t x_496; uint8_t x_497; 
x_483 = lean_ctor_get(x_367, 0);
x_484 = lean_ctor_get(x_367, 1);
x_485 = lean_ctor_get(x_367, 2);
x_486 = lean_ctor_get(x_367, 3);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_367);
x_487 = 1;
x_488 = 0;
x_489 = 0;
x_490 = 0;
x_491 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_491, 0, x_483);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_485);
lean_ctor_set(x_491, 3, x_486);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_491, sizeof(void*)*4, x_488);
lean_ctor_set_uint16(x_491, sizeof(void*)*4 + 4, x_489);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 7, x_490);
x_492 = 0;
x_493 = 0;
x_494 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_492);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_493);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_494);
x_495 = 0;
x_496 = 0;
x_497 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_491);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_495);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_496);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_497);
return x_1;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint32_t x_507; uint16_t x_508; uint8_t x_509; lean_object* x_510; uint32_t x_511; uint16_t x_512; uint8_t x_513; lean_object* x_514; uint32_t x_515; uint16_t x_516; uint8_t x_517; 
x_498 = lean_ctor_get(x_366, 1);
x_499 = lean_ctor_get(x_366, 2);
x_500 = lean_ctor_get(x_366, 3);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_366);
x_501 = lean_ctor_get(x_367, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_367, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_367, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_367, 3);
lean_inc(x_504);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_505 = x_367;
} else {
 lean_dec_ref(x_367);
 x_505 = lean_box(0);
}
x_506 = 1;
x_507 = 0;
x_508 = 0;
x_509 = 0;
if (lean_is_scalar(x_505)) {
 x_510 = lean_alloc_ctor(1, 4, 8);
} else {
 x_510 = x_505;
}
lean_ctor_set(x_510, 0, x_501);
lean_ctor_set(x_510, 1, x_502);
lean_ctor_set(x_510, 2, x_503);
lean_ctor_set(x_510, 3, x_504);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_510, sizeof(void*)*4, x_507);
lean_ctor_set_uint16(x_510, sizeof(void*)*4 + 4, x_508);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 7, x_509);
x_511 = 0;
x_512 = 0;
x_513 = 0;
x_514 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_57);
lean_ctor_set(x_514, 2, x_58);
lean_ctor_set(x_514, 3, x_59);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_514, sizeof(void*)*4, x_511);
lean_ctor_set_uint16(x_514, sizeof(void*)*4 + 4, x_512);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 7, x_513);
x_515 = 0;
x_516 = 0;
x_517 = 0;
lean_ctor_set(x_1, 3, x_514);
lean_ctor_set(x_1, 2, x_499);
lean_ctor_set(x_1, 1, x_498);
lean_ctor_set(x_1, 0, x_510);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_515);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_516);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_517);
return x_1;
}
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_366, 3);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
uint8_t x_519; 
x_519 = !lean_is_exclusive(x_366);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint32_t x_523; uint16_t x_524; uint8_t x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_520 = lean_ctor_get(x_366, 3);
lean_dec(x_520);
x_521 = lean_ctor_get(x_366, 0);
lean_dec(x_521);
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_522);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_523);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_524);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_525);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; uint32_t x_536; uint16_t x_537; uint8_t x_538; 
x_529 = lean_ctor_get(x_366, 1);
x_530 = lean_ctor_get(x_366, 2);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_366);
x_531 = 0;
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_535, 0, x_367);
lean_ctor_set(x_535, 1, x_529);
lean_ctor_set(x_535, 2, x_530);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 6, x_531);
lean_ctor_set_uint32(x_535, sizeof(void*)*4, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*4 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 7, x_534);
x_536 = 0;
x_537 = 0;
x_538 = 0;
lean_ctor_set(x_1, 0, x_535);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_536);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_537);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_538);
return x_1;
}
}
else
{
uint8_t x_539; 
x_539 = lean_ctor_get_uint8(x_518, sizeof(void*)*4 + 6);
if (x_539 == 0)
{
uint8_t x_540; 
lean_free_object(x_1);
x_540 = !lean_is_exclusive(x_366);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_541 = lean_ctor_get(x_366, 1);
x_542 = lean_ctor_get(x_366, 2);
x_543 = lean_ctor_get(x_366, 3);
lean_dec(x_543);
x_544 = lean_ctor_get(x_366, 0);
lean_dec(x_544);
x_545 = !lean_is_exclusive(x_518);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint32_t x_550; uint16_t x_551; uint8_t x_552; uint8_t x_553; 
x_546 = lean_ctor_get(x_518, 0);
x_547 = lean_ctor_get(x_518, 1);
x_548 = lean_ctor_get(x_518, 2);
x_549 = lean_ctor_get(x_518, 3);
x_550 = 0;
x_551 = 0;
x_552 = 0;
lean_inc(x_367);
lean_ctor_set(x_518, 3, x_546);
lean_ctor_set(x_518, 2, x_542);
lean_ctor_set(x_518, 1, x_541);
lean_ctor_set(x_518, 0, x_367);
x_553 = !lean_is_exclusive(x_367);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; uint32_t x_561; uint16_t x_562; uint8_t x_563; 
x_554 = lean_ctor_get(x_367, 3);
lean_dec(x_554);
x_555 = lean_ctor_get(x_367, 2);
lean_dec(x_555);
x_556 = lean_ctor_get(x_367, 1);
lean_dec(x_556);
x_557 = lean_ctor_get(x_367, 0);
lean_dec(x_557);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_367, 3, x_59);
lean_ctor_set(x_367, 2, x_58);
lean_ctor_set(x_367, 1, x_57);
lean_ctor_set(x_367, 0, x_549);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_560);
x_561 = 0;
x_562 = 0;
x_563 = 0;
lean_ctor_set(x_366, 3, x_367);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_561);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_562);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_563);
return x_366;
}
else
{
uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; uint32_t x_568; uint16_t x_569; uint8_t x_570; 
lean_dec(x_367);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_567, 0, x_549);
lean_ctor_set(x_567, 1, x_57);
lean_ctor_set(x_567, 2, x_58);
lean_ctor_set(x_567, 3, x_59);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_567, sizeof(void*)*4, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*4 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 7, x_566);
x_568 = 0;
x_569 = 0;
x_570 = 0;
lean_ctor_set(x_366, 3, x_567);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_568);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_569);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_570);
return x_366;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint32_t x_575; uint16_t x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; uint32_t x_580; uint16_t x_581; uint8_t x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; 
x_571 = lean_ctor_get(x_518, 0);
x_572 = lean_ctor_get(x_518, 1);
x_573 = lean_ctor_get(x_518, 2);
x_574 = lean_ctor_get(x_518, 3);
lean_inc(x_574);
lean_inc(x_573);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_518);
x_575 = 0;
x_576 = 0;
x_577 = 0;
lean_inc(x_367);
x_578 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_578, 0, x_367);
lean_ctor_set(x_578, 1, x_541);
lean_ctor_set(x_578, 2, x_542);
lean_ctor_set(x_578, 3, x_571);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_579 = x_367;
} else {
 lean_dec_ref(x_367);
 x_579 = lean_box(0);
}
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_578, sizeof(void*)*4, x_575);
lean_ctor_set_uint16(x_578, sizeof(void*)*4 + 4, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 7, x_577);
x_580 = 0;
x_581 = 0;
x_582 = 0;
if (lean_is_scalar(x_579)) {
 x_583 = lean_alloc_ctor(1, 4, 8);
} else {
 x_583 = x_579;
}
lean_ctor_set(x_583, 0, x_574);
lean_ctor_set(x_583, 1, x_57);
lean_ctor_set(x_583, 2, x_58);
lean_ctor_set(x_583, 3, x_59);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_583, sizeof(void*)*4, x_580);
lean_ctor_set_uint16(x_583, sizeof(void*)*4 + 4, x_581);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 7, x_582);
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_ctor_set(x_366, 3, x_583);
lean_ctor_set(x_366, 2, x_573);
lean_ctor_set(x_366, 1, x_572);
lean_ctor_set(x_366, 0, x_578);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_586);
return x_366;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint32_t x_594; uint16_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; uint32_t x_603; uint16_t x_604; uint8_t x_605; lean_object* x_606; 
x_587 = lean_ctor_get(x_366, 1);
x_588 = lean_ctor_get(x_366, 2);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_366);
x_589 = lean_ctor_get(x_518, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_518, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_518, 2);
lean_inc(x_591);
x_592 = lean_ctor_get(x_518, 3);
lean_inc(x_592);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 lean_ctor_release(x_518, 3);
 x_593 = x_518;
} else {
 lean_dec_ref(x_518);
 x_593 = lean_box(0);
}
x_594 = 0;
x_595 = 0;
x_596 = 0;
lean_inc(x_367);
if (lean_is_scalar(x_593)) {
 x_597 = lean_alloc_ctor(1, 4, 8);
} else {
 x_597 = x_593;
}
lean_ctor_set(x_597, 0, x_367);
lean_ctor_set(x_597, 1, x_587);
lean_ctor_set(x_597, 2, x_588);
lean_ctor_set(x_597, 3, x_589);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_598 = x_367;
} else {
 lean_dec_ref(x_367);
 x_598 = lean_box(0);
}
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_597, sizeof(void*)*4, x_594);
lean_ctor_set_uint16(x_597, sizeof(void*)*4 + 4, x_595);
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 7, x_596);
x_599 = 0;
x_600 = 0;
x_601 = 0;
if (lean_is_scalar(x_598)) {
 x_602 = lean_alloc_ctor(1, 4, 8);
} else {
 x_602 = x_598;
}
lean_ctor_set(x_602, 0, x_592);
lean_ctor_set(x_602, 1, x_57);
lean_ctor_set(x_602, 2, x_58);
lean_ctor_set(x_602, 3, x_59);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_602, sizeof(void*)*4, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*4 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 7, x_601);
x_603 = 0;
x_604 = 0;
x_605 = 0;
x_606 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_606, 0, x_597);
lean_ctor_set(x_606, 1, x_590);
lean_ctor_set(x_606, 2, x_591);
lean_ctor_set(x_606, 3, x_602);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_606, sizeof(void*)*4, x_603);
lean_ctor_set_uint16(x_606, sizeof(void*)*4 + 4, x_604);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 7, x_605);
return x_606;
}
}
else
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_366);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_ctor_get(x_366, 3);
lean_dec(x_608);
x_609 = lean_ctor_get(x_366, 0);
lean_dec(x_609);
x_610 = !lean_is_exclusive(x_367);
if (x_610 == 0)
{
uint32_t x_611; uint16_t x_612; uint8_t x_613; uint8_t x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; uint32_t x_618; uint16_t x_619; uint8_t x_620; 
x_611 = 0;
x_612 = 0;
x_613 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_611);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_612);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_613);
x_614 = 0;
x_615 = 0;
x_616 = 0;
x_617 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_614);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_617);
x_618 = 0;
x_619 = 0;
x_620 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_618);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_619);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_620);
return x_1;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint32_t x_625; uint16_t x_626; uint8_t x_627; lean_object* x_628; uint8_t x_629; uint32_t x_630; uint16_t x_631; uint8_t x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; 
x_621 = lean_ctor_get(x_367, 0);
x_622 = lean_ctor_get(x_367, 1);
x_623 = lean_ctor_get(x_367, 2);
x_624 = lean_ctor_get(x_367, 3);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_367);
x_625 = 0;
x_626 = 0;
x_627 = 0;
x_628 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_628, 0, x_621);
lean_ctor_set(x_628, 1, x_622);
lean_ctor_set(x_628, 2, x_623);
lean_ctor_set(x_628, 3, x_624);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_628, sizeof(void*)*4, x_625);
lean_ctor_set_uint16(x_628, sizeof(void*)*4 + 4, x_626);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 7, x_627);
x_629 = 0;
x_630 = 0;
x_631 = 0;
x_632 = 0;
lean_ctor_set(x_366, 0, x_628);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_629);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_630);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_631);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_632);
x_633 = 0;
x_634 = 0;
x_635 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_635);
return x_1;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint32_t x_643; uint16_t x_644; uint8_t x_645; lean_object* x_646; uint8_t x_647; uint32_t x_648; uint16_t x_649; uint8_t x_650; lean_object* x_651; uint32_t x_652; uint16_t x_653; uint8_t x_654; 
x_636 = lean_ctor_get(x_366, 1);
x_637 = lean_ctor_get(x_366, 2);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_366);
x_638 = lean_ctor_get(x_367, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_367, 1);
lean_inc(x_639);
x_640 = lean_ctor_get(x_367, 2);
lean_inc(x_640);
x_641 = lean_ctor_get(x_367, 3);
lean_inc(x_641);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_642 = x_367;
} else {
 lean_dec_ref(x_367);
 x_642 = lean_box(0);
}
x_643 = 0;
x_644 = 0;
x_645 = 0;
if (lean_is_scalar(x_642)) {
 x_646 = lean_alloc_ctor(1, 4, 8);
} else {
 x_646 = x_642;
}
lean_ctor_set(x_646, 0, x_638);
lean_ctor_set(x_646, 1, x_639);
lean_ctor_set(x_646, 2, x_640);
lean_ctor_set(x_646, 3, x_641);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_646, sizeof(void*)*4, x_643);
lean_ctor_set_uint16(x_646, sizeof(void*)*4 + 4, x_644);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 7, x_645);
x_647 = 0;
x_648 = 0;
x_649 = 0;
x_650 = 0;
x_651 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_651, 0, x_646);
lean_ctor_set(x_651, 1, x_636);
lean_ctor_set(x_651, 2, x_637);
lean_ctor_set(x_651, 3, x_518);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 6, x_647);
lean_ctor_set_uint32(x_651, sizeof(void*)*4, x_648);
lean_ctor_set_uint16(x_651, sizeof(void*)*4 + 4, x_649);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 7, x_650);
x_652 = 0;
x_653 = 0;
x_654 = 0;
lean_ctor_set(x_1, 0, x_651);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_652);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_653);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_654);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint32_t x_659; uint8_t x_660; 
x_655 = lean_ctor_get(x_1, 0);
x_656 = lean_ctor_get(x_1, 1);
x_657 = lean_ctor_get(x_1, 2);
x_658 = lean_ctor_get(x_1, 3);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_1);
x_659 = lean_unbox_uint32(x_656);
x_660 = x_2 < x_659;
if (x_660 == 0)
{
uint32_t x_661; uint8_t x_662; 
x_661 = lean_unbox_uint32(x_656);
x_662 = x_661 < x_2;
if (x_662 == 0)
{
uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_657);
lean_dec(x_656);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_box_uint32(x_2);
x_667 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_667, 0, x_655);
lean_ctor_set(x_667, 1, x_666);
lean_ctor_set(x_667, 2, x_3);
lean_ctor_set(x_667, 3, x_658);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_667, sizeof(void*)*4, x_663);
lean_ctor_set_uint16(x_667, sizeof(void*)*4 + 4, x_664);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 7, x_665);
return x_667;
}
else
{
uint8_t x_668; 
x_668 = l_RBNode_isRed___rarg(x_658);
if (x_668 == 0)
{
lean_object* x_669; uint32_t x_670; uint16_t x_671; uint8_t x_672; lean_object* x_673; 
x_669 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_658, x_2, x_3);
x_670 = 0;
x_671 = 0;
x_672 = 0;
x_673 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_673, 0, x_655);
lean_ctor_set(x_673, 1, x_656);
lean_ctor_set(x_673, 2, x_657);
lean_ctor_set(x_673, 3, x_669);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_673, sizeof(void*)*4, x_670);
lean_ctor_set_uint16(x_673, sizeof(void*)*4 + 4, x_671);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 7, x_672);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_658, x_2, x_3);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_674, 3);
lean_inc(x_676);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; uint32_t x_681; uint16_t x_682; uint8_t x_683; lean_object* x_684; uint8_t x_685; uint32_t x_686; uint16_t x_687; uint8_t x_688; lean_object* x_689; 
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 2);
lean_inc(x_678);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_679 = x_674;
} else {
 lean_dec_ref(x_674);
 x_679 = lean_box(0);
}
x_680 = 0;
x_681 = 0;
x_682 = 0;
x_683 = 0;
if (lean_is_scalar(x_679)) {
 x_684 = lean_alloc_ctor(1, 4, 8);
} else {
 x_684 = x_679;
}
lean_ctor_set(x_684, 0, x_676);
lean_ctor_set(x_684, 1, x_677);
lean_ctor_set(x_684, 2, x_678);
lean_ctor_set(x_684, 3, x_676);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 6, x_680);
lean_ctor_set_uint32(x_684, sizeof(void*)*4, x_681);
lean_ctor_set_uint16(x_684, sizeof(void*)*4 + 4, x_682);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 7, x_683);
x_685 = 1;
x_686 = 0;
x_687 = 0;
x_688 = 0;
x_689 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_689, 0, x_655);
lean_ctor_set(x_689, 1, x_656);
lean_ctor_set(x_689, 2, x_657);
lean_ctor_set(x_689, 3, x_684);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 6, x_685);
lean_ctor_set_uint32(x_689, sizeof(void*)*4, x_686);
lean_ctor_set_uint16(x_689, sizeof(void*)*4 + 4, x_687);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 7, x_688);
return x_689;
}
else
{
uint8_t x_690; 
x_690 = lean_ctor_get_uint8(x_676, sizeof(void*)*4 + 6);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; uint32_t x_700; uint16_t x_701; uint8_t x_702; lean_object* x_703; uint32_t x_704; uint16_t x_705; uint8_t x_706; lean_object* x_707; uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; 
x_691 = lean_ctor_get(x_674, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_674, 2);
lean_inc(x_692);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_693 = x_674;
} else {
 lean_dec_ref(x_674);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_676, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_676, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_676, 2);
lean_inc(x_696);
x_697 = lean_ctor_get(x_676, 3);
lean_inc(x_697);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 lean_ctor_release(x_676, 2);
 lean_ctor_release(x_676, 3);
 x_698 = x_676;
} else {
 lean_dec_ref(x_676);
 x_698 = lean_box(0);
}
x_699 = 1;
x_700 = 0;
x_701 = 0;
x_702 = 0;
if (lean_is_scalar(x_698)) {
 x_703 = lean_alloc_ctor(1, 4, 8);
} else {
 x_703 = x_698;
}
lean_ctor_set(x_703, 0, x_655);
lean_ctor_set(x_703, 1, x_656);
lean_ctor_set(x_703, 2, x_657);
lean_ctor_set(x_703, 3, x_675);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_703, sizeof(void*)*4, x_700);
lean_ctor_set_uint16(x_703, sizeof(void*)*4 + 4, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 7, x_702);
x_704 = 0;
x_705 = 0;
x_706 = 0;
if (lean_is_scalar(x_693)) {
 x_707 = lean_alloc_ctor(1, 4, 8);
} else {
 x_707 = x_693;
}
lean_ctor_set(x_707, 0, x_694);
lean_ctor_set(x_707, 1, x_695);
lean_ctor_set(x_707, 2, x_696);
lean_ctor_set(x_707, 3, x_697);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_707, sizeof(void*)*4, x_704);
lean_ctor_set_uint16(x_707, sizeof(void*)*4 + 4, x_705);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 7, x_706);
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_711, 0, x_703);
lean_ctor_set(x_711, 1, x_691);
lean_ctor_set(x_711, 2, x_692);
lean_ctor_set(x_711, 3, x_707);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_711, sizeof(void*)*4, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*4 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 7, x_710);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint32_t x_716; uint16_t x_717; uint8_t x_718; lean_object* x_719; uint32_t x_720; uint16_t x_721; uint8_t x_722; lean_object* x_723; 
x_712 = lean_ctor_get(x_674, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_674, 2);
lean_inc(x_713);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_714 = x_674;
} else {
 lean_dec_ref(x_674);
 x_714 = lean_box(0);
}
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = 0;
if (lean_is_scalar(x_714)) {
 x_719 = lean_alloc_ctor(1, 4, 8);
} else {
 x_719 = x_714;
}
lean_ctor_set(x_719, 0, x_675);
lean_ctor_set(x_719, 1, x_712);
lean_ctor_set(x_719, 2, x_713);
lean_ctor_set(x_719, 3, x_676);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 6, x_715);
lean_ctor_set_uint32(x_719, sizeof(void*)*4, x_716);
lean_ctor_set_uint16(x_719, sizeof(void*)*4 + 4, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 7, x_718);
x_720 = 0;
x_721 = 0;
x_722 = 0;
x_723 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_723, 0, x_655);
lean_ctor_set(x_723, 1, x_656);
lean_ctor_set(x_723, 2, x_657);
lean_ctor_set(x_723, 3, x_719);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_723, sizeof(void*)*4, x_720);
lean_ctor_set_uint16(x_723, sizeof(void*)*4 + 4, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 7, x_722);
return x_723;
}
}
}
else
{
uint8_t x_724; 
x_724 = lean_ctor_get_uint8(x_675, sizeof(void*)*4 + 6);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; uint32_t x_735; uint16_t x_736; uint8_t x_737; lean_object* x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_725 = lean_ctor_get(x_674, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_674, 2);
lean_inc(x_726);
x_727 = lean_ctor_get(x_674, 3);
lean_inc(x_727);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_728 = x_674;
} else {
 lean_dec_ref(x_674);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_675, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_675, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_675, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_675, 3);
lean_inc(x_732);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_733 = x_675;
} else {
 lean_dec_ref(x_675);
 x_733 = lean_box(0);
}
x_734 = 1;
x_735 = 0;
x_736 = 0;
x_737 = 0;
if (lean_is_scalar(x_733)) {
 x_738 = lean_alloc_ctor(1, 4, 8);
} else {
 x_738 = x_733;
}
lean_ctor_set(x_738, 0, x_655);
lean_ctor_set(x_738, 1, x_656);
lean_ctor_set(x_738, 2, x_657);
lean_ctor_set(x_738, 3, x_729);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_738, sizeof(void*)*4, x_735);
lean_ctor_set_uint16(x_738, sizeof(void*)*4 + 4, x_736);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 7, x_737);
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_728)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_728;
}
lean_ctor_set(x_742, 0, x_732);
lean_ctor_set(x_742, 1, x_725);
lean_ctor_set(x_742, 2, x_726);
lean_ctor_set(x_742, 3, x_727);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_738);
lean_ctor_set(x_746, 1, x_730);
lean_ctor_set(x_746, 2, x_731);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
lean_object* x_747; 
x_747 = lean_ctor_get(x_674, 3);
lean_inc(x_747);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; uint32_t x_752; uint16_t x_753; uint8_t x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; 
x_748 = lean_ctor_get(x_674, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_674, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_750 = x_674;
} else {
 lean_dec_ref(x_674);
 x_750 = lean_box(0);
}
x_751 = 0;
x_752 = 0;
x_753 = 0;
x_754 = 0;
if (lean_is_scalar(x_750)) {
 x_755 = lean_alloc_ctor(1, 4, 8);
} else {
 x_755 = x_750;
}
lean_ctor_set(x_755, 0, x_675);
lean_ctor_set(x_755, 1, x_748);
lean_ctor_set(x_755, 2, x_749);
lean_ctor_set(x_755, 3, x_747);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 6, x_751);
lean_ctor_set_uint32(x_755, sizeof(void*)*4, x_752);
lean_ctor_set_uint16(x_755, sizeof(void*)*4 + 4, x_753);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 7, x_754);
x_756 = 0;
x_757 = 0;
x_758 = 0;
x_759 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_759, 0, x_655);
lean_ctor_set(x_759, 1, x_656);
lean_ctor_set(x_759, 2, x_657);
lean_ctor_set(x_759, 3, x_755);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
return x_759;
}
else
{
uint8_t x_760; 
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*4 + 6);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; uint32_t x_769; uint16_t x_770; uint8_t x_771; lean_object* x_772; lean_object* x_773; uint32_t x_774; uint16_t x_775; uint8_t x_776; lean_object* x_777; uint32_t x_778; uint16_t x_779; uint8_t x_780; lean_object* x_781; 
x_761 = lean_ctor_get(x_674, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_674, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_763 = x_674;
} else {
 lean_dec_ref(x_674);
 x_763 = lean_box(0);
}
x_764 = lean_ctor_get(x_747, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_747, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_747, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_747, 3);
lean_inc(x_767);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 lean_ctor_release(x_747, 2);
 lean_ctor_release(x_747, 3);
 x_768 = x_747;
} else {
 lean_dec_ref(x_747);
 x_768 = lean_box(0);
}
x_769 = 0;
x_770 = 0;
x_771 = 0;
lean_inc(x_675);
if (lean_is_scalar(x_768)) {
 x_772 = lean_alloc_ctor(1, 4, 8);
} else {
 x_772 = x_768;
}
lean_ctor_set(x_772, 0, x_655);
lean_ctor_set(x_772, 1, x_656);
lean_ctor_set(x_772, 2, x_657);
lean_ctor_set(x_772, 3, x_675);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_773 = x_675;
} else {
 lean_dec_ref(x_675);
 x_773 = lean_box(0);
}
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_772, sizeof(void*)*4, x_769);
lean_ctor_set_uint16(x_772, sizeof(void*)*4 + 4, x_770);
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 7, x_771);
x_774 = 0;
x_775 = 0;
x_776 = 0;
if (lean_is_scalar(x_773)) {
 x_777 = lean_alloc_ctor(1, 4, 8);
} else {
 x_777 = x_773;
}
lean_ctor_set(x_777, 0, x_764);
lean_ctor_set(x_777, 1, x_765);
lean_ctor_set(x_777, 2, x_766);
lean_ctor_set(x_777, 3, x_767);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_777, sizeof(void*)*4, x_774);
lean_ctor_set_uint16(x_777, sizeof(void*)*4 + 4, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 7, x_776);
x_778 = 0;
x_779 = 0;
x_780 = 0;
if (lean_is_scalar(x_763)) {
 x_781 = lean_alloc_ctor(1, 4, 8);
} else {
 x_781 = x_763;
}
lean_ctor_set(x_781, 0, x_772);
lean_ctor_set(x_781, 1, x_761);
lean_ctor_set(x_781, 2, x_762);
lean_ctor_set(x_781, 3, x_777);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_781, sizeof(void*)*4, x_778);
lean_ctor_set_uint16(x_781, sizeof(void*)*4 + 4, x_779);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 7, x_780);
return x_781;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; uint32_t x_790; uint16_t x_791; uint8_t x_792; lean_object* x_793; uint8_t x_794; uint32_t x_795; uint16_t x_796; uint8_t x_797; lean_object* x_798; uint32_t x_799; uint16_t x_800; uint8_t x_801; lean_object* x_802; 
x_782 = lean_ctor_get(x_674, 1);
lean_inc(x_782);
x_783 = lean_ctor_get(x_674, 2);
lean_inc(x_783);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_784 = x_674;
} else {
 lean_dec_ref(x_674);
 x_784 = lean_box(0);
}
x_785 = lean_ctor_get(x_675, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_675, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_675, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_675, 3);
lean_inc(x_788);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_789 = x_675;
} else {
 lean_dec_ref(x_675);
 x_789 = lean_box(0);
}
x_790 = 0;
x_791 = 0;
x_792 = 0;
if (lean_is_scalar(x_789)) {
 x_793 = lean_alloc_ctor(1, 4, 8);
} else {
 x_793 = x_789;
}
lean_ctor_set(x_793, 0, x_785);
lean_ctor_set(x_793, 1, x_786);
lean_ctor_set(x_793, 2, x_787);
lean_ctor_set(x_793, 3, x_788);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_793, sizeof(void*)*4, x_790);
lean_ctor_set_uint16(x_793, sizeof(void*)*4 + 4, x_791);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 7, x_792);
x_794 = 0;
x_795 = 0;
x_796 = 0;
x_797 = 0;
if (lean_is_scalar(x_784)) {
 x_798 = lean_alloc_ctor(1, 4, 8);
} else {
 x_798 = x_784;
}
lean_ctor_set(x_798, 0, x_793);
lean_ctor_set(x_798, 1, x_782);
lean_ctor_set(x_798, 2, x_783);
lean_ctor_set(x_798, 3, x_747);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 6, x_794);
lean_ctor_set_uint32(x_798, sizeof(void*)*4, x_795);
lean_ctor_set_uint16(x_798, sizeof(void*)*4 + 4, x_796);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 7, x_797);
x_799 = 0;
x_800 = 0;
x_801 = 0;
x_802 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_802, 0, x_655);
lean_ctor_set(x_802, 1, x_656);
lean_ctor_set(x_802, 2, x_657);
lean_ctor_set(x_802, 3, x_798);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_802, sizeof(void*)*4, x_799);
lean_ctor_set_uint16(x_802, sizeof(void*)*4 + 4, x_800);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 7, x_801);
return x_802;
}
}
}
}
}
}
}
else
{
uint8_t x_803; 
x_803 = l_RBNode_isRed___rarg(x_655);
if (x_803 == 0)
{
lean_object* x_804; uint32_t x_805; uint16_t x_806; uint8_t x_807; lean_object* x_808; 
x_804 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_655, x_2, x_3);
x_805 = 0;
x_806 = 0;
x_807 = 0;
x_808 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_808, 0, x_804);
lean_ctor_set(x_808, 1, x_656);
lean_ctor_set(x_808, 2, x_657);
lean_ctor_set(x_808, 3, x_658);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_808, sizeof(void*)*4, x_805);
lean_ctor_set_uint16(x_808, sizeof(void*)*4 + 4, x_806);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 7, x_807);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_655, x_2, x_3);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_809, 3);
lean_inc(x_811);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; uint32_t x_816; uint16_t x_817; uint8_t x_818; lean_object* x_819; uint8_t x_820; uint32_t x_821; uint16_t x_822; uint8_t x_823; lean_object* x_824; 
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
x_813 = lean_ctor_get(x_809, 2);
lean_inc(x_813);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_814 = x_809;
} else {
 lean_dec_ref(x_809);
 x_814 = lean_box(0);
}
x_815 = 0;
x_816 = 0;
x_817 = 0;
x_818 = 0;
if (lean_is_scalar(x_814)) {
 x_819 = lean_alloc_ctor(1, 4, 8);
} else {
 x_819 = x_814;
}
lean_ctor_set(x_819, 0, x_811);
lean_ctor_set(x_819, 1, x_812);
lean_ctor_set(x_819, 2, x_813);
lean_ctor_set(x_819, 3, x_811);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 6, x_815);
lean_ctor_set_uint32(x_819, sizeof(void*)*4, x_816);
lean_ctor_set_uint16(x_819, sizeof(void*)*4 + 4, x_817);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 7, x_818);
x_820 = 1;
x_821 = 0;
x_822 = 0;
x_823 = 0;
x_824 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_824, 0, x_819);
lean_ctor_set(x_824, 1, x_656);
lean_ctor_set(x_824, 2, x_657);
lean_ctor_set(x_824, 3, x_658);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 6, x_820);
lean_ctor_set_uint32(x_824, sizeof(void*)*4, x_821);
lean_ctor_set_uint16(x_824, sizeof(void*)*4 + 4, x_822);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 7, x_823);
return x_824;
}
else
{
uint8_t x_825; 
x_825 = lean_ctor_get_uint8(x_811, sizeof(void*)*4 + 6);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; uint32_t x_835; uint16_t x_836; uint8_t x_837; lean_object* x_838; uint32_t x_839; uint16_t x_840; uint8_t x_841; lean_object* x_842; uint32_t x_843; uint16_t x_844; uint8_t x_845; lean_object* x_846; 
x_826 = lean_ctor_get(x_809, 1);
lean_inc(x_826);
x_827 = lean_ctor_get(x_809, 2);
lean_inc(x_827);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_828 = x_809;
} else {
 lean_dec_ref(x_809);
 x_828 = lean_box(0);
}
x_829 = lean_ctor_get(x_811, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_811, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_811, 2);
lean_inc(x_831);
x_832 = lean_ctor_get(x_811, 3);
lean_inc(x_832);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 lean_ctor_release(x_811, 2);
 lean_ctor_release(x_811, 3);
 x_833 = x_811;
} else {
 lean_dec_ref(x_811);
 x_833 = lean_box(0);
}
x_834 = 1;
x_835 = 0;
x_836 = 0;
x_837 = 0;
if (lean_is_scalar(x_833)) {
 x_838 = lean_alloc_ctor(1, 4, 8);
} else {
 x_838 = x_833;
}
lean_ctor_set(x_838, 0, x_810);
lean_ctor_set(x_838, 1, x_826);
lean_ctor_set(x_838, 2, x_827);
lean_ctor_set(x_838, 3, x_829);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_838, sizeof(void*)*4, x_835);
lean_ctor_set_uint16(x_838, sizeof(void*)*4 + 4, x_836);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 7, x_837);
x_839 = 0;
x_840 = 0;
x_841 = 0;
if (lean_is_scalar(x_828)) {
 x_842 = lean_alloc_ctor(1, 4, 8);
} else {
 x_842 = x_828;
}
lean_ctor_set(x_842, 0, x_832);
lean_ctor_set(x_842, 1, x_656);
lean_ctor_set(x_842, 2, x_657);
lean_ctor_set(x_842, 3, x_658);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_842, sizeof(void*)*4, x_839);
lean_ctor_set_uint16(x_842, sizeof(void*)*4 + 4, x_840);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 7, x_841);
x_843 = 0;
x_844 = 0;
x_845 = 0;
x_846 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_846, 0, x_838);
lean_ctor_set(x_846, 1, x_830);
lean_ctor_set(x_846, 2, x_831);
lean_ctor_set(x_846, 3, x_842);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_846, sizeof(void*)*4, x_843);
lean_ctor_set_uint16(x_846, sizeof(void*)*4 + 4, x_844);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 7, x_845);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; uint32_t x_851; uint16_t x_852; uint8_t x_853; lean_object* x_854; uint32_t x_855; uint16_t x_856; uint8_t x_857; lean_object* x_858; 
x_847 = lean_ctor_get(x_809, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_809, 2);
lean_inc(x_848);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_849 = x_809;
} else {
 lean_dec_ref(x_809);
 x_849 = lean_box(0);
}
x_850 = 0;
x_851 = 0;
x_852 = 0;
x_853 = 0;
if (lean_is_scalar(x_849)) {
 x_854 = lean_alloc_ctor(1, 4, 8);
} else {
 x_854 = x_849;
}
lean_ctor_set(x_854, 0, x_810);
lean_ctor_set(x_854, 1, x_847);
lean_ctor_set(x_854, 2, x_848);
lean_ctor_set(x_854, 3, x_811);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 6, x_850);
lean_ctor_set_uint32(x_854, sizeof(void*)*4, x_851);
lean_ctor_set_uint16(x_854, sizeof(void*)*4 + 4, x_852);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 7, x_853);
x_855 = 0;
x_856 = 0;
x_857 = 0;
x_858 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_858, 0, x_854);
lean_ctor_set(x_858, 1, x_656);
lean_ctor_set(x_858, 2, x_657);
lean_ctor_set(x_858, 3, x_658);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_858, sizeof(void*)*4, x_855);
lean_ctor_set_uint16(x_858, sizeof(void*)*4 + 4, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 7, x_857);
return x_858;
}
}
}
else
{
uint8_t x_859; 
x_859 = lean_ctor_get_uint8(x_810, sizeof(void*)*4 + 6);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; uint32_t x_870; uint16_t x_871; uint8_t x_872; lean_object* x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_860 = lean_ctor_get(x_809, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_809, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_809, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_863 = x_809;
} else {
 lean_dec_ref(x_809);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_810, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_810, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_810, 2);
lean_inc(x_866);
x_867 = lean_ctor_get(x_810, 3);
lean_inc(x_867);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_868 = x_810;
} else {
 lean_dec_ref(x_810);
 x_868 = lean_box(0);
}
x_869 = 1;
x_870 = 0;
x_871 = 0;
x_872 = 0;
if (lean_is_scalar(x_868)) {
 x_873 = lean_alloc_ctor(1, 4, 8);
} else {
 x_873 = x_868;
}
lean_ctor_set(x_873, 0, x_864);
lean_ctor_set(x_873, 1, x_865);
lean_ctor_set(x_873, 2, x_866);
lean_ctor_set(x_873, 3, x_867);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_873, sizeof(void*)*4, x_870);
lean_ctor_set_uint16(x_873, sizeof(void*)*4 + 4, x_871);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 7, x_872);
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_863)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_863;
}
lean_ctor_set(x_877, 0, x_862);
lean_ctor_set(x_877, 1, x_656);
lean_ctor_set(x_877, 2, x_657);
lean_ctor_set(x_877, 3, x_658);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_860);
lean_ctor_set(x_881, 2, x_861);
lean_ctor_set(x_881, 3, x_877);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
lean_object* x_882; 
x_882 = lean_ctor_get(x_809, 3);
lean_inc(x_882);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; uint32_t x_887; uint16_t x_888; uint8_t x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; 
x_883 = lean_ctor_get(x_809, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_809, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_885 = x_809;
} else {
 lean_dec_ref(x_809);
 x_885 = lean_box(0);
}
x_886 = 0;
x_887 = 0;
x_888 = 0;
x_889 = 0;
if (lean_is_scalar(x_885)) {
 x_890 = lean_alloc_ctor(1, 4, 8);
} else {
 x_890 = x_885;
}
lean_ctor_set(x_890, 0, x_810);
lean_ctor_set(x_890, 1, x_883);
lean_ctor_set(x_890, 2, x_884);
lean_ctor_set(x_890, 3, x_882);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 6, x_886);
lean_ctor_set_uint32(x_890, sizeof(void*)*4, x_887);
lean_ctor_set_uint16(x_890, sizeof(void*)*4 + 4, x_888);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 7, x_889);
x_891 = 0;
x_892 = 0;
x_893 = 0;
x_894 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_656);
lean_ctor_set(x_894, 2, x_657);
lean_ctor_set(x_894, 3, x_658);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
return x_894;
}
else
{
uint8_t x_895; 
x_895 = lean_ctor_get_uint8(x_882, sizeof(void*)*4 + 6);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint32_t x_904; uint16_t x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; uint32_t x_909; uint16_t x_910; uint8_t x_911; lean_object* x_912; uint32_t x_913; uint16_t x_914; uint8_t x_915; lean_object* x_916; 
x_896 = lean_ctor_get(x_809, 1);
lean_inc(x_896);
x_897 = lean_ctor_get(x_809, 2);
lean_inc(x_897);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_898 = x_809;
} else {
 lean_dec_ref(x_809);
 x_898 = lean_box(0);
}
x_899 = lean_ctor_get(x_882, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_882, 1);
lean_inc(x_900);
x_901 = lean_ctor_get(x_882, 2);
lean_inc(x_901);
x_902 = lean_ctor_get(x_882, 3);
lean_inc(x_902);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 lean_ctor_release(x_882, 2);
 lean_ctor_release(x_882, 3);
 x_903 = x_882;
} else {
 lean_dec_ref(x_882);
 x_903 = lean_box(0);
}
x_904 = 0;
x_905 = 0;
x_906 = 0;
lean_inc(x_810);
if (lean_is_scalar(x_903)) {
 x_907 = lean_alloc_ctor(1, 4, 8);
} else {
 x_907 = x_903;
}
lean_ctor_set(x_907, 0, x_810);
lean_ctor_set(x_907, 1, x_896);
lean_ctor_set(x_907, 2, x_897);
lean_ctor_set(x_907, 3, x_899);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_908 = x_810;
} else {
 lean_dec_ref(x_810);
 x_908 = lean_box(0);
}
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_907, sizeof(void*)*4, x_904);
lean_ctor_set_uint16(x_907, sizeof(void*)*4 + 4, x_905);
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 7, x_906);
x_909 = 0;
x_910 = 0;
x_911 = 0;
if (lean_is_scalar(x_908)) {
 x_912 = lean_alloc_ctor(1, 4, 8);
} else {
 x_912 = x_908;
}
lean_ctor_set(x_912, 0, x_902);
lean_ctor_set(x_912, 1, x_656);
lean_ctor_set(x_912, 2, x_657);
lean_ctor_set(x_912, 3, x_658);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_912, sizeof(void*)*4, x_909);
lean_ctor_set_uint16(x_912, sizeof(void*)*4 + 4, x_910);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 7, x_911);
x_913 = 0;
x_914 = 0;
x_915 = 0;
if (lean_is_scalar(x_898)) {
 x_916 = lean_alloc_ctor(1, 4, 8);
} else {
 x_916 = x_898;
}
lean_ctor_set(x_916, 0, x_907);
lean_ctor_set(x_916, 1, x_900);
lean_ctor_set(x_916, 2, x_901);
lean_ctor_set(x_916, 3, x_912);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_916, sizeof(void*)*4, x_913);
lean_ctor_set_uint16(x_916, sizeof(void*)*4 + 4, x_914);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 7, x_915);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint32_t x_925; uint16_t x_926; uint8_t x_927; lean_object* x_928; uint8_t x_929; uint32_t x_930; uint16_t x_931; uint8_t x_932; lean_object* x_933; uint32_t x_934; uint16_t x_935; uint8_t x_936; lean_object* x_937; 
x_917 = lean_ctor_get(x_809, 1);
lean_inc(x_917);
x_918 = lean_ctor_get(x_809, 2);
lean_inc(x_918);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_919 = x_809;
} else {
 lean_dec_ref(x_809);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_810, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_810, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_810, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_810, 3);
lean_inc(x_923);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_924 = x_810;
} else {
 lean_dec_ref(x_810);
 x_924 = lean_box(0);
}
x_925 = 0;
x_926 = 0;
x_927 = 0;
if (lean_is_scalar(x_924)) {
 x_928 = lean_alloc_ctor(1, 4, 8);
} else {
 x_928 = x_924;
}
lean_ctor_set(x_928, 0, x_920);
lean_ctor_set(x_928, 1, x_921);
lean_ctor_set(x_928, 2, x_922);
lean_ctor_set(x_928, 3, x_923);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_928, sizeof(void*)*4, x_925);
lean_ctor_set_uint16(x_928, sizeof(void*)*4 + 4, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 7, x_927);
x_929 = 0;
x_930 = 0;
x_931 = 0;
x_932 = 0;
if (lean_is_scalar(x_919)) {
 x_933 = lean_alloc_ctor(1, 4, 8);
} else {
 x_933 = x_919;
}
lean_ctor_set(x_933, 0, x_928);
lean_ctor_set(x_933, 1, x_917);
lean_ctor_set(x_933, 2, x_918);
lean_ctor_set(x_933, 3, x_882);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 6, x_929);
lean_ctor_set_uint32(x_933, sizeof(void*)*4, x_930);
lean_ctor_set_uint16(x_933, sizeof(void*)*4 + 4, x_931);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 7, x_932);
x_934 = 0;
x_935 = 0;
x_936 = 0;
x_937 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_937, 0, x_933);
lean_ctor_set(x_937, 1, x_656);
lean_ctor_set(x_937, 2, x_657);
lean_ctor_set(x_937, 3, x_658);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_937, sizeof(void*)*4, x_934);
lean_ctor_set_uint16(x_937, sizeof(void*)*4 + 4, x_935);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 7, x_936);
return x_937;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_box_uint32(x_2);
x_9 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_9, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 7, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_unbox_uint32(x_13);
x_17 = x_2 < x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = lean_unbox_uint32(x_13);
x_19 = x_18 < x_2;
if (x_19 == 0)
{
uint32_t x_20; uint16_t x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = 0;
x_21 = 0;
x_22 = 0;
x_23 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_20);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_22);
return x_1;
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_15, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 3, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; 
x_28 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_12, x_2, x_3);
x_29 = 0;
x_30 = 0;
x_31 = 0;
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_29);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_36 = lean_unbox_uint32(x_33);
x_37 = x_2 < x_36;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = lean_unbox_uint32(x_33);
x_39 = x_38 < x_2;
if (x_39 == 0)
{
uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_33);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_box_uint32(x_2);
x_44 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_44, sizeof(void*)*4, x_40);
lean_ctor_set_uint16(x_44, sizeof(void*)*4 + 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 7, x_42);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint16_t x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_35, x_2, x_3);
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_49, sizeof(void*)*4, x_46);
lean_ctor_set_uint16(x_49, sizeof(void*)*4 + 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 7, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint32_t x_51; uint16_t x_52; uint8_t x_53; lean_object* x_54; 
x_50 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_32, x_2, x_3);
x_51 = 0;
x_52 = 0;
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_34);
lean_ctor_set(x_54, 3, x_35);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_54, sizeof(void*)*4, x_51);
lean_ctor_set_uint16(x_54, sizeof(void*)*4 + 4, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 7, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
x_60 = lean_unbox_uint32(x_57);
x_61 = x_2 < x_60;
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = lean_unbox_uint32(x_57);
x_63 = x_62 < x_2;
if (x_63 == 0)
{
uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_64);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_66);
return x_1;
}
else
{
uint8_t x_68; 
x_68 = l_RBNode_isRed___rarg(x_59);
if (x_68 == 0)
{
lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; 
x_69 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_59, x_2, x_3);
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_1, 3, x_69);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_72);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_59, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; uint8_t x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; 
x_77 = lean_ctor_get(x_73, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
lean_ctor_set(x_73, 0, x_75);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_82);
x_83 = 1;
x_84 = 0;
x_85 = 0;
x_86 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_83);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_84);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_86);
return x_1;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint32_t x_90; uint16_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint32_t x_95; uint16_t x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_73, 1);
x_88 = lean_ctor_get(x_73, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = 0;
x_90 = 0;
x_91 = 0;
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_75);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 6, x_89);
lean_ctor_set_uint32(x_93, sizeof(void*)*4, x_90);
lean_ctor_set_uint16(x_93, sizeof(void*)*4 + 4, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 7, x_92);
x_94 = 1;
x_95 = 0;
x_96 = 0;
x_97 = 0;
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_94);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_95);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_97);
return x_1;
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_75, sizeof(void*)*4 + 6);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_73);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_73, 1);
x_101 = lean_ctor_get(x_73, 2);
x_102 = lean_ctor_get(x_73, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_73, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_75);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint32_t x_110; uint16_t x_111; uint8_t x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; uint32_t x_116; uint16_t x_117; uint8_t x_118; 
x_105 = lean_ctor_get(x_75, 0);
x_106 = lean_ctor_get(x_75, 1);
x_107 = lean_ctor_get(x_75, 2);
x_108 = lean_ctor_get(x_75, 3);
x_109 = 1;
x_110 = 0;
x_111 = 0;
x_112 = 0;
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_75, sizeof(void*)*4, x_110);
lean_ctor_set_uint16(x_75, sizeof(void*)*4 + 4, x_111);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 7, x_112);
x_113 = 0;
x_114 = 0;
x_115 = 0;
lean_ctor_set(x_73, 3, x_108);
lean_ctor_set(x_73, 2, x_107);
lean_ctor_set(x_73, 1, x_106);
lean_ctor_set(x_73, 0, x_105);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_113);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_114);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_115);
x_116 = 0;
x_117 = 0;
x_118 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_116);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_118);
return x_1;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; uint32_t x_128; uint16_t x_129; uint8_t x_130; uint32_t x_131; uint16_t x_132; uint8_t x_133; 
x_119 = lean_ctor_get(x_75, 0);
x_120 = lean_ctor_get(x_75, 1);
x_121 = lean_ctor_get(x_75, 2);
x_122 = lean_ctor_get(x_75, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_75);
x_123 = 1;
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_127, 0, x_56);
lean_ctor_set(x_127, 1, x_57);
lean_ctor_set(x_127, 2, x_58);
lean_ctor_set(x_127, 3, x_74);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_127, sizeof(void*)*4, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*4 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 7, x_126);
x_128 = 0;
x_129 = 0;
x_130 = 0;
lean_ctor_set(x_73, 3, x_122);
lean_ctor_set(x_73, 2, x_121);
lean_ctor_set(x_73, 1, x_120);
lean_ctor_set(x_73, 0, x_119);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_128);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_129);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_130);
x_131 = 0;
x_132 = 0;
x_133 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_131);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_133);
return x_1;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint32_t x_142; uint16_t x_143; uint8_t x_144; lean_object* x_145; uint32_t x_146; uint16_t x_147; uint8_t x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_73, 1);
x_135 = lean_ctor_get(x_73, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_73);
x_136 = lean_ctor_get(x_75, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_75, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_75, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_75, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_140 = x_75;
} else {
 lean_dec_ref(x_75);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = 0;
x_143 = 0;
x_144 = 0;
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(1, 4, 8);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_56);
lean_ctor_set(x_145, 1, x_57);
lean_ctor_set(x_145, 2, x_58);
lean_ctor_set(x_145, 3, x_74);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_145, sizeof(void*)*4, x_142);
lean_ctor_set_uint16(x_145, sizeof(void*)*4 + 4, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 7, x_144);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_149, sizeof(void*)*4, x_146);
lean_ctor_set_uint16(x_149, sizeof(void*)*4 + 4, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 7, x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_149);
lean_ctor_set(x_1, 2, x_135);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_145);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_73);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint32_t x_157; uint16_t x_158; uint8_t x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_73, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_73, 0);
lean_dec(x_155);
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_156);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_157);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_158);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_159);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; uint32_t x_170; uint16_t x_171; uint8_t x_172; 
x_163 = lean_ctor_get(x_73, 1);
x_164 = lean_ctor_get(x_73, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_73);
x_165 = 0;
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_169, 0, x_74);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 3, x_75);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 6, x_165);
lean_ctor_set_uint32(x_169, sizeof(void*)*4, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*4 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 7, x_168);
x_170 = 0;
x_171 = 0;
x_172 = 0;
lean_ctor_set(x_1, 3, x_169);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_170);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_171);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_172);
return x_1;
}
}
}
}
else
{
uint8_t x_173; 
x_173 = lean_ctor_get_uint8(x_74, sizeof(void*)*4 + 6);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_73);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_73, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_74);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint32_t x_182; uint16_t x_183; uint8_t x_184; uint32_t x_185; uint16_t x_186; uint8_t x_187; uint32_t x_188; uint16_t x_189; uint8_t x_190; 
x_177 = lean_ctor_get(x_74, 0);
x_178 = lean_ctor_get(x_74, 1);
x_179 = lean_ctor_get(x_74, 2);
x_180 = lean_ctor_get(x_74, 3);
x_181 = 1;
x_182 = 0;
x_183 = 0;
x_184 = 0;
lean_ctor_set(x_74, 3, x_177);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_182);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_183);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_184);
x_185 = 0;
x_186 = 0;
x_187 = 0;
lean_ctor_set(x_73, 0, x_180);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_185);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_186);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_187);
x_188 = 0;
x_189 = 0;
x_190 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_179);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_188);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_190);
return x_1;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint32_t x_196; uint16_t x_197; uint8_t x_198; lean_object* x_199; uint32_t x_200; uint16_t x_201; uint8_t x_202; uint32_t x_203; uint16_t x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_74, 0);
x_192 = lean_ctor_get(x_74, 1);
x_193 = lean_ctor_get(x_74, 2);
x_194 = lean_ctor_get(x_74, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_74);
x_195 = 1;
x_196 = 0;
x_197 = 0;
x_198 = 0;
x_199 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_199, 0, x_56);
lean_ctor_set(x_199, 1, x_57);
lean_ctor_set(x_199, 2, x_58);
lean_ctor_set(x_199, 3, x_191);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_199, sizeof(void*)*4, x_196);
lean_ctor_set_uint16(x_199, sizeof(void*)*4 + 4, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 7, x_198);
x_200 = 0;
x_201 = 0;
x_202 = 0;
lean_ctor_set(x_73, 0, x_194);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_200);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_201);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_202);
x_203 = 0;
x_204 = 0;
x_205 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_193);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_203);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_205);
return x_1;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint32_t x_215; uint16_t x_216; uint8_t x_217; lean_object* x_218; uint32_t x_219; uint16_t x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; 
x_206 = lean_ctor_get(x_73, 1);
x_207 = lean_ctor_get(x_73, 2);
x_208 = lean_ctor_get(x_73, 3);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_73);
x_209 = lean_ctor_get(x_74, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_74, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_74, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_74, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_213 = x_74;
} else {
 lean_dec_ref(x_74);
 x_213 = lean_box(0);
}
x_214 = 1;
x_215 = 0;
x_216 = 0;
x_217 = 0;
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(1, 4, 8);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_56);
lean_ctor_set(x_218, 1, x_57);
lean_ctor_set(x_218, 2, x_58);
lean_ctor_set(x_218, 3, x_209);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_218, sizeof(void*)*4, x_215);
lean_ctor_set_uint16(x_218, sizeof(void*)*4 + 4, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 7, x_217);
x_219 = 0;
x_220 = 0;
x_221 = 0;
x_222 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_206);
lean_ctor_set(x_222, 2, x_207);
lean_ctor_set(x_222, 3, x_208);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_222, sizeof(void*)*4, x_219);
lean_ctor_set_uint16(x_222, sizeof(void*)*4 + 4, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 7, x_221);
x_223 = 0;
x_224 = 0;
x_225 = 0;
lean_ctor_set(x_1, 3, x_222);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_218);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_223);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_225);
return x_1;
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_73, 3);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_73);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint32_t x_231; uint16_t x_232; uint8_t x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_228 = lean_ctor_get(x_73, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_73, 0);
lean_dec(x_229);
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_230);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_231);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_232);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_233);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; uint32_t x_244; uint16_t x_245; uint8_t x_246; 
x_237 = lean_ctor_get(x_73, 1);
x_238 = lean_ctor_get(x_73, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_73);
x_239 = 0;
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_243, 0, x_74);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_226);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 6, x_239);
lean_ctor_set_uint32(x_243, sizeof(void*)*4, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*4 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 7, x_242);
x_244 = 0;
x_245 = 0;
x_246 = 0;
lean_ctor_set(x_1, 3, x_243);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_244);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_246);
return x_1;
}
}
else
{
uint8_t x_247; 
x_247 = lean_ctor_get_uint8(x_226, sizeof(void*)*4 + 6);
if (x_247 == 0)
{
uint8_t x_248; 
lean_free_object(x_1);
x_248 = !lean_is_exclusive(x_73);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_73, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_73, 0);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_226);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint32_t x_256; uint16_t x_257; uint8_t x_258; uint8_t x_259; 
x_252 = lean_ctor_get(x_226, 0);
x_253 = lean_ctor_get(x_226, 1);
x_254 = lean_ctor_get(x_226, 2);
x_255 = lean_ctor_get(x_226, 3);
x_256 = 0;
x_257 = 0;
x_258 = 0;
lean_inc(x_74);
lean_ctor_set(x_226, 3, x_74);
lean_ctor_set(x_226, 2, x_58);
lean_ctor_set(x_226, 1, x_57);
lean_ctor_set(x_226, 0, x_56);
x_259 = !lean_is_exclusive(x_74);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; 
x_260 = lean_ctor_get(x_74, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_74, 2);
lean_dec(x_261);
x_262 = lean_ctor_get(x_74, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_74, 3, x_255);
lean_ctor_set(x_74, 2, x_254);
lean_ctor_set(x_74, 1, x_253);
lean_ctor_set(x_74, 0, x_252);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_266);
x_267 = 0;
x_268 = 0;
x_269 = 0;
lean_ctor_set(x_73, 3, x_74);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_267);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_268);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_269);
return x_73;
}
else
{
uint32_t x_270; uint16_t x_271; uint8_t x_272; lean_object* x_273; uint32_t x_274; uint16_t x_275; uint8_t x_276; 
lean_dec(x_74);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_270 = 0;
x_271 = 0;
x_272 = 0;
x_273 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_273, 0, x_252);
lean_ctor_set(x_273, 1, x_253);
lean_ctor_set(x_273, 2, x_254);
lean_ctor_set(x_273, 3, x_255);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_273, sizeof(void*)*4, x_270);
lean_ctor_set_uint16(x_273, sizeof(void*)*4 + 4, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 7, x_272);
x_274 = 0;
x_275 = 0;
x_276 = 0;
lean_ctor_set(x_73, 3, x_273);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_274);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_275);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_276);
return x_73;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint32_t x_281; uint16_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint32_t x_286; uint16_t x_287; uint8_t x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; 
x_277 = lean_ctor_get(x_226, 0);
x_278 = lean_ctor_get(x_226, 1);
x_279 = lean_ctor_get(x_226, 2);
x_280 = lean_ctor_get(x_226, 3);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_226);
x_281 = 0;
x_282 = 0;
x_283 = 0;
lean_inc(x_74);
x_284 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_284, 0, x_56);
lean_ctor_set(x_284, 1, x_57);
lean_ctor_set(x_284, 2, x_58);
lean_ctor_set(x_284, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_285 = x_74;
} else {
 lean_dec_ref(x_74);
 x_285 = lean_box(0);
}
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_284, sizeof(void*)*4, x_281);
lean_ctor_set_uint16(x_284, sizeof(void*)*4 + 4, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 7, x_283);
x_286 = 0;
x_287 = 0;
x_288 = 0;
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(1, 4, 8);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_278);
lean_ctor_set(x_289, 2, x_279);
lean_ctor_set(x_289, 3, x_280);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_289, sizeof(void*)*4, x_286);
lean_ctor_set_uint16(x_289, sizeof(void*)*4 + 4, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 7, x_288);
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_ctor_set(x_73, 3, x_289);
lean_ctor_set(x_73, 0, x_284);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_292);
return x_73;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint32_t x_300; uint16_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint32_t x_305; uint16_t x_306; uint8_t x_307; lean_object* x_308; uint32_t x_309; uint16_t x_310; uint8_t x_311; lean_object* x_312; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_73);
x_295 = lean_ctor_get(x_226, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_226, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_226, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_226, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 x_299 = x_226;
} else {
 lean_dec_ref(x_226);
 x_299 = lean_box(0);
}
x_300 = 0;
x_301 = 0;
x_302 = 0;
lean_inc(x_74);
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(1, 4, 8);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_56);
lean_ctor_set(x_303, 1, x_57);
lean_ctor_set(x_303, 2, x_58);
lean_ctor_set(x_303, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_304 = x_74;
} else {
 lean_dec_ref(x_74);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_303, sizeof(void*)*4, x_300);
lean_ctor_set_uint16(x_303, sizeof(void*)*4 + 4, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 7, x_302);
x_305 = 0;
x_306 = 0;
x_307 = 0;
if (lean_is_scalar(x_304)) {
 x_308 = lean_alloc_ctor(1, 4, 8);
} else {
 x_308 = x_304;
}
lean_ctor_set(x_308, 0, x_295);
lean_ctor_set(x_308, 1, x_296);
lean_ctor_set(x_308, 2, x_297);
lean_ctor_set(x_308, 3, x_298);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_308, sizeof(void*)*4, x_305);
lean_ctor_set_uint16(x_308, sizeof(void*)*4 + 4, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 7, x_307);
x_309 = 0;
x_310 = 0;
x_311 = 0;
x_312 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_293);
lean_ctor_set(x_312, 2, x_294);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_312, sizeof(void*)*4, x_309);
lean_ctor_set_uint16(x_312, sizeof(void*)*4 + 4, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 7, x_311);
return x_312;
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_73);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_73, 3);
lean_dec(x_314);
x_315 = lean_ctor_get(x_73, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_74);
if (x_316 == 0)
{
uint32_t x_317; uint16_t x_318; uint8_t x_319; uint8_t x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; uint32_t x_324; uint16_t x_325; uint8_t x_326; 
x_317 = 0;
x_318 = 0;
x_319 = 0;
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_317);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_318);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_319);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_320);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_323);
x_324 = 0;
x_325 = 0;
x_326 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_324);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_326);
return x_1;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; uint32_t x_336; uint16_t x_337; uint8_t x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; 
x_327 = lean_ctor_get(x_74, 0);
x_328 = lean_ctor_get(x_74, 1);
x_329 = lean_ctor_get(x_74, 2);
x_330 = lean_ctor_get(x_74, 3);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_74);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_334, 2, x_329);
lean_ctor_set(x_334, 3, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_334, sizeof(void*)*4, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*4 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 7, x_333);
x_335 = 0;
x_336 = 0;
x_337 = 0;
x_338 = 0;
lean_ctor_set(x_73, 0, x_334);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_335);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_336);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_337);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_338);
x_339 = 0;
x_340 = 0;
x_341 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_341);
return x_1;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint32_t x_349; uint16_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; uint32_t x_354; uint16_t x_355; uint8_t x_356; lean_object* x_357; uint32_t x_358; uint16_t x_359; uint8_t x_360; 
x_342 = lean_ctor_get(x_73, 1);
x_343 = lean_ctor_get(x_73, 2);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_73);
x_344 = lean_ctor_get(x_74, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_74, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_74, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_74, 3);
lean_inc(x_347);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_348 = x_74;
} else {
 lean_dec_ref(x_74);
 x_348 = lean_box(0);
}
x_349 = 0;
x_350 = 0;
x_351 = 0;
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(1, 4, 8);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_345);
lean_ctor_set(x_352, 2, x_346);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_352, sizeof(void*)*4, x_349);
lean_ctor_set_uint16(x_352, sizeof(void*)*4 + 4, x_350);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 7, x_351);
x_353 = 0;
x_354 = 0;
x_355 = 0;
x_356 = 0;
x_357 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_342);
lean_ctor_set(x_357, 2, x_343);
lean_ctor_set(x_357, 3, x_226);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_353);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_354);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_356);
x_358 = 0;
x_359 = 0;
x_360 = 0;
lean_ctor_set(x_1, 3, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_358);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_359);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_360);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_361; 
x_361 = l_RBNode_isRed___rarg(x_56);
if (x_361 == 0)
{
lean_object* x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; 
x_362 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_56, x_2, x_3);
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_1, 0, x_362);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_365);
return x_1;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_56, x_2, x_3);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_366);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; uint8_t x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; 
x_370 = lean_ctor_get(x_366, 3);
lean_dec(x_370);
x_371 = lean_ctor_get(x_366, 0);
lean_dec(x_371);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
lean_ctor_set(x_366, 0, x_368);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_375);
x_376 = 1;
x_377 = 0;
x_378 = 0;
x_379 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_376);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_377);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_378);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_379);
return x_1;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; uint8_t x_387; uint32_t x_388; uint16_t x_389; uint8_t x_390; 
x_380 = lean_ctor_get(x_366, 1);
x_381 = lean_ctor_get(x_366, 2);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_366);
x_382 = 0;
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_386, 0, x_368);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_368);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 6, x_382);
lean_ctor_set_uint32(x_386, sizeof(void*)*4, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*4 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 7, x_385);
x_387 = 1;
x_388 = 0;
x_389 = 0;
x_390 = 0;
lean_ctor_set(x_1, 0, x_386);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_387);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_388);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_389);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_390);
return x_1;
}
}
else
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_368, sizeof(void*)*4 + 6);
if (x_391 == 0)
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_366);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_393 = lean_ctor_get(x_366, 1);
x_394 = lean_ctor_get(x_366, 2);
x_395 = lean_ctor_get(x_366, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_366, 0);
lean_dec(x_396);
x_397 = !lean_is_exclusive(x_368);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint32_t x_403; uint16_t x_404; uint8_t x_405; uint32_t x_406; uint16_t x_407; uint8_t x_408; uint32_t x_409; uint16_t x_410; uint8_t x_411; 
x_398 = lean_ctor_get(x_368, 0);
x_399 = lean_ctor_get(x_368, 1);
x_400 = lean_ctor_get(x_368, 2);
x_401 = lean_ctor_get(x_368, 3);
x_402 = 1;
x_403 = 0;
x_404 = 0;
x_405 = 0;
lean_ctor_set(x_368, 3, x_398);
lean_ctor_set(x_368, 2, x_394);
lean_ctor_set(x_368, 1, x_393);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_368, sizeof(void*)*4, x_403);
lean_ctor_set_uint16(x_368, sizeof(void*)*4 + 4, x_404);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 7, x_405);
x_406 = 0;
x_407 = 0;
x_408 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_401);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_406);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_407);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_408);
x_409 = 0;
x_410 = 0;
x_411 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_400);
lean_ctor_set(x_1, 1, x_399);
lean_ctor_set(x_1, 0, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_409);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_411);
return x_1;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; uint32_t x_417; uint16_t x_418; uint8_t x_419; lean_object* x_420; uint32_t x_421; uint16_t x_422; uint8_t x_423; uint32_t x_424; uint16_t x_425; uint8_t x_426; 
x_412 = lean_ctor_get(x_368, 0);
x_413 = lean_ctor_get(x_368, 1);
x_414 = lean_ctor_get(x_368, 2);
x_415 = lean_ctor_get(x_368, 3);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_368);
x_416 = 1;
x_417 = 0;
x_418 = 0;
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_420, 0, x_367);
lean_ctor_set(x_420, 1, x_393);
lean_ctor_set(x_420, 2, x_394);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_420, sizeof(void*)*4, x_417);
lean_ctor_set_uint16(x_420, sizeof(void*)*4 + 4, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 7, x_419);
x_421 = 0;
x_422 = 0;
x_423 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_415);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_421);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_422);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_423);
x_424 = 0;
x_425 = 0;
x_426 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_414);
lean_ctor_set(x_1, 1, x_413);
lean_ctor_set(x_1, 0, x_420);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_424);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_425);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_426);
return x_1;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_427 = lean_ctor_get(x_366, 1);
x_428 = lean_ctor_get(x_366, 2);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_366);
x_429 = lean_ctor_get(x_368, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_368, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_368, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_368, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_433 = x_368;
} else {
 lean_dec_ref(x_368);
 x_433 = lean_box(0);
}
x_434 = 1;
x_435 = 0;
x_436 = 0;
x_437 = 0;
if (lean_is_scalar(x_433)) {
 x_438 = lean_alloc_ctor(1, 4, 8);
} else {
 x_438 = x_433;
}
lean_ctor_set(x_438, 0, x_367);
lean_ctor_set(x_438, 1, x_427);
lean_ctor_set(x_438, 2, x_428);
lean_ctor_set(x_438, 3, x_429);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_438, sizeof(void*)*4, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*4 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_442, 0, x_432);
lean_ctor_set(x_442, 1, x_57);
lean_ctor_set(x_442, 2, x_58);
lean_ctor_set(x_442, 3, x_59);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_442, sizeof(void*)*4, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*4 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 7, x_441);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 3, x_442);
lean_ctor_set(x_1, 2, x_431);
lean_ctor_set(x_1, 1, x_430);
lean_ctor_set(x_1, 0, x_438);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
}
else
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_366);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint32_t x_450; uint16_t x_451; uint8_t x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_447 = lean_ctor_get(x_366, 3);
lean_dec(x_447);
x_448 = lean_ctor_get(x_366, 0);
lean_dec(x_448);
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_449);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_450);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_451);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_452);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; 
x_456 = lean_ctor_get(x_366, 1);
x_457 = lean_ctor_get(x_366, 2);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_366);
x_458 = 0;
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_462, 0, x_367);
lean_ctor_set(x_462, 1, x_456);
lean_ctor_set(x_462, 2, x_457);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 6, x_458);
lean_ctor_set_uint32(x_462, sizeof(void*)*4, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*4 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
lean_ctor_set(x_1, 0, x_462);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_463);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_464);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_465);
return x_1;
}
}
}
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_367, sizeof(void*)*4 + 6);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_366);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_468 = lean_ctor_get(x_366, 1);
x_469 = lean_ctor_get(x_366, 2);
x_470 = lean_ctor_get(x_366, 3);
x_471 = lean_ctor_get(x_366, 0);
lean_dec(x_471);
x_472 = !lean_is_exclusive(x_367);
if (x_472 == 0)
{
uint8_t x_473; uint32_t x_474; uint16_t x_475; uint8_t x_476; uint32_t x_477; uint16_t x_478; uint8_t x_479; uint32_t x_480; uint16_t x_481; uint8_t x_482; 
x_473 = 1;
x_474 = 0;
x_475 = 0;
x_476 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_474);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_475);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_476);
x_477 = 0;
x_478 = 0;
x_479 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_477);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_478);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_479);
x_480 = 0;
x_481 = 0;
x_482 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_367);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_480);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_482);
return x_1;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; uint32_t x_488; uint16_t x_489; uint8_t x_490; lean_object* x_491; uint32_t x_492; uint16_t x_493; uint8_t x_494; uint32_t x_495; uint16_t x_496; uint8_t x_497; 
x_483 = lean_ctor_get(x_367, 0);
x_484 = lean_ctor_get(x_367, 1);
x_485 = lean_ctor_get(x_367, 2);
x_486 = lean_ctor_get(x_367, 3);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_367);
x_487 = 1;
x_488 = 0;
x_489 = 0;
x_490 = 0;
x_491 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_491, 0, x_483);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_485);
lean_ctor_set(x_491, 3, x_486);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_491, sizeof(void*)*4, x_488);
lean_ctor_set_uint16(x_491, sizeof(void*)*4 + 4, x_489);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 7, x_490);
x_492 = 0;
x_493 = 0;
x_494 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_492);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_493);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_494);
x_495 = 0;
x_496 = 0;
x_497 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_491);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_495);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_496);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_497);
return x_1;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint32_t x_507; uint16_t x_508; uint8_t x_509; lean_object* x_510; uint32_t x_511; uint16_t x_512; uint8_t x_513; lean_object* x_514; uint32_t x_515; uint16_t x_516; uint8_t x_517; 
x_498 = lean_ctor_get(x_366, 1);
x_499 = lean_ctor_get(x_366, 2);
x_500 = lean_ctor_get(x_366, 3);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_366);
x_501 = lean_ctor_get(x_367, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_367, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_367, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_367, 3);
lean_inc(x_504);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_505 = x_367;
} else {
 lean_dec_ref(x_367);
 x_505 = lean_box(0);
}
x_506 = 1;
x_507 = 0;
x_508 = 0;
x_509 = 0;
if (lean_is_scalar(x_505)) {
 x_510 = lean_alloc_ctor(1, 4, 8);
} else {
 x_510 = x_505;
}
lean_ctor_set(x_510, 0, x_501);
lean_ctor_set(x_510, 1, x_502);
lean_ctor_set(x_510, 2, x_503);
lean_ctor_set(x_510, 3, x_504);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_510, sizeof(void*)*4, x_507);
lean_ctor_set_uint16(x_510, sizeof(void*)*4 + 4, x_508);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 7, x_509);
x_511 = 0;
x_512 = 0;
x_513 = 0;
x_514 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_57);
lean_ctor_set(x_514, 2, x_58);
lean_ctor_set(x_514, 3, x_59);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_514, sizeof(void*)*4, x_511);
lean_ctor_set_uint16(x_514, sizeof(void*)*4 + 4, x_512);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 7, x_513);
x_515 = 0;
x_516 = 0;
x_517 = 0;
lean_ctor_set(x_1, 3, x_514);
lean_ctor_set(x_1, 2, x_499);
lean_ctor_set(x_1, 1, x_498);
lean_ctor_set(x_1, 0, x_510);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_515);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_516);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_517);
return x_1;
}
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_366, 3);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
uint8_t x_519; 
x_519 = !lean_is_exclusive(x_366);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint32_t x_523; uint16_t x_524; uint8_t x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_520 = lean_ctor_get(x_366, 3);
lean_dec(x_520);
x_521 = lean_ctor_get(x_366, 0);
lean_dec(x_521);
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_522);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_523);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_524);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_525);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; uint32_t x_536; uint16_t x_537; uint8_t x_538; 
x_529 = lean_ctor_get(x_366, 1);
x_530 = lean_ctor_get(x_366, 2);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_366);
x_531 = 0;
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_535, 0, x_367);
lean_ctor_set(x_535, 1, x_529);
lean_ctor_set(x_535, 2, x_530);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 6, x_531);
lean_ctor_set_uint32(x_535, sizeof(void*)*4, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*4 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 7, x_534);
x_536 = 0;
x_537 = 0;
x_538 = 0;
lean_ctor_set(x_1, 0, x_535);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_536);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_537);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_538);
return x_1;
}
}
else
{
uint8_t x_539; 
x_539 = lean_ctor_get_uint8(x_518, sizeof(void*)*4 + 6);
if (x_539 == 0)
{
uint8_t x_540; 
lean_free_object(x_1);
x_540 = !lean_is_exclusive(x_366);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_541 = lean_ctor_get(x_366, 1);
x_542 = lean_ctor_get(x_366, 2);
x_543 = lean_ctor_get(x_366, 3);
lean_dec(x_543);
x_544 = lean_ctor_get(x_366, 0);
lean_dec(x_544);
x_545 = !lean_is_exclusive(x_518);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint32_t x_550; uint16_t x_551; uint8_t x_552; uint8_t x_553; 
x_546 = lean_ctor_get(x_518, 0);
x_547 = lean_ctor_get(x_518, 1);
x_548 = lean_ctor_get(x_518, 2);
x_549 = lean_ctor_get(x_518, 3);
x_550 = 0;
x_551 = 0;
x_552 = 0;
lean_inc(x_367);
lean_ctor_set(x_518, 3, x_546);
lean_ctor_set(x_518, 2, x_542);
lean_ctor_set(x_518, 1, x_541);
lean_ctor_set(x_518, 0, x_367);
x_553 = !lean_is_exclusive(x_367);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; uint32_t x_561; uint16_t x_562; uint8_t x_563; 
x_554 = lean_ctor_get(x_367, 3);
lean_dec(x_554);
x_555 = lean_ctor_get(x_367, 2);
lean_dec(x_555);
x_556 = lean_ctor_get(x_367, 1);
lean_dec(x_556);
x_557 = lean_ctor_get(x_367, 0);
lean_dec(x_557);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_367, 3, x_59);
lean_ctor_set(x_367, 2, x_58);
lean_ctor_set(x_367, 1, x_57);
lean_ctor_set(x_367, 0, x_549);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_560);
x_561 = 0;
x_562 = 0;
x_563 = 0;
lean_ctor_set(x_366, 3, x_367);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_561);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_562);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_563);
return x_366;
}
else
{
uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; uint32_t x_568; uint16_t x_569; uint8_t x_570; 
lean_dec(x_367);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_567, 0, x_549);
lean_ctor_set(x_567, 1, x_57);
lean_ctor_set(x_567, 2, x_58);
lean_ctor_set(x_567, 3, x_59);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_567, sizeof(void*)*4, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*4 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 7, x_566);
x_568 = 0;
x_569 = 0;
x_570 = 0;
lean_ctor_set(x_366, 3, x_567);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_568);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_569);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_570);
return x_366;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint32_t x_575; uint16_t x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; uint32_t x_580; uint16_t x_581; uint8_t x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; 
x_571 = lean_ctor_get(x_518, 0);
x_572 = lean_ctor_get(x_518, 1);
x_573 = lean_ctor_get(x_518, 2);
x_574 = lean_ctor_get(x_518, 3);
lean_inc(x_574);
lean_inc(x_573);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_518);
x_575 = 0;
x_576 = 0;
x_577 = 0;
lean_inc(x_367);
x_578 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_578, 0, x_367);
lean_ctor_set(x_578, 1, x_541);
lean_ctor_set(x_578, 2, x_542);
lean_ctor_set(x_578, 3, x_571);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_579 = x_367;
} else {
 lean_dec_ref(x_367);
 x_579 = lean_box(0);
}
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_578, sizeof(void*)*4, x_575);
lean_ctor_set_uint16(x_578, sizeof(void*)*4 + 4, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 7, x_577);
x_580 = 0;
x_581 = 0;
x_582 = 0;
if (lean_is_scalar(x_579)) {
 x_583 = lean_alloc_ctor(1, 4, 8);
} else {
 x_583 = x_579;
}
lean_ctor_set(x_583, 0, x_574);
lean_ctor_set(x_583, 1, x_57);
lean_ctor_set(x_583, 2, x_58);
lean_ctor_set(x_583, 3, x_59);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_583, sizeof(void*)*4, x_580);
lean_ctor_set_uint16(x_583, sizeof(void*)*4 + 4, x_581);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 7, x_582);
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_ctor_set(x_366, 3, x_583);
lean_ctor_set(x_366, 2, x_573);
lean_ctor_set(x_366, 1, x_572);
lean_ctor_set(x_366, 0, x_578);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_586);
return x_366;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint32_t x_594; uint16_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; uint32_t x_603; uint16_t x_604; uint8_t x_605; lean_object* x_606; 
x_587 = lean_ctor_get(x_366, 1);
x_588 = lean_ctor_get(x_366, 2);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_366);
x_589 = lean_ctor_get(x_518, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_518, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_518, 2);
lean_inc(x_591);
x_592 = lean_ctor_get(x_518, 3);
lean_inc(x_592);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 lean_ctor_release(x_518, 3);
 x_593 = x_518;
} else {
 lean_dec_ref(x_518);
 x_593 = lean_box(0);
}
x_594 = 0;
x_595 = 0;
x_596 = 0;
lean_inc(x_367);
if (lean_is_scalar(x_593)) {
 x_597 = lean_alloc_ctor(1, 4, 8);
} else {
 x_597 = x_593;
}
lean_ctor_set(x_597, 0, x_367);
lean_ctor_set(x_597, 1, x_587);
lean_ctor_set(x_597, 2, x_588);
lean_ctor_set(x_597, 3, x_589);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_598 = x_367;
} else {
 lean_dec_ref(x_367);
 x_598 = lean_box(0);
}
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_597, sizeof(void*)*4, x_594);
lean_ctor_set_uint16(x_597, sizeof(void*)*4 + 4, x_595);
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 7, x_596);
x_599 = 0;
x_600 = 0;
x_601 = 0;
if (lean_is_scalar(x_598)) {
 x_602 = lean_alloc_ctor(1, 4, 8);
} else {
 x_602 = x_598;
}
lean_ctor_set(x_602, 0, x_592);
lean_ctor_set(x_602, 1, x_57);
lean_ctor_set(x_602, 2, x_58);
lean_ctor_set(x_602, 3, x_59);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_602, sizeof(void*)*4, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*4 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 7, x_601);
x_603 = 0;
x_604 = 0;
x_605 = 0;
x_606 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_606, 0, x_597);
lean_ctor_set(x_606, 1, x_590);
lean_ctor_set(x_606, 2, x_591);
lean_ctor_set(x_606, 3, x_602);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_606, sizeof(void*)*4, x_603);
lean_ctor_set_uint16(x_606, sizeof(void*)*4 + 4, x_604);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 7, x_605);
return x_606;
}
}
else
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_366);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_ctor_get(x_366, 3);
lean_dec(x_608);
x_609 = lean_ctor_get(x_366, 0);
lean_dec(x_609);
x_610 = !lean_is_exclusive(x_367);
if (x_610 == 0)
{
uint32_t x_611; uint16_t x_612; uint8_t x_613; uint8_t x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; uint32_t x_618; uint16_t x_619; uint8_t x_620; 
x_611 = 0;
x_612 = 0;
x_613 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_611);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_612);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_613);
x_614 = 0;
x_615 = 0;
x_616 = 0;
x_617 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_614);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_617);
x_618 = 0;
x_619 = 0;
x_620 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_618);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_619);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_620);
return x_1;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint32_t x_625; uint16_t x_626; uint8_t x_627; lean_object* x_628; uint8_t x_629; uint32_t x_630; uint16_t x_631; uint8_t x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; 
x_621 = lean_ctor_get(x_367, 0);
x_622 = lean_ctor_get(x_367, 1);
x_623 = lean_ctor_get(x_367, 2);
x_624 = lean_ctor_get(x_367, 3);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_367);
x_625 = 0;
x_626 = 0;
x_627 = 0;
x_628 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_628, 0, x_621);
lean_ctor_set(x_628, 1, x_622);
lean_ctor_set(x_628, 2, x_623);
lean_ctor_set(x_628, 3, x_624);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_628, sizeof(void*)*4, x_625);
lean_ctor_set_uint16(x_628, sizeof(void*)*4 + 4, x_626);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 7, x_627);
x_629 = 0;
x_630 = 0;
x_631 = 0;
x_632 = 0;
lean_ctor_set(x_366, 0, x_628);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_629);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_630);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_631);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_632);
x_633 = 0;
x_634 = 0;
x_635 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_635);
return x_1;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint32_t x_643; uint16_t x_644; uint8_t x_645; lean_object* x_646; uint8_t x_647; uint32_t x_648; uint16_t x_649; uint8_t x_650; lean_object* x_651; uint32_t x_652; uint16_t x_653; uint8_t x_654; 
x_636 = lean_ctor_get(x_366, 1);
x_637 = lean_ctor_get(x_366, 2);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_366);
x_638 = lean_ctor_get(x_367, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_367, 1);
lean_inc(x_639);
x_640 = lean_ctor_get(x_367, 2);
lean_inc(x_640);
x_641 = lean_ctor_get(x_367, 3);
lean_inc(x_641);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_642 = x_367;
} else {
 lean_dec_ref(x_367);
 x_642 = lean_box(0);
}
x_643 = 0;
x_644 = 0;
x_645 = 0;
if (lean_is_scalar(x_642)) {
 x_646 = lean_alloc_ctor(1, 4, 8);
} else {
 x_646 = x_642;
}
lean_ctor_set(x_646, 0, x_638);
lean_ctor_set(x_646, 1, x_639);
lean_ctor_set(x_646, 2, x_640);
lean_ctor_set(x_646, 3, x_641);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_646, sizeof(void*)*4, x_643);
lean_ctor_set_uint16(x_646, sizeof(void*)*4 + 4, x_644);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 7, x_645);
x_647 = 0;
x_648 = 0;
x_649 = 0;
x_650 = 0;
x_651 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_651, 0, x_646);
lean_ctor_set(x_651, 1, x_636);
lean_ctor_set(x_651, 2, x_637);
lean_ctor_set(x_651, 3, x_518);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 6, x_647);
lean_ctor_set_uint32(x_651, sizeof(void*)*4, x_648);
lean_ctor_set_uint16(x_651, sizeof(void*)*4 + 4, x_649);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 7, x_650);
x_652 = 0;
x_653 = 0;
x_654 = 0;
lean_ctor_set(x_1, 0, x_651);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_652);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_653);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_654);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint32_t x_659; uint8_t x_660; 
x_655 = lean_ctor_get(x_1, 0);
x_656 = lean_ctor_get(x_1, 1);
x_657 = lean_ctor_get(x_1, 2);
x_658 = lean_ctor_get(x_1, 3);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_1);
x_659 = lean_unbox_uint32(x_656);
x_660 = x_2 < x_659;
if (x_660 == 0)
{
uint32_t x_661; uint8_t x_662; 
x_661 = lean_unbox_uint32(x_656);
x_662 = x_661 < x_2;
if (x_662 == 0)
{
uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_657);
lean_dec(x_656);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_box_uint32(x_2);
x_667 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_667, 0, x_655);
lean_ctor_set(x_667, 1, x_666);
lean_ctor_set(x_667, 2, x_3);
lean_ctor_set(x_667, 3, x_658);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_667, sizeof(void*)*4, x_663);
lean_ctor_set_uint16(x_667, sizeof(void*)*4 + 4, x_664);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 7, x_665);
return x_667;
}
else
{
uint8_t x_668; 
x_668 = l_RBNode_isRed___rarg(x_658);
if (x_668 == 0)
{
lean_object* x_669; uint32_t x_670; uint16_t x_671; uint8_t x_672; lean_object* x_673; 
x_669 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_658, x_2, x_3);
x_670 = 0;
x_671 = 0;
x_672 = 0;
x_673 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_673, 0, x_655);
lean_ctor_set(x_673, 1, x_656);
lean_ctor_set(x_673, 2, x_657);
lean_ctor_set(x_673, 3, x_669);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_673, sizeof(void*)*4, x_670);
lean_ctor_set_uint16(x_673, sizeof(void*)*4 + 4, x_671);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 7, x_672);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_658, x_2, x_3);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_674, 3);
lean_inc(x_676);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; uint32_t x_681; uint16_t x_682; uint8_t x_683; lean_object* x_684; uint8_t x_685; uint32_t x_686; uint16_t x_687; uint8_t x_688; lean_object* x_689; 
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 2);
lean_inc(x_678);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_679 = x_674;
} else {
 lean_dec_ref(x_674);
 x_679 = lean_box(0);
}
x_680 = 0;
x_681 = 0;
x_682 = 0;
x_683 = 0;
if (lean_is_scalar(x_679)) {
 x_684 = lean_alloc_ctor(1, 4, 8);
} else {
 x_684 = x_679;
}
lean_ctor_set(x_684, 0, x_676);
lean_ctor_set(x_684, 1, x_677);
lean_ctor_set(x_684, 2, x_678);
lean_ctor_set(x_684, 3, x_676);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 6, x_680);
lean_ctor_set_uint32(x_684, sizeof(void*)*4, x_681);
lean_ctor_set_uint16(x_684, sizeof(void*)*4 + 4, x_682);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 7, x_683);
x_685 = 1;
x_686 = 0;
x_687 = 0;
x_688 = 0;
x_689 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_689, 0, x_655);
lean_ctor_set(x_689, 1, x_656);
lean_ctor_set(x_689, 2, x_657);
lean_ctor_set(x_689, 3, x_684);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 6, x_685);
lean_ctor_set_uint32(x_689, sizeof(void*)*4, x_686);
lean_ctor_set_uint16(x_689, sizeof(void*)*4 + 4, x_687);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 7, x_688);
return x_689;
}
else
{
uint8_t x_690; 
x_690 = lean_ctor_get_uint8(x_676, sizeof(void*)*4 + 6);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; uint32_t x_700; uint16_t x_701; uint8_t x_702; lean_object* x_703; uint32_t x_704; uint16_t x_705; uint8_t x_706; lean_object* x_707; uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; 
x_691 = lean_ctor_get(x_674, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_674, 2);
lean_inc(x_692);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_693 = x_674;
} else {
 lean_dec_ref(x_674);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_676, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_676, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_676, 2);
lean_inc(x_696);
x_697 = lean_ctor_get(x_676, 3);
lean_inc(x_697);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 lean_ctor_release(x_676, 2);
 lean_ctor_release(x_676, 3);
 x_698 = x_676;
} else {
 lean_dec_ref(x_676);
 x_698 = lean_box(0);
}
x_699 = 1;
x_700 = 0;
x_701 = 0;
x_702 = 0;
if (lean_is_scalar(x_698)) {
 x_703 = lean_alloc_ctor(1, 4, 8);
} else {
 x_703 = x_698;
}
lean_ctor_set(x_703, 0, x_655);
lean_ctor_set(x_703, 1, x_656);
lean_ctor_set(x_703, 2, x_657);
lean_ctor_set(x_703, 3, x_675);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_703, sizeof(void*)*4, x_700);
lean_ctor_set_uint16(x_703, sizeof(void*)*4 + 4, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 7, x_702);
x_704 = 0;
x_705 = 0;
x_706 = 0;
if (lean_is_scalar(x_693)) {
 x_707 = lean_alloc_ctor(1, 4, 8);
} else {
 x_707 = x_693;
}
lean_ctor_set(x_707, 0, x_694);
lean_ctor_set(x_707, 1, x_695);
lean_ctor_set(x_707, 2, x_696);
lean_ctor_set(x_707, 3, x_697);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_707, sizeof(void*)*4, x_704);
lean_ctor_set_uint16(x_707, sizeof(void*)*4 + 4, x_705);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 7, x_706);
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_711, 0, x_703);
lean_ctor_set(x_711, 1, x_691);
lean_ctor_set(x_711, 2, x_692);
lean_ctor_set(x_711, 3, x_707);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_711, sizeof(void*)*4, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*4 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 7, x_710);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint32_t x_716; uint16_t x_717; uint8_t x_718; lean_object* x_719; uint32_t x_720; uint16_t x_721; uint8_t x_722; lean_object* x_723; 
x_712 = lean_ctor_get(x_674, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_674, 2);
lean_inc(x_713);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_714 = x_674;
} else {
 lean_dec_ref(x_674);
 x_714 = lean_box(0);
}
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = 0;
if (lean_is_scalar(x_714)) {
 x_719 = lean_alloc_ctor(1, 4, 8);
} else {
 x_719 = x_714;
}
lean_ctor_set(x_719, 0, x_675);
lean_ctor_set(x_719, 1, x_712);
lean_ctor_set(x_719, 2, x_713);
lean_ctor_set(x_719, 3, x_676);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 6, x_715);
lean_ctor_set_uint32(x_719, sizeof(void*)*4, x_716);
lean_ctor_set_uint16(x_719, sizeof(void*)*4 + 4, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 7, x_718);
x_720 = 0;
x_721 = 0;
x_722 = 0;
x_723 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_723, 0, x_655);
lean_ctor_set(x_723, 1, x_656);
lean_ctor_set(x_723, 2, x_657);
lean_ctor_set(x_723, 3, x_719);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_723, sizeof(void*)*4, x_720);
lean_ctor_set_uint16(x_723, sizeof(void*)*4 + 4, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 7, x_722);
return x_723;
}
}
}
else
{
uint8_t x_724; 
x_724 = lean_ctor_get_uint8(x_675, sizeof(void*)*4 + 6);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; uint32_t x_735; uint16_t x_736; uint8_t x_737; lean_object* x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_725 = lean_ctor_get(x_674, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_674, 2);
lean_inc(x_726);
x_727 = lean_ctor_get(x_674, 3);
lean_inc(x_727);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_728 = x_674;
} else {
 lean_dec_ref(x_674);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_675, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_675, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_675, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_675, 3);
lean_inc(x_732);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_733 = x_675;
} else {
 lean_dec_ref(x_675);
 x_733 = lean_box(0);
}
x_734 = 1;
x_735 = 0;
x_736 = 0;
x_737 = 0;
if (lean_is_scalar(x_733)) {
 x_738 = lean_alloc_ctor(1, 4, 8);
} else {
 x_738 = x_733;
}
lean_ctor_set(x_738, 0, x_655);
lean_ctor_set(x_738, 1, x_656);
lean_ctor_set(x_738, 2, x_657);
lean_ctor_set(x_738, 3, x_729);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_738, sizeof(void*)*4, x_735);
lean_ctor_set_uint16(x_738, sizeof(void*)*4 + 4, x_736);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 7, x_737);
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_728)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_728;
}
lean_ctor_set(x_742, 0, x_732);
lean_ctor_set(x_742, 1, x_725);
lean_ctor_set(x_742, 2, x_726);
lean_ctor_set(x_742, 3, x_727);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_738);
lean_ctor_set(x_746, 1, x_730);
lean_ctor_set(x_746, 2, x_731);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
lean_object* x_747; 
x_747 = lean_ctor_get(x_674, 3);
lean_inc(x_747);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; uint32_t x_752; uint16_t x_753; uint8_t x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; 
x_748 = lean_ctor_get(x_674, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_674, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_750 = x_674;
} else {
 lean_dec_ref(x_674);
 x_750 = lean_box(0);
}
x_751 = 0;
x_752 = 0;
x_753 = 0;
x_754 = 0;
if (lean_is_scalar(x_750)) {
 x_755 = lean_alloc_ctor(1, 4, 8);
} else {
 x_755 = x_750;
}
lean_ctor_set(x_755, 0, x_675);
lean_ctor_set(x_755, 1, x_748);
lean_ctor_set(x_755, 2, x_749);
lean_ctor_set(x_755, 3, x_747);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 6, x_751);
lean_ctor_set_uint32(x_755, sizeof(void*)*4, x_752);
lean_ctor_set_uint16(x_755, sizeof(void*)*4 + 4, x_753);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 7, x_754);
x_756 = 0;
x_757 = 0;
x_758 = 0;
x_759 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_759, 0, x_655);
lean_ctor_set(x_759, 1, x_656);
lean_ctor_set(x_759, 2, x_657);
lean_ctor_set(x_759, 3, x_755);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
return x_759;
}
else
{
uint8_t x_760; 
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*4 + 6);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; uint32_t x_769; uint16_t x_770; uint8_t x_771; lean_object* x_772; lean_object* x_773; uint32_t x_774; uint16_t x_775; uint8_t x_776; lean_object* x_777; uint32_t x_778; uint16_t x_779; uint8_t x_780; lean_object* x_781; 
x_761 = lean_ctor_get(x_674, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_674, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_763 = x_674;
} else {
 lean_dec_ref(x_674);
 x_763 = lean_box(0);
}
x_764 = lean_ctor_get(x_747, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_747, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_747, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_747, 3);
lean_inc(x_767);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 lean_ctor_release(x_747, 2);
 lean_ctor_release(x_747, 3);
 x_768 = x_747;
} else {
 lean_dec_ref(x_747);
 x_768 = lean_box(0);
}
x_769 = 0;
x_770 = 0;
x_771 = 0;
lean_inc(x_675);
if (lean_is_scalar(x_768)) {
 x_772 = lean_alloc_ctor(1, 4, 8);
} else {
 x_772 = x_768;
}
lean_ctor_set(x_772, 0, x_655);
lean_ctor_set(x_772, 1, x_656);
lean_ctor_set(x_772, 2, x_657);
lean_ctor_set(x_772, 3, x_675);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_773 = x_675;
} else {
 lean_dec_ref(x_675);
 x_773 = lean_box(0);
}
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_772, sizeof(void*)*4, x_769);
lean_ctor_set_uint16(x_772, sizeof(void*)*4 + 4, x_770);
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 7, x_771);
x_774 = 0;
x_775 = 0;
x_776 = 0;
if (lean_is_scalar(x_773)) {
 x_777 = lean_alloc_ctor(1, 4, 8);
} else {
 x_777 = x_773;
}
lean_ctor_set(x_777, 0, x_764);
lean_ctor_set(x_777, 1, x_765);
lean_ctor_set(x_777, 2, x_766);
lean_ctor_set(x_777, 3, x_767);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_777, sizeof(void*)*4, x_774);
lean_ctor_set_uint16(x_777, sizeof(void*)*4 + 4, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 7, x_776);
x_778 = 0;
x_779 = 0;
x_780 = 0;
if (lean_is_scalar(x_763)) {
 x_781 = lean_alloc_ctor(1, 4, 8);
} else {
 x_781 = x_763;
}
lean_ctor_set(x_781, 0, x_772);
lean_ctor_set(x_781, 1, x_761);
lean_ctor_set(x_781, 2, x_762);
lean_ctor_set(x_781, 3, x_777);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_781, sizeof(void*)*4, x_778);
lean_ctor_set_uint16(x_781, sizeof(void*)*4 + 4, x_779);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 7, x_780);
return x_781;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; uint32_t x_790; uint16_t x_791; uint8_t x_792; lean_object* x_793; uint8_t x_794; uint32_t x_795; uint16_t x_796; uint8_t x_797; lean_object* x_798; uint32_t x_799; uint16_t x_800; uint8_t x_801; lean_object* x_802; 
x_782 = lean_ctor_get(x_674, 1);
lean_inc(x_782);
x_783 = lean_ctor_get(x_674, 2);
lean_inc(x_783);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_784 = x_674;
} else {
 lean_dec_ref(x_674);
 x_784 = lean_box(0);
}
x_785 = lean_ctor_get(x_675, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_675, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_675, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_675, 3);
lean_inc(x_788);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_789 = x_675;
} else {
 lean_dec_ref(x_675);
 x_789 = lean_box(0);
}
x_790 = 0;
x_791 = 0;
x_792 = 0;
if (lean_is_scalar(x_789)) {
 x_793 = lean_alloc_ctor(1, 4, 8);
} else {
 x_793 = x_789;
}
lean_ctor_set(x_793, 0, x_785);
lean_ctor_set(x_793, 1, x_786);
lean_ctor_set(x_793, 2, x_787);
lean_ctor_set(x_793, 3, x_788);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_793, sizeof(void*)*4, x_790);
lean_ctor_set_uint16(x_793, sizeof(void*)*4 + 4, x_791);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 7, x_792);
x_794 = 0;
x_795 = 0;
x_796 = 0;
x_797 = 0;
if (lean_is_scalar(x_784)) {
 x_798 = lean_alloc_ctor(1, 4, 8);
} else {
 x_798 = x_784;
}
lean_ctor_set(x_798, 0, x_793);
lean_ctor_set(x_798, 1, x_782);
lean_ctor_set(x_798, 2, x_783);
lean_ctor_set(x_798, 3, x_747);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 6, x_794);
lean_ctor_set_uint32(x_798, sizeof(void*)*4, x_795);
lean_ctor_set_uint16(x_798, sizeof(void*)*4 + 4, x_796);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 7, x_797);
x_799 = 0;
x_800 = 0;
x_801 = 0;
x_802 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_802, 0, x_655);
lean_ctor_set(x_802, 1, x_656);
lean_ctor_set(x_802, 2, x_657);
lean_ctor_set(x_802, 3, x_798);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_802, sizeof(void*)*4, x_799);
lean_ctor_set_uint16(x_802, sizeof(void*)*4 + 4, x_800);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 7, x_801);
return x_802;
}
}
}
}
}
}
}
else
{
uint8_t x_803; 
x_803 = l_RBNode_isRed___rarg(x_655);
if (x_803 == 0)
{
lean_object* x_804; uint32_t x_805; uint16_t x_806; uint8_t x_807; lean_object* x_808; 
x_804 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_655, x_2, x_3);
x_805 = 0;
x_806 = 0;
x_807 = 0;
x_808 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_808, 0, x_804);
lean_ctor_set(x_808, 1, x_656);
lean_ctor_set(x_808, 2, x_657);
lean_ctor_set(x_808, 3, x_658);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_808, sizeof(void*)*4, x_805);
lean_ctor_set_uint16(x_808, sizeof(void*)*4 + 4, x_806);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 7, x_807);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_655, x_2, x_3);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_809, 3);
lean_inc(x_811);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; uint32_t x_816; uint16_t x_817; uint8_t x_818; lean_object* x_819; uint8_t x_820; uint32_t x_821; uint16_t x_822; uint8_t x_823; lean_object* x_824; 
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
x_813 = lean_ctor_get(x_809, 2);
lean_inc(x_813);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_814 = x_809;
} else {
 lean_dec_ref(x_809);
 x_814 = lean_box(0);
}
x_815 = 0;
x_816 = 0;
x_817 = 0;
x_818 = 0;
if (lean_is_scalar(x_814)) {
 x_819 = lean_alloc_ctor(1, 4, 8);
} else {
 x_819 = x_814;
}
lean_ctor_set(x_819, 0, x_811);
lean_ctor_set(x_819, 1, x_812);
lean_ctor_set(x_819, 2, x_813);
lean_ctor_set(x_819, 3, x_811);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 6, x_815);
lean_ctor_set_uint32(x_819, sizeof(void*)*4, x_816);
lean_ctor_set_uint16(x_819, sizeof(void*)*4 + 4, x_817);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 7, x_818);
x_820 = 1;
x_821 = 0;
x_822 = 0;
x_823 = 0;
x_824 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_824, 0, x_819);
lean_ctor_set(x_824, 1, x_656);
lean_ctor_set(x_824, 2, x_657);
lean_ctor_set(x_824, 3, x_658);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 6, x_820);
lean_ctor_set_uint32(x_824, sizeof(void*)*4, x_821);
lean_ctor_set_uint16(x_824, sizeof(void*)*4 + 4, x_822);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 7, x_823);
return x_824;
}
else
{
uint8_t x_825; 
x_825 = lean_ctor_get_uint8(x_811, sizeof(void*)*4 + 6);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; uint32_t x_835; uint16_t x_836; uint8_t x_837; lean_object* x_838; uint32_t x_839; uint16_t x_840; uint8_t x_841; lean_object* x_842; uint32_t x_843; uint16_t x_844; uint8_t x_845; lean_object* x_846; 
x_826 = lean_ctor_get(x_809, 1);
lean_inc(x_826);
x_827 = lean_ctor_get(x_809, 2);
lean_inc(x_827);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_828 = x_809;
} else {
 lean_dec_ref(x_809);
 x_828 = lean_box(0);
}
x_829 = lean_ctor_get(x_811, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_811, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_811, 2);
lean_inc(x_831);
x_832 = lean_ctor_get(x_811, 3);
lean_inc(x_832);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 lean_ctor_release(x_811, 2);
 lean_ctor_release(x_811, 3);
 x_833 = x_811;
} else {
 lean_dec_ref(x_811);
 x_833 = lean_box(0);
}
x_834 = 1;
x_835 = 0;
x_836 = 0;
x_837 = 0;
if (lean_is_scalar(x_833)) {
 x_838 = lean_alloc_ctor(1, 4, 8);
} else {
 x_838 = x_833;
}
lean_ctor_set(x_838, 0, x_810);
lean_ctor_set(x_838, 1, x_826);
lean_ctor_set(x_838, 2, x_827);
lean_ctor_set(x_838, 3, x_829);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_838, sizeof(void*)*4, x_835);
lean_ctor_set_uint16(x_838, sizeof(void*)*4 + 4, x_836);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 7, x_837);
x_839 = 0;
x_840 = 0;
x_841 = 0;
if (lean_is_scalar(x_828)) {
 x_842 = lean_alloc_ctor(1, 4, 8);
} else {
 x_842 = x_828;
}
lean_ctor_set(x_842, 0, x_832);
lean_ctor_set(x_842, 1, x_656);
lean_ctor_set(x_842, 2, x_657);
lean_ctor_set(x_842, 3, x_658);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_842, sizeof(void*)*4, x_839);
lean_ctor_set_uint16(x_842, sizeof(void*)*4 + 4, x_840);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 7, x_841);
x_843 = 0;
x_844 = 0;
x_845 = 0;
x_846 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_846, 0, x_838);
lean_ctor_set(x_846, 1, x_830);
lean_ctor_set(x_846, 2, x_831);
lean_ctor_set(x_846, 3, x_842);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_846, sizeof(void*)*4, x_843);
lean_ctor_set_uint16(x_846, sizeof(void*)*4 + 4, x_844);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 7, x_845);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; uint32_t x_851; uint16_t x_852; uint8_t x_853; lean_object* x_854; uint32_t x_855; uint16_t x_856; uint8_t x_857; lean_object* x_858; 
x_847 = lean_ctor_get(x_809, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_809, 2);
lean_inc(x_848);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_849 = x_809;
} else {
 lean_dec_ref(x_809);
 x_849 = lean_box(0);
}
x_850 = 0;
x_851 = 0;
x_852 = 0;
x_853 = 0;
if (lean_is_scalar(x_849)) {
 x_854 = lean_alloc_ctor(1, 4, 8);
} else {
 x_854 = x_849;
}
lean_ctor_set(x_854, 0, x_810);
lean_ctor_set(x_854, 1, x_847);
lean_ctor_set(x_854, 2, x_848);
lean_ctor_set(x_854, 3, x_811);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 6, x_850);
lean_ctor_set_uint32(x_854, sizeof(void*)*4, x_851);
lean_ctor_set_uint16(x_854, sizeof(void*)*4 + 4, x_852);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 7, x_853);
x_855 = 0;
x_856 = 0;
x_857 = 0;
x_858 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_858, 0, x_854);
lean_ctor_set(x_858, 1, x_656);
lean_ctor_set(x_858, 2, x_657);
lean_ctor_set(x_858, 3, x_658);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_858, sizeof(void*)*4, x_855);
lean_ctor_set_uint16(x_858, sizeof(void*)*4 + 4, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 7, x_857);
return x_858;
}
}
}
else
{
uint8_t x_859; 
x_859 = lean_ctor_get_uint8(x_810, sizeof(void*)*4 + 6);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; uint32_t x_870; uint16_t x_871; uint8_t x_872; lean_object* x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_860 = lean_ctor_get(x_809, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_809, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_809, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_863 = x_809;
} else {
 lean_dec_ref(x_809);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_810, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_810, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_810, 2);
lean_inc(x_866);
x_867 = lean_ctor_get(x_810, 3);
lean_inc(x_867);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_868 = x_810;
} else {
 lean_dec_ref(x_810);
 x_868 = lean_box(0);
}
x_869 = 1;
x_870 = 0;
x_871 = 0;
x_872 = 0;
if (lean_is_scalar(x_868)) {
 x_873 = lean_alloc_ctor(1, 4, 8);
} else {
 x_873 = x_868;
}
lean_ctor_set(x_873, 0, x_864);
lean_ctor_set(x_873, 1, x_865);
lean_ctor_set(x_873, 2, x_866);
lean_ctor_set(x_873, 3, x_867);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_873, sizeof(void*)*4, x_870);
lean_ctor_set_uint16(x_873, sizeof(void*)*4 + 4, x_871);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 7, x_872);
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_863)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_863;
}
lean_ctor_set(x_877, 0, x_862);
lean_ctor_set(x_877, 1, x_656);
lean_ctor_set(x_877, 2, x_657);
lean_ctor_set(x_877, 3, x_658);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_860);
lean_ctor_set(x_881, 2, x_861);
lean_ctor_set(x_881, 3, x_877);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
lean_object* x_882; 
x_882 = lean_ctor_get(x_809, 3);
lean_inc(x_882);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; uint32_t x_887; uint16_t x_888; uint8_t x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; 
x_883 = lean_ctor_get(x_809, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_809, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_885 = x_809;
} else {
 lean_dec_ref(x_809);
 x_885 = lean_box(0);
}
x_886 = 0;
x_887 = 0;
x_888 = 0;
x_889 = 0;
if (lean_is_scalar(x_885)) {
 x_890 = lean_alloc_ctor(1, 4, 8);
} else {
 x_890 = x_885;
}
lean_ctor_set(x_890, 0, x_810);
lean_ctor_set(x_890, 1, x_883);
lean_ctor_set(x_890, 2, x_884);
lean_ctor_set(x_890, 3, x_882);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 6, x_886);
lean_ctor_set_uint32(x_890, sizeof(void*)*4, x_887);
lean_ctor_set_uint16(x_890, sizeof(void*)*4 + 4, x_888);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 7, x_889);
x_891 = 0;
x_892 = 0;
x_893 = 0;
x_894 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_656);
lean_ctor_set(x_894, 2, x_657);
lean_ctor_set(x_894, 3, x_658);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
return x_894;
}
else
{
uint8_t x_895; 
x_895 = lean_ctor_get_uint8(x_882, sizeof(void*)*4 + 6);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint32_t x_904; uint16_t x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; uint32_t x_909; uint16_t x_910; uint8_t x_911; lean_object* x_912; uint32_t x_913; uint16_t x_914; uint8_t x_915; lean_object* x_916; 
x_896 = lean_ctor_get(x_809, 1);
lean_inc(x_896);
x_897 = lean_ctor_get(x_809, 2);
lean_inc(x_897);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_898 = x_809;
} else {
 lean_dec_ref(x_809);
 x_898 = lean_box(0);
}
x_899 = lean_ctor_get(x_882, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_882, 1);
lean_inc(x_900);
x_901 = lean_ctor_get(x_882, 2);
lean_inc(x_901);
x_902 = lean_ctor_get(x_882, 3);
lean_inc(x_902);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 lean_ctor_release(x_882, 2);
 lean_ctor_release(x_882, 3);
 x_903 = x_882;
} else {
 lean_dec_ref(x_882);
 x_903 = lean_box(0);
}
x_904 = 0;
x_905 = 0;
x_906 = 0;
lean_inc(x_810);
if (lean_is_scalar(x_903)) {
 x_907 = lean_alloc_ctor(1, 4, 8);
} else {
 x_907 = x_903;
}
lean_ctor_set(x_907, 0, x_810);
lean_ctor_set(x_907, 1, x_896);
lean_ctor_set(x_907, 2, x_897);
lean_ctor_set(x_907, 3, x_899);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_908 = x_810;
} else {
 lean_dec_ref(x_810);
 x_908 = lean_box(0);
}
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_907, sizeof(void*)*4, x_904);
lean_ctor_set_uint16(x_907, sizeof(void*)*4 + 4, x_905);
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 7, x_906);
x_909 = 0;
x_910 = 0;
x_911 = 0;
if (lean_is_scalar(x_908)) {
 x_912 = lean_alloc_ctor(1, 4, 8);
} else {
 x_912 = x_908;
}
lean_ctor_set(x_912, 0, x_902);
lean_ctor_set(x_912, 1, x_656);
lean_ctor_set(x_912, 2, x_657);
lean_ctor_set(x_912, 3, x_658);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_912, sizeof(void*)*4, x_909);
lean_ctor_set_uint16(x_912, sizeof(void*)*4 + 4, x_910);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 7, x_911);
x_913 = 0;
x_914 = 0;
x_915 = 0;
if (lean_is_scalar(x_898)) {
 x_916 = lean_alloc_ctor(1, 4, 8);
} else {
 x_916 = x_898;
}
lean_ctor_set(x_916, 0, x_907);
lean_ctor_set(x_916, 1, x_900);
lean_ctor_set(x_916, 2, x_901);
lean_ctor_set(x_916, 3, x_912);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_916, sizeof(void*)*4, x_913);
lean_ctor_set_uint16(x_916, sizeof(void*)*4 + 4, x_914);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 7, x_915);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint32_t x_925; uint16_t x_926; uint8_t x_927; lean_object* x_928; uint8_t x_929; uint32_t x_930; uint16_t x_931; uint8_t x_932; lean_object* x_933; uint32_t x_934; uint16_t x_935; uint8_t x_936; lean_object* x_937; 
x_917 = lean_ctor_get(x_809, 1);
lean_inc(x_917);
x_918 = lean_ctor_get(x_809, 2);
lean_inc(x_918);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_919 = x_809;
} else {
 lean_dec_ref(x_809);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_810, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_810, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_810, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_810, 3);
lean_inc(x_923);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_924 = x_810;
} else {
 lean_dec_ref(x_810);
 x_924 = lean_box(0);
}
x_925 = 0;
x_926 = 0;
x_927 = 0;
if (lean_is_scalar(x_924)) {
 x_928 = lean_alloc_ctor(1, 4, 8);
} else {
 x_928 = x_924;
}
lean_ctor_set(x_928, 0, x_920);
lean_ctor_set(x_928, 1, x_921);
lean_ctor_set(x_928, 2, x_922);
lean_ctor_set(x_928, 3, x_923);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_928, sizeof(void*)*4, x_925);
lean_ctor_set_uint16(x_928, sizeof(void*)*4 + 4, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 7, x_927);
x_929 = 0;
x_930 = 0;
x_931 = 0;
x_932 = 0;
if (lean_is_scalar(x_919)) {
 x_933 = lean_alloc_ctor(1, 4, 8);
} else {
 x_933 = x_919;
}
lean_ctor_set(x_933, 0, x_928);
lean_ctor_set(x_933, 1, x_917);
lean_ctor_set(x_933, 2, x_918);
lean_ctor_set(x_933, 3, x_882);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 6, x_929);
lean_ctor_set_uint32(x_933, sizeof(void*)*4, x_930);
lean_ctor_set_uint16(x_933, sizeof(void*)*4 + 4, x_931);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 7, x_932);
x_934 = 0;
x_935 = 0;
x_936 = 0;
x_937 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_937, 0, x_933);
lean_ctor_set(x_937, 1, x_656);
lean_ctor_set(x_937, 2, x_657);
lean_ctor_set(x_937, 3, x_658);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_937, sizeof(void*)*4, x_934);
lean_ctor_set_uint16(x_937, sizeof(void*)*4 + 4, x_935);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 7, x_936);
return x_937;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_box_uint32(x_2);
x_9 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_9, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 7, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_unbox_uint32(x_13);
x_17 = x_2 < x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = lean_unbox_uint32(x_13);
x_19 = x_18 < x_2;
if (x_19 == 0)
{
uint32_t x_20; uint16_t x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = 0;
x_21 = 0;
x_22 = 0;
x_23 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_20);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_22);
return x_1;
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_15, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 3, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; 
x_28 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_12, x_2, x_3);
x_29 = 0;
x_30 = 0;
x_31 = 0;
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_29);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_36 = lean_unbox_uint32(x_33);
x_37 = x_2 < x_36;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = lean_unbox_uint32(x_33);
x_39 = x_38 < x_2;
if (x_39 == 0)
{
uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_33);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_box_uint32(x_2);
x_44 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_44, sizeof(void*)*4, x_40);
lean_ctor_set_uint16(x_44, sizeof(void*)*4 + 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 7, x_42);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint16_t x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_35, x_2, x_3);
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_49, sizeof(void*)*4, x_46);
lean_ctor_set_uint16(x_49, sizeof(void*)*4 + 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 7, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint32_t x_51; uint16_t x_52; uint8_t x_53; lean_object* x_54; 
x_50 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_32, x_2, x_3);
x_51 = 0;
x_52 = 0;
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_34);
lean_ctor_set(x_54, 3, x_35);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_54, sizeof(void*)*4, x_51);
lean_ctor_set_uint16(x_54, sizeof(void*)*4 + 4, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 7, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
x_60 = lean_unbox_uint32(x_57);
x_61 = x_2 < x_60;
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = lean_unbox_uint32(x_57);
x_63 = x_62 < x_2;
if (x_63 == 0)
{
uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_64);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_66);
return x_1;
}
else
{
uint8_t x_68; 
x_68 = l_RBNode_isRed___rarg(x_59);
if (x_68 == 0)
{
lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; 
x_69 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_59, x_2, x_3);
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_1, 3, x_69);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_72);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_59, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; uint8_t x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; 
x_77 = lean_ctor_get(x_73, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
lean_ctor_set(x_73, 0, x_75);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_82);
x_83 = 1;
x_84 = 0;
x_85 = 0;
x_86 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_83);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_84);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_86);
return x_1;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint32_t x_90; uint16_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint32_t x_95; uint16_t x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_73, 1);
x_88 = lean_ctor_get(x_73, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = 0;
x_90 = 0;
x_91 = 0;
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_75);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 6, x_89);
lean_ctor_set_uint32(x_93, sizeof(void*)*4, x_90);
lean_ctor_set_uint16(x_93, sizeof(void*)*4 + 4, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 7, x_92);
x_94 = 1;
x_95 = 0;
x_96 = 0;
x_97 = 0;
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_94);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_95);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_97);
return x_1;
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_75, sizeof(void*)*4 + 6);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_73);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_73, 1);
x_101 = lean_ctor_get(x_73, 2);
x_102 = lean_ctor_get(x_73, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_73, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_75);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint32_t x_110; uint16_t x_111; uint8_t x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; uint32_t x_116; uint16_t x_117; uint8_t x_118; 
x_105 = lean_ctor_get(x_75, 0);
x_106 = lean_ctor_get(x_75, 1);
x_107 = lean_ctor_get(x_75, 2);
x_108 = lean_ctor_get(x_75, 3);
x_109 = 1;
x_110 = 0;
x_111 = 0;
x_112 = 0;
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_75, sizeof(void*)*4, x_110);
lean_ctor_set_uint16(x_75, sizeof(void*)*4 + 4, x_111);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 7, x_112);
x_113 = 0;
x_114 = 0;
x_115 = 0;
lean_ctor_set(x_73, 3, x_108);
lean_ctor_set(x_73, 2, x_107);
lean_ctor_set(x_73, 1, x_106);
lean_ctor_set(x_73, 0, x_105);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_113);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_114);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_115);
x_116 = 0;
x_117 = 0;
x_118 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_116);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_118);
return x_1;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; uint32_t x_128; uint16_t x_129; uint8_t x_130; uint32_t x_131; uint16_t x_132; uint8_t x_133; 
x_119 = lean_ctor_get(x_75, 0);
x_120 = lean_ctor_get(x_75, 1);
x_121 = lean_ctor_get(x_75, 2);
x_122 = lean_ctor_get(x_75, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_75);
x_123 = 1;
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_127, 0, x_56);
lean_ctor_set(x_127, 1, x_57);
lean_ctor_set(x_127, 2, x_58);
lean_ctor_set(x_127, 3, x_74);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_127, sizeof(void*)*4, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*4 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 7, x_126);
x_128 = 0;
x_129 = 0;
x_130 = 0;
lean_ctor_set(x_73, 3, x_122);
lean_ctor_set(x_73, 2, x_121);
lean_ctor_set(x_73, 1, x_120);
lean_ctor_set(x_73, 0, x_119);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_128);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_129);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_130);
x_131 = 0;
x_132 = 0;
x_133 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_131);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_133);
return x_1;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint32_t x_142; uint16_t x_143; uint8_t x_144; lean_object* x_145; uint32_t x_146; uint16_t x_147; uint8_t x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_73, 1);
x_135 = lean_ctor_get(x_73, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_73);
x_136 = lean_ctor_get(x_75, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_75, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_75, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_75, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_140 = x_75;
} else {
 lean_dec_ref(x_75);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = 0;
x_143 = 0;
x_144 = 0;
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(1, 4, 8);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_56);
lean_ctor_set(x_145, 1, x_57);
lean_ctor_set(x_145, 2, x_58);
lean_ctor_set(x_145, 3, x_74);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_145, sizeof(void*)*4, x_142);
lean_ctor_set_uint16(x_145, sizeof(void*)*4 + 4, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 7, x_144);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_149, sizeof(void*)*4, x_146);
lean_ctor_set_uint16(x_149, sizeof(void*)*4 + 4, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 7, x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_149);
lean_ctor_set(x_1, 2, x_135);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_145);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_73);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint32_t x_157; uint16_t x_158; uint8_t x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_73, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_73, 0);
lean_dec(x_155);
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_156);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_157);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_158);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_159);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; uint32_t x_170; uint16_t x_171; uint8_t x_172; 
x_163 = lean_ctor_get(x_73, 1);
x_164 = lean_ctor_get(x_73, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_73);
x_165 = 0;
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_169, 0, x_74);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 3, x_75);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 6, x_165);
lean_ctor_set_uint32(x_169, sizeof(void*)*4, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*4 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 7, x_168);
x_170 = 0;
x_171 = 0;
x_172 = 0;
lean_ctor_set(x_1, 3, x_169);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_170);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_171);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_172);
return x_1;
}
}
}
}
else
{
uint8_t x_173; 
x_173 = lean_ctor_get_uint8(x_74, sizeof(void*)*4 + 6);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_73);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_73, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_74);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint32_t x_182; uint16_t x_183; uint8_t x_184; uint32_t x_185; uint16_t x_186; uint8_t x_187; uint32_t x_188; uint16_t x_189; uint8_t x_190; 
x_177 = lean_ctor_get(x_74, 0);
x_178 = lean_ctor_get(x_74, 1);
x_179 = lean_ctor_get(x_74, 2);
x_180 = lean_ctor_get(x_74, 3);
x_181 = 1;
x_182 = 0;
x_183 = 0;
x_184 = 0;
lean_ctor_set(x_74, 3, x_177);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_182);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_183);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_184);
x_185 = 0;
x_186 = 0;
x_187 = 0;
lean_ctor_set(x_73, 0, x_180);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_185);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_186);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_187);
x_188 = 0;
x_189 = 0;
x_190 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_179);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_188);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_190);
return x_1;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint32_t x_196; uint16_t x_197; uint8_t x_198; lean_object* x_199; uint32_t x_200; uint16_t x_201; uint8_t x_202; uint32_t x_203; uint16_t x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_74, 0);
x_192 = lean_ctor_get(x_74, 1);
x_193 = lean_ctor_get(x_74, 2);
x_194 = lean_ctor_get(x_74, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_74);
x_195 = 1;
x_196 = 0;
x_197 = 0;
x_198 = 0;
x_199 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_199, 0, x_56);
lean_ctor_set(x_199, 1, x_57);
lean_ctor_set(x_199, 2, x_58);
lean_ctor_set(x_199, 3, x_191);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_199, sizeof(void*)*4, x_196);
lean_ctor_set_uint16(x_199, sizeof(void*)*4 + 4, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 7, x_198);
x_200 = 0;
x_201 = 0;
x_202 = 0;
lean_ctor_set(x_73, 0, x_194);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_200);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_201);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_202);
x_203 = 0;
x_204 = 0;
x_205 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_193);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_203);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_205);
return x_1;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint32_t x_215; uint16_t x_216; uint8_t x_217; lean_object* x_218; uint32_t x_219; uint16_t x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; 
x_206 = lean_ctor_get(x_73, 1);
x_207 = lean_ctor_get(x_73, 2);
x_208 = lean_ctor_get(x_73, 3);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_73);
x_209 = lean_ctor_get(x_74, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_74, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_74, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_74, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_213 = x_74;
} else {
 lean_dec_ref(x_74);
 x_213 = lean_box(0);
}
x_214 = 1;
x_215 = 0;
x_216 = 0;
x_217 = 0;
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(1, 4, 8);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_56);
lean_ctor_set(x_218, 1, x_57);
lean_ctor_set(x_218, 2, x_58);
lean_ctor_set(x_218, 3, x_209);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_218, sizeof(void*)*4, x_215);
lean_ctor_set_uint16(x_218, sizeof(void*)*4 + 4, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 7, x_217);
x_219 = 0;
x_220 = 0;
x_221 = 0;
x_222 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_206);
lean_ctor_set(x_222, 2, x_207);
lean_ctor_set(x_222, 3, x_208);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_222, sizeof(void*)*4, x_219);
lean_ctor_set_uint16(x_222, sizeof(void*)*4 + 4, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 7, x_221);
x_223 = 0;
x_224 = 0;
x_225 = 0;
lean_ctor_set(x_1, 3, x_222);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_218);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_223);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_225);
return x_1;
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_73, 3);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_73);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint32_t x_231; uint16_t x_232; uint8_t x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_228 = lean_ctor_get(x_73, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_73, 0);
lean_dec(x_229);
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_230);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_231);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_232);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_233);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; uint32_t x_244; uint16_t x_245; uint8_t x_246; 
x_237 = lean_ctor_get(x_73, 1);
x_238 = lean_ctor_get(x_73, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_73);
x_239 = 0;
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_243, 0, x_74);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_226);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 6, x_239);
lean_ctor_set_uint32(x_243, sizeof(void*)*4, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*4 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 7, x_242);
x_244 = 0;
x_245 = 0;
x_246 = 0;
lean_ctor_set(x_1, 3, x_243);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_244);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_246);
return x_1;
}
}
else
{
uint8_t x_247; 
x_247 = lean_ctor_get_uint8(x_226, sizeof(void*)*4 + 6);
if (x_247 == 0)
{
uint8_t x_248; 
lean_free_object(x_1);
x_248 = !lean_is_exclusive(x_73);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_73, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_73, 0);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_226);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint32_t x_256; uint16_t x_257; uint8_t x_258; uint8_t x_259; 
x_252 = lean_ctor_get(x_226, 0);
x_253 = lean_ctor_get(x_226, 1);
x_254 = lean_ctor_get(x_226, 2);
x_255 = lean_ctor_get(x_226, 3);
x_256 = 0;
x_257 = 0;
x_258 = 0;
lean_inc(x_74);
lean_ctor_set(x_226, 3, x_74);
lean_ctor_set(x_226, 2, x_58);
lean_ctor_set(x_226, 1, x_57);
lean_ctor_set(x_226, 0, x_56);
x_259 = !lean_is_exclusive(x_74);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; 
x_260 = lean_ctor_get(x_74, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_74, 2);
lean_dec(x_261);
x_262 = lean_ctor_get(x_74, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_74, 3, x_255);
lean_ctor_set(x_74, 2, x_254);
lean_ctor_set(x_74, 1, x_253);
lean_ctor_set(x_74, 0, x_252);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_266);
x_267 = 0;
x_268 = 0;
x_269 = 0;
lean_ctor_set(x_73, 3, x_74);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_267);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_268);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_269);
return x_73;
}
else
{
uint32_t x_270; uint16_t x_271; uint8_t x_272; lean_object* x_273; uint32_t x_274; uint16_t x_275; uint8_t x_276; 
lean_dec(x_74);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_270 = 0;
x_271 = 0;
x_272 = 0;
x_273 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_273, 0, x_252);
lean_ctor_set(x_273, 1, x_253);
lean_ctor_set(x_273, 2, x_254);
lean_ctor_set(x_273, 3, x_255);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_273, sizeof(void*)*4, x_270);
lean_ctor_set_uint16(x_273, sizeof(void*)*4 + 4, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 7, x_272);
x_274 = 0;
x_275 = 0;
x_276 = 0;
lean_ctor_set(x_73, 3, x_273);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_274);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_275);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_276);
return x_73;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint32_t x_281; uint16_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint32_t x_286; uint16_t x_287; uint8_t x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; 
x_277 = lean_ctor_get(x_226, 0);
x_278 = lean_ctor_get(x_226, 1);
x_279 = lean_ctor_get(x_226, 2);
x_280 = lean_ctor_get(x_226, 3);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_226);
x_281 = 0;
x_282 = 0;
x_283 = 0;
lean_inc(x_74);
x_284 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_284, 0, x_56);
lean_ctor_set(x_284, 1, x_57);
lean_ctor_set(x_284, 2, x_58);
lean_ctor_set(x_284, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_285 = x_74;
} else {
 lean_dec_ref(x_74);
 x_285 = lean_box(0);
}
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_284, sizeof(void*)*4, x_281);
lean_ctor_set_uint16(x_284, sizeof(void*)*4 + 4, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 7, x_283);
x_286 = 0;
x_287 = 0;
x_288 = 0;
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(1, 4, 8);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_278);
lean_ctor_set(x_289, 2, x_279);
lean_ctor_set(x_289, 3, x_280);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_289, sizeof(void*)*4, x_286);
lean_ctor_set_uint16(x_289, sizeof(void*)*4 + 4, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 7, x_288);
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_ctor_set(x_73, 3, x_289);
lean_ctor_set(x_73, 0, x_284);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_292);
return x_73;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint32_t x_300; uint16_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint32_t x_305; uint16_t x_306; uint8_t x_307; lean_object* x_308; uint32_t x_309; uint16_t x_310; uint8_t x_311; lean_object* x_312; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_73);
x_295 = lean_ctor_get(x_226, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_226, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_226, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_226, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 x_299 = x_226;
} else {
 lean_dec_ref(x_226);
 x_299 = lean_box(0);
}
x_300 = 0;
x_301 = 0;
x_302 = 0;
lean_inc(x_74);
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(1, 4, 8);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_56);
lean_ctor_set(x_303, 1, x_57);
lean_ctor_set(x_303, 2, x_58);
lean_ctor_set(x_303, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_304 = x_74;
} else {
 lean_dec_ref(x_74);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_303, sizeof(void*)*4, x_300);
lean_ctor_set_uint16(x_303, sizeof(void*)*4 + 4, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 7, x_302);
x_305 = 0;
x_306 = 0;
x_307 = 0;
if (lean_is_scalar(x_304)) {
 x_308 = lean_alloc_ctor(1, 4, 8);
} else {
 x_308 = x_304;
}
lean_ctor_set(x_308, 0, x_295);
lean_ctor_set(x_308, 1, x_296);
lean_ctor_set(x_308, 2, x_297);
lean_ctor_set(x_308, 3, x_298);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_308, sizeof(void*)*4, x_305);
lean_ctor_set_uint16(x_308, sizeof(void*)*4 + 4, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 7, x_307);
x_309 = 0;
x_310 = 0;
x_311 = 0;
x_312 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_293);
lean_ctor_set(x_312, 2, x_294);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_312, sizeof(void*)*4, x_309);
lean_ctor_set_uint16(x_312, sizeof(void*)*4 + 4, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 7, x_311);
return x_312;
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_73);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_73, 3);
lean_dec(x_314);
x_315 = lean_ctor_get(x_73, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_74);
if (x_316 == 0)
{
uint32_t x_317; uint16_t x_318; uint8_t x_319; uint8_t x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; uint32_t x_324; uint16_t x_325; uint8_t x_326; 
x_317 = 0;
x_318 = 0;
x_319 = 0;
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_317);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_318);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_319);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_320);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_323);
x_324 = 0;
x_325 = 0;
x_326 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_324);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_326);
return x_1;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; uint32_t x_336; uint16_t x_337; uint8_t x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; 
x_327 = lean_ctor_get(x_74, 0);
x_328 = lean_ctor_get(x_74, 1);
x_329 = lean_ctor_get(x_74, 2);
x_330 = lean_ctor_get(x_74, 3);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_74);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_334, 2, x_329);
lean_ctor_set(x_334, 3, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_334, sizeof(void*)*4, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*4 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 7, x_333);
x_335 = 0;
x_336 = 0;
x_337 = 0;
x_338 = 0;
lean_ctor_set(x_73, 0, x_334);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_335);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_336);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_337);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_338);
x_339 = 0;
x_340 = 0;
x_341 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_341);
return x_1;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint32_t x_349; uint16_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; uint32_t x_354; uint16_t x_355; uint8_t x_356; lean_object* x_357; uint32_t x_358; uint16_t x_359; uint8_t x_360; 
x_342 = lean_ctor_get(x_73, 1);
x_343 = lean_ctor_get(x_73, 2);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_73);
x_344 = lean_ctor_get(x_74, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_74, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_74, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_74, 3);
lean_inc(x_347);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_348 = x_74;
} else {
 lean_dec_ref(x_74);
 x_348 = lean_box(0);
}
x_349 = 0;
x_350 = 0;
x_351 = 0;
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(1, 4, 8);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_345);
lean_ctor_set(x_352, 2, x_346);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_352, sizeof(void*)*4, x_349);
lean_ctor_set_uint16(x_352, sizeof(void*)*4 + 4, x_350);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 7, x_351);
x_353 = 0;
x_354 = 0;
x_355 = 0;
x_356 = 0;
x_357 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_342);
lean_ctor_set(x_357, 2, x_343);
lean_ctor_set(x_357, 3, x_226);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_353);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_354);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_356);
x_358 = 0;
x_359 = 0;
x_360 = 0;
lean_ctor_set(x_1, 3, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_358);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_359);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_360);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_361; 
x_361 = l_RBNode_isRed___rarg(x_56);
if (x_361 == 0)
{
lean_object* x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; 
x_362 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_56, x_2, x_3);
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_1, 0, x_362);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_365);
return x_1;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_56, x_2, x_3);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_366);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; uint8_t x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; 
x_370 = lean_ctor_get(x_366, 3);
lean_dec(x_370);
x_371 = lean_ctor_get(x_366, 0);
lean_dec(x_371);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
lean_ctor_set(x_366, 0, x_368);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_375);
x_376 = 1;
x_377 = 0;
x_378 = 0;
x_379 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_376);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_377);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_378);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_379);
return x_1;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; uint8_t x_387; uint32_t x_388; uint16_t x_389; uint8_t x_390; 
x_380 = lean_ctor_get(x_366, 1);
x_381 = lean_ctor_get(x_366, 2);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_366);
x_382 = 0;
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_386, 0, x_368);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_368);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 6, x_382);
lean_ctor_set_uint32(x_386, sizeof(void*)*4, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*4 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 7, x_385);
x_387 = 1;
x_388 = 0;
x_389 = 0;
x_390 = 0;
lean_ctor_set(x_1, 0, x_386);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_387);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_388);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_389);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_390);
return x_1;
}
}
else
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_368, sizeof(void*)*4 + 6);
if (x_391 == 0)
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_366);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_393 = lean_ctor_get(x_366, 1);
x_394 = lean_ctor_get(x_366, 2);
x_395 = lean_ctor_get(x_366, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_366, 0);
lean_dec(x_396);
x_397 = !lean_is_exclusive(x_368);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint32_t x_403; uint16_t x_404; uint8_t x_405; uint32_t x_406; uint16_t x_407; uint8_t x_408; uint32_t x_409; uint16_t x_410; uint8_t x_411; 
x_398 = lean_ctor_get(x_368, 0);
x_399 = lean_ctor_get(x_368, 1);
x_400 = lean_ctor_get(x_368, 2);
x_401 = lean_ctor_get(x_368, 3);
x_402 = 1;
x_403 = 0;
x_404 = 0;
x_405 = 0;
lean_ctor_set(x_368, 3, x_398);
lean_ctor_set(x_368, 2, x_394);
lean_ctor_set(x_368, 1, x_393);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_368, sizeof(void*)*4, x_403);
lean_ctor_set_uint16(x_368, sizeof(void*)*4 + 4, x_404);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 7, x_405);
x_406 = 0;
x_407 = 0;
x_408 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_401);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_406);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_407);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_408);
x_409 = 0;
x_410 = 0;
x_411 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_400);
lean_ctor_set(x_1, 1, x_399);
lean_ctor_set(x_1, 0, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_409);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_411);
return x_1;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; uint32_t x_417; uint16_t x_418; uint8_t x_419; lean_object* x_420; uint32_t x_421; uint16_t x_422; uint8_t x_423; uint32_t x_424; uint16_t x_425; uint8_t x_426; 
x_412 = lean_ctor_get(x_368, 0);
x_413 = lean_ctor_get(x_368, 1);
x_414 = lean_ctor_get(x_368, 2);
x_415 = lean_ctor_get(x_368, 3);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_368);
x_416 = 1;
x_417 = 0;
x_418 = 0;
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_420, 0, x_367);
lean_ctor_set(x_420, 1, x_393);
lean_ctor_set(x_420, 2, x_394);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_420, sizeof(void*)*4, x_417);
lean_ctor_set_uint16(x_420, sizeof(void*)*4 + 4, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 7, x_419);
x_421 = 0;
x_422 = 0;
x_423 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_415);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_421);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_422);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_423);
x_424 = 0;
x_425 = 0;
x_426 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_414);
lean_ctor_set(x_1, 1, x_413);
lean_ctor_set(x_1, 0, x_420);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_424);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_425);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_426);
return x_1;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_427 = lean_ctor_get(x_366, 1);
x_428 = lean_ctor_get(x_366, 2);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_366);
x_429 = lean_ctor_get(x_368, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_368, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_368, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_368, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_433 = x_368;
} else {
 lean_dec_ref(x_368);
 x_433 = lean_box(0);
}
x_434 = 1;
x_435 = 0;
x_436 = 0;
x_437 = 0;
if (lean_is_scalar(x_433)) {
 x_438 = lean_alloc_ctor(1, 4, 8);
} else {
 x_438 = x_433;
}
lean_ctor_set(x_438, 0, x_367);
lean_ctor_set(x_438, 1, x_427);
lean_ctor_set(x_438, 2, x_428);
lean_ctor_set(x_438, 3, x_429);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_438, sizeof(void*)*4, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*4 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_442, 0, x_432);
lean_ctor_set(x_442, 1, x_57);
lean_ctor_set(x_442, 2, x_58);
lean_ctor_set(x_442, 3, x_59);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_442, sizeof(void*)*4, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*4 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 7, x_441);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 3, x_442);
lean_ctor_set(x_1, 2, x_431);
lean_ctor_set(x_1, 1, x_430);
lean_ctor_set(x_1, 0, x_438);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
}
else
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_366);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint32_t x_450; uint16_t x_451; uint8_t x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_447 = lean_ctor_get(x_366, 3);
lean_dec(x_447);
x_448 = lean_ctor_get(x_366, 0);
lean_dec(x_448);
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_449);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_450);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_451);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_452);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; 
x_456 = lean_ctor_get(x_366, 1);
x_457 = lean_ctor_get(x_366, 2);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_366);
x_458 = 0;
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_462, 0, x_367);
lean_ctor_set(x_462, 1, x_456);
lean_ctor_set(x_462, 2, x_457);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 6, x_458);
lean_ctor_set_uint32(x_462, sizeof(void*)*4, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*4 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
lean_ctor_set(x_1, 0, x_462);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_463);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_464);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_465);
return x_1;
}
}
}
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_367, sizeof(void*)*4 + 6);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_366);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_468 = lean_ctor_get(x_366, 1);
x_469 = lean_ctor_get(x_366, 2);
x_470 = lean_ctor_get(x_366, 3);
x_471 = lean_ctor_get(x_366, 0);
lean_dec(x_471);
x_472 = !lean_is_exclusive(x_367);
if (x_472 == 0)
{
uint8_t x_473; uint32_t x_474; uint16_t x_475; uint8_t x_476; uint32_t x_477; uint16_t x_478; uint8_t x_479; uint32_t x_480; uint16_t x_481; uint8_t x_482; 
x_473 = 1;
x_474 = 0;
x_475 = 0;
x_476 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_474);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_475);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_476);
x_477 = 0;
x_478 = 0;
x_479 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_477);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_478);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_479);
x_480 = 0;
x_481 = 0;
x_482 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_367);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_480);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_482);
return x_1;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; uint32_t x_488; uint16_t x_489; uint8_t x_490; lean_object* x_491; uint32_t x_492; uint16_t x_493; uint8_t x_494; uint32_t x_495; uint16_t x_496; uint8_t x_497; 
x_483 = lean_ctor_get(x_367, 0);
x_484 = lean_ctor_get(x_367, 1);
x_485 = lean_ctor_get(x_367, 2);
x_486 = lean_ctor_get(x_367, 3);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_367);
x_487 = 1;
x_488 = 0;
x_489 = 0;
x_490 = 0;
x_491 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_491, 0, x_483);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_485);
lean_ctor_set(x_491, 3, x_486);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_491, sizeof(void*)*4, x_488);
lean_ctor_set_uint16(x_491, sizeof(void*)*4 + 4, x_489);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 7, x_490);
x_492 = 0;
x_493 = 0;
x_494 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_492);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_493);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_494);
x_495 = 0;
x_496 = 0;
x_497 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_491);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_495);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_496);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_497);
return x_1;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint32_t x_507; uint16_t x_508; uint8_t x_509; lean_object* x_510; uint32_t x_511; uint16_t x_512; uint8_t x_513; lean_object* x_514; uint32_t x_515; uint16_t x_516; uint8_t x_517; 
x_498 = lean_ctor_get(x_366, 1);
x_499 = lean_ctor_get(x_366, 2);
x_500 = lean_ctor_get(x_366, 3);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_366);
x_501 = lean_ctor_get(x_367, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_367, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_367, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_367, 3);
lean_inc(x_504);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_505 = x_367;
} else {
 lean_dec_ref(x_367);
 x_505 = lean_box(0);
}
x_506 = 1;
x_507 = 0;
x_508 = 0;
x_509 = 0;
if (lean_is_scalar(x_505)) {
 x_510 = lean_alloc_ctor(1, 4, 8);
} else {
 x_510 = x_505;
}
lean_ctor_set(x_510, 0, x_501);
lean_ctor_set(x_510, 1, x_502);
lean_ctor_set(x_510, 2, x_503);
lean_ctor_set(x_510, 3, x_504);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_510, sizeof(void*)*4, x_507);
lean_ctor_set_uint16(x_510, sizeof(void*)*4 + 4, x_508);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 7, x_509);
x_511 = 0;
x_512 = 0;
x_513 = 0;
x_514 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_57);
lean_ctor_set(x_514, 2, x_58);
lean_ctor_set(x_514, 3, x_59);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_514, sizeof(void*)*4, x_511);
lean_ctor_set_uint16(x_514, sizeof(void*)*4 + 4, x_512);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 7, x_513);
x_515 = 0;
x_516 = 0;
x_517 = 0;
lean_ctor_set(x_1, 3, x_514);
lean_ctor_set(x_1, 2, x_499);
lean_ctor_set(x_1, 1, x_498);
lean_ctor_set(x_1, 0, x_510);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_515);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_516);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_517);
return x_1;
}
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_366, 3);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
uint8_t x_519; 
x_519 = !lean_is_exclusive(x_366);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint32_t x_523; uint16_t x_524; uint8_t x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_520 = lean_ctor_get(x_366, 3);
lean_dec(x_520);
x_521 = lean_ctor_get(x_366, 0);
lean_dec(x_521);
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_522);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_523);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_524);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_525);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; uint32_t x_536; uint16_t x_537; uint8_t x_538; 
x_529 = lean_ctor_get(x_366, 1);
x_530 = lean_ctor_get(x_366, 2);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_366);
x_531 = 0;
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_535, 0, x_367);
lean_ctor_set(x_535, 1, x_529);
lean_ctor_set(x_535, 2, x_530);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 6, x_531);
lean_ctor_set_uint32(x_535, sizeof(void*)*4, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*4 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 7, x_534);
x_536 = 0;
x_537 = 0;
x_538 = 0;
lean_ctor_set(x_1, 0, x_535);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_536);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_537);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_538);
return x_1;
}
}
else
{
uint8_t x_539; 
x_539 = lean_ctor_get_uint8(x_518, sizeof(void*)*4 + 6);
if (x_539 == 0)
{
uint8_t x_540; 
lean_free_object(x_1);
x_540 = !lean_is_exclusive(x_366);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_541 = lean_ctor_get(x_366, 1);
x_542 = lean_ctor_get(x_366, 2);
x_543 = lean_ctor_get(x_366, 3);
lean_dec(x_543);
x_544 = lean_ctor_get(x_366, 0);
lean_dec(x_544);
x_545 = !lean_is_exclusive(x_518);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint32_t x_550; uint16_t x_551; uint8_t x_552; uint8_t x_553; 
x_546 = lean_ctor_get(x_518, 0);
x_547 = lean_ctor_get(x_518, 1);
x_548 = lean_ctor_get(x_518, 2);
x_549 = lean_ctor_get(x_518, 3);
x_550 = 0;
x_551 = 0;
x_552 = 0;
lean_inc(x_367);
lean_ctor_set(x_518, 3, x_546);
lean_ctor_set(x_518, 2, x_542);
lean_ctor_set(x_518, 1, x_541);
lean_ctor_set(x_518, 0, x_367);
x_553 = !lean_is_exclusive(x_367);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; uint32_t x_561; uint16_t x_562; uint8_t x_563; 
x_554 = lean_ctor_get(x_367, 3);
lean_dec(x_554);
x_555 = lean_ctor_get(x_367, 2);
lean_dec(x_555);
x_556 = lean_ctor_get(x_367, 1);
lean_dec(x_556);
x_557 = lean_ctor_get(x_367, 0);
lean_dec(x_557);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_367, 3, x_59);
lean_ctor_set(x_367, 2, x_58);
lean_ctor_set(x_367, 1, x_57);
lean_ctor_set(x_367, 0, x_549);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_560);
x_561 = 0;
x_562 = 0;
x_563 = 0;
lean_ctor_set(x_366, 3, x_367);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_561);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_562);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_563);
return x_366;
}
else
{
uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; uint32_t x_568; uint16_t x_569; uint8_t x_570; 
lean_dec(x_367);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_567, 0, x_549);
lean_ctor_set(x_567, 1, x_57);
lean_ctor_set(x_567, 2, x_58);
lean_ctor_set(x_567, 3, x_59);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_567, sizeof(void*)*4, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*4 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 7, x_566);
x_568 = 0;
x_569 = 0;
x_570 = 0;
lean_ctor_set(x_366, 3, x_567);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_568);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_569);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_570);
return x_366;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint32_t x_575; uint16_t x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; uint32_t x_580; uint16_t x_581; uint8_t x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; 
x_571 = lean_ctor_get(x_518, 0);
x_572 = lean_ctor_get(x_518, 1);
x_573 = lean_ctor_get(x_518, 2);
x_574 = lean_ctor_get(x_518, 3);
lean_inc(x_574);
lean_inc(x_573);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_518);
x_575 = 0;
x_576 = 0;
x_577 = 0;
lean_inc(x_367);
x_578 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_578, 0, x_367);
lean_ctor_set(x_578, 1, x_541);
lean_ctor_set(x_578, 2, x_542);
lean_ctor_set(x_578, 3, x_571);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_579 = x_367;
} else {
 lean_dec_ref(x_367);
 x_579 = lean_box(0);
}
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_578, sizeof(void*)*4, x_575);
lean_ctor_set_uint16(x_578, sizeof(void*)*4 + 4, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 7, x_577);
x_580 = 0;
x_581 = 0;
x_582 = 0;
if (lean_is_scalar(x_579)) {
 x_583 = lean_alloc_ctor(1, 4, 8);
} else {
 x_583 = x_579;
}
lean_ctor_set(x_583, 0, x_574);
lean_ctor_set(x_583, 1, x_57);
lean_ctor_set(x_583, 2, x_58);
lean_ctor_set(x_583, 3, x_59);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_583, sizeof(void*)*4, x_580);
lean_ctor_set_uint16(x_583, sizeof(void*)*4 + 4, x_581);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 7, x_582);
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_ctor_set(x_366, 3, x_583);
lean_ctor_set(x_366, 2, x_573);
lean_ctor_set(x_366, 1, x_572);
lean_ctor_set(x_366, 0, x_578);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_586);
return x_366;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint32_t x_594; uint16_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; uint32_t x_603; uint16_t x_604; uint8_t x_605; lean_object* x_606; 
x_587 = lean_ctor_get(x_366, 1);
x_588 = lean_ctor_get(x_366, 2);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_366);
x_589 = lean_ctor_get(x_518, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_518, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_518, 2);
lean_inc(x_591);
x_592 = lean_ctor_get(x_518, 3);
lean_inc(x_592);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 lean_ctor_release(x_518, 3);
 x_593 = x_518;
} else {
 lean_dec_ref(x_518);
 x_593 = lean_box(0);
}
x_594 = 0;
x_595 = 0;
x_596 = 0;
lean_inc(x_367);
if (lean_is_scalar(x_593)) {
 x_597 = lean_alloc_ctor(1, 4, 8);
} else {
 x_597 = x_593;
}
lean_ctor_set(x_597, 0, x_367);
lean_ctor_set(x_597, 1, x_587);
lean_ctor_set(x_597, 2, x_588);
lean_ctor_set(x_597, 3, x_589);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_598 = x_367;
} else {
 lean_dec_ref(x_367);
 x_598 = lean_box(0);
}
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_597, sizeof(void*)*4, x_594);
lean_ctor_set_uint16(x_597, sizeof(void*)*4 + 4, x_595);
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 7, x_596);
x_599 = 0;
x_600 = 0;
x_601 = 0;
if (lean_is_scalar(x_598)) {
 x_602 = lean_alloc_ctor(1, 4, 8);
} else {
 x_602 = x_598;
}
lean_ctor_set(x_602, 0, x_592);
lean_ctor_set(x_602, 1, x_57);
lean_ctor_set(x_602, 2, x_58);
lean_ctor_set(x_602, 3, x_59);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_602, sizeof(void*)*4, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*4 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 7, x_601);
x_603 = 0;
x_604 = 0;
x_605 = 0;
x_606 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_606, 0, x_597);
lean_ctor_set(x_606, 1, x_590);
lean_ctor_set(x_606, 2, x_591);
lean_ctor_set(x_606, 3, x_602);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_606, sizeof(void*)*4, x_603);
lean_ctor_set_uint16(x_606, sizeof(void*)*4 + 4, x_604);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 7, x_605);
return x_606;
}
}
else
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_366);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_ctor_get(x_366, 3);
lean_dec(x_608);
x_609 = lean_ctor_get(x_366, 0);
lean_dec(x_609);
x_610 = !lean_is_exclusive(x_367);
if (x_610 == 0)
{
uint32_t x_611; uint16_t x_612; uint8_t x_613; uint8_t x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; uint32_t x_618; uint16_t x_619; uint8_t x_620; 
x_611 = 0;
x_612 = 0;
x_613 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_611);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_612);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_613);
x_614 = 0;
x_615 = 0;
x_616 = 0;
x_617 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_614);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_617);
x_618 = 0;
x_619 = 0;
x_620 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_618);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_619);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_620);
return x_1;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint32_t x_625; uint16_t x_626; uint8_t x_627; lean_object* x_628; uint8_t x_629; uint32_t x_630; uint16_t x_631; uint8_t x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; 
x_621 = lean_ctor_get(x_367, 0);
x_622 = lean_ctor_get(x_367, 1);
x_623 = lean_ctor_get(x_367, 2);
x_624 = lean_ctor_get(x_367, 3);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_367);
x_625 = 0;
x_626 = 0;
x_627 = 0;
x_628 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_628, 0, x_621);
lean_ctor_set(x_628, 1, x_622);
lean_ctor_set(x_628, 2, x_623);
lean_ctor_set(x_628, 3, x_624);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_628, sizeof(void*)*4, x_625);
lean_ctor_set_uint16(x_628, sizeof(void*)*4 + 4, x_626);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 7, x_627);
x_629 = 0;
x_630 = 0;
x_631 = 0;
x_632 = 0;
lean_ctor_set(x_366, 0, x_628);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_629);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_630);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_631);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_632);
x_633 = 0;
x_634 = 0;
x_635 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_635);
return x_1;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint32_t x_643; uint16_t x_644; uint8_t x_645; lean_object* x_646; uint8_t x_647; uint32_t x_648; uint16_t x_649; uint8_t x_650; lean_object* x_651; uint32_t x_652; uint16_t x_653; uint8_t x_654; 
x_636 = lean_ctor_get(x_366, 1);
x_637 = lean_ctor_get(x_366, 2);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_366);
x_638 = lean_ctor_get(x_367, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_367, 1);
lean_inc(x_639);
x_640 = lean_ctor_get(x_367, 2);
lean_inc(x_640);
x_641 = lean_ctor_get(x_367, 3);
lean_inc(x_641);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_642 = x_367;
} else {
 lean_dec_ref(x_367);
 x_642 = lean_box(0);
}
x_643 = 0;
x_644 = 0;
x_645 = 0;
if (lean_is_scalar(x_642)) {
 x_646 = lean_alloc_ctor(1, 4, 8);
} else {
 x_646 = x_642;
}
lean_ctor_set(x_646, 0, x_638);
lean_ctor_set(x_646, 1, x_639);
lean_ctor_set(x_646, 2, x_640);
lean_ctor_set(x_646, 3, x_641);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_646, sizeof(void*)*4, x_643);
lean_ctor_set_uint16(x_646, sizeof(void*)*4 + 4, x_644);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 7, x_645);
x_647 = 0;
x_648 = 0;
x_649 = 0;
x_650 = 0;
x_651 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_651, 0, x_646);
lean_ctor_set(x_651, 1, x_636);
lean_ctor_set(x_651, 2, x_637);
lean_ctor_set(x_651, 3, x_518);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 6, x_647);
lean_ctor_set_uint32(x_651, sizeof(void*)*4, x_648);
lean_ctor_set_uint16(x_651, sizeof(void*)*4 + 4, x_649);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 7, x_650);
x_652 = 0;
x_653 = 0;
x_654 = 0;
lean_ctor_set(x_1, 0, x_651);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_652);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_653);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_654);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint32_t x_659; uint8_t x_660; 
x_655 = lean_ctor_get(x_1, 0);
x_656 = lean_ctor_get(x_1, 1);
x_657 = lean_ctor_get(x_1, 2);
x_658 = lean_ctor_get(x_1, 3);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_1);
x_659 = lean_unbox_uint32(x_656);
x_660 = x_2 < x_659;
if (x_660 == 0)
{
uint32_t x_661; uint8_t x_662; 
x_661 = lean_unbox_uint32(x_656);
x_662 = x_661 < x_2;
if (x_662 == 0)
{
uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_657);
lean_dec(x_656);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_box_uint32(x_2);
x_667 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_667, 0, x_655);
lean_ctor_set(x_667, 1, x_666);
lean_ctor_set(x_667, 2, x_3);
lean_ctor_set(x_667, 3, x_658);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_667, sizeof(void*)*4, x_663);
lean_ctor_set_uint16(x_667, sizeof(void*)*4 + 4, x_664);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 7, x_665);
return x_667;
}
else
{
uint8_t x_668; 
x_668 = l_RBNode_isRed___rarg(x_658);
if (x_668 == 0)
{
lean_object* x_669; uint32_t x_670; uint16_t x_671; uint8_t x_672; lean_object* x_673; 
x_669 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_658, x_2, x_3);
x_670 = 0;
x_671 = 0;
x_672 = 0;
x_673 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_673, 0, x_655);
lean_ctor_set(x_673, 1, x_656);
lean_ctor_set(x_673, 2, x_657);
lean_ctor_set(x_673, 3, x_669);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_673, sizeof(void*)*4, x_670);
lean_ctor_set_uint16(x_673, sizeof(void*)*4 + 4, x_671);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 7, x_672);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_658, x_2, x_3);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_674, 3);
lean_inc(x_676);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; uint32_t x_681; uint16_t x_682; uint8_t x_683; lean_object* x_684; uint8_t x_685; uint32_t x_686; uint16_t x_687; uint8_t x_688; lean_object* x_689; 
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 2);
lean_inc(x_678);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_679 = x_674;
} else {
 lean_dec_ref(x_674);
 x_679 = lean_box(0);
}
x_680 = 0;
x_681 = 0;
x_682 = 0;
x_683 = 0;
if (lean_is_scalar(x_679)) {
 x_684 = lean_alloc_ctor(1, 4, 8);
} else {
 x_684 = x_679;
}
lean_ctor_set(x_684, 0, x_676);
lean_ctor_set(x_684, 1, x_677);
lean_ctor_set(x_684, 2, x_678);
lean_ctor_set(x_684, 3, x_676);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 6, x_680);
lean_ctor_set_uint32(x_684, sizeof(void*)*4, x_681);
lean_ctor_set_uint16(x_684, sizeof(void*)*4 + 4, x_682);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 7, x_683);
x_685 = 1;
x_686 = 0;
x_687 = 0;
x_688 = 0;
x_689 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_689, 0, x_655);
lean_ctor_set(x_689, 1, x_656);
lean_ctor_set(x_689, 2, x_657);
lean_ctor_set(x_689, 3, x_684);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 6, x_685);
lean_ctor_set_uint32(x_689, sizeof(void*)*4, x_686);
lean_ctor_set_uint16(x_689, sizeof(void*)*4 + 4, x_687);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 7, x_688);
return x_689;
}
else
{
uint8_t x_690; 
x_690 = lean_ctor_get_uint8(x_676, sizeof(void*)*4 + 6);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; uint32_t x_700; uint16_t x_701; uint8_t x_702; lean_object* x_703; uint32_t x_704; uint16_t x_705; uint8_t x_706; lean_object* x_707; uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; 
x_691 = lean_ctor_get(x_674, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_674, 2);
lean_inc(x_692);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_693 = x_674;
} else {
 lean_dec_ref(x_674);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_676, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_676, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_676, 2);
lean_inc(x_696);
x_697 = lean_ctor_get(x_676, 3);
lean_inc(x_697);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 lean_ctor_release(x_676, 2);
 lean_ctor_release(x_676, 3);
 x_698 = x_676;
} else {
 lean_dec_ref(x_676);
 x_698 = lean_box(0);
}
x_699 = 1;
x_700 = 0;
x_701 = 0;
x_702 = 0;
if (lean_is_scalar(x_698)) {
 x_703 = lean_alloc_ctor(1, 4, 8);
} else {
 x_703 = x_698;
}
lean_ctor_set(x_703, 0, x_655);
lean_ctor_set(x_703, 1, x_656);
lean_ctor_set(x_703, 2, x_657);
lean_ctor_set(x_703, 3, x_675);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_703, sizeof(void*)*4, x_700);
lean_ctor_set_uint16(x_703, sizeof(void*)*4 + 4, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 7, x_702);
x_704 = 0;
x_705 = 0;
x_706 = 0;
if (lean_is_scalar(x_693)) {
 x_707 = lean_alloc_ctor(1, 4, 8);
} else {
 x_707 = x_693;
}
lean_ctor_set(x_707, 0, x_694);
lean_ctor_set(x_707, 1, x_695);
lean_ctor_set(x_707, 2, x_696);
lean_ctor_set(x_707, 3, x_697);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_707, sizeof(void*)*4, x_704);
lean_ctor_set_uint16(x_707, sizeof(void*)*4 + 4, x_705);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 7, x_706);
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_711, 0, x_703);
lean_ctor_set(x_711, 1, x_691);
lean_ctor_set(x_711, 2, x_692);
lean_ctor_set(x_711, 3, x_707);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_711, sizeof(void*)*4, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*4 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 7, x_710);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint32_t x_716; uint16_t x_717; uint8_t x_718; lean_object* x_719; uint32_t x_720; uint16_t x_721; uint8_t x_722; lean_object* x_723; 
x_712 = lean_ctor_get(x_674, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_674, 2);
lean_inc(x_713);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_714 = x_674;
} else {
 lean_dec_ref(x_674);
 x_714 = lean_box(0);
}
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = 0;
if (lean_is_scalar(x_714)) {
 x_719 = lean_alloc_ctor(1, 4, 8);
} else {
 x_719 = x_714;
}
lean_ctor_set(x_719, 0, x_675);
lean_ctor_set(x_719, 1, x_712);
lean_ctor_set(x_719, 2, x_713);
lean_ctor_set(x_719, 3, x_676);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 6, x_715);
lean_ctor_set_uint32(x_719, sizeof(void*)*4, x_716);
lean_ctor_set_uint16(x_719, sizeof(void*)*4 + 4, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 7, x_718);
x_720 = 0;
x_721 = 0;
x_722 = 0;
x_723 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_723, 0, x_655);
lean_ctor_set(x_723, 1, x_656);
lean_ctor_set(x_723, 2, x_657);
lean_ctor_set(x_723, 3, x_719);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_723, sizeof(void*)*4, x_720);
lean_ctor_set_uint16(x_723, sizeof(void*)*4 + 4, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 7, x_722);
return x_723;
}
}
}
else
{
uint8_t x_724; 
x_724 = lean_ctor_get_uint8(x_675, sizeof(void*)*4 + 6);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; uint32_t x_735; uint16_t x_736; uint8_t x_737; lean_object* x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_725 = lean_ctor_get(x_674, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_674, 2);
lean_inc(x_726);
x_727 = lean_ctor_get(x_674, 3);
lean_inc(x_727);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_728 = x_674;
} else {
 lean_dec_ref(x_674);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_675, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_675, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_675, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_675, 3);
lean_inc(x_732);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_733 = x_675;
} else {
 lean_dec_ref(x_675);
 x_733 = lean_box(0);
}
x_734 = 1;
x_735 = 0;
x_736 = 0;
x_737 = 0;
if (lean_is_scalar(x_733)) {
 x_738 = lean_alloc_ctor(1, 4, 8);
} else {
 x_738 = x_733;
}
lean_ctor_set(x_738, 0, x_655);
lean_ctor_set(x_738, 1, x_656);
lean_ctor_set(x_738, 2, x_657);
lean_ctor_set(x_738, 3, x_729);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_738, sizeof(void*)*4, x_735);
lean_ctor_set_uint16(x_738, sizeof(void*)*4 + 4, x_736);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 7, x_737);
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_728)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_728;
}
lean_ctor_set(x_742, 0, x_732);
lean_ctor_set(x_742, 1, x_725);
lean_ctor_set(x_742, 2, x_726);
lean_ctor_set(x_742, 3, x_727);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_738);
lean_ctor_set(x_746, 1, x_730);
lean_ctor_set(x_746, 2, x_731);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
lean_object* x_747; 
x_747 = lean_ctor_get(x_674, 3);
lean_inc(x_747);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; uint32_t x_752; uint16_t x_753; uint8_t x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; 
x_748 = lean_ctor_get(x_674, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_674, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_750 = x_674;
} else {
 lean_dec_ref(x_674);
 x_750 = lean_box(0);
}
x_751 = 0;
x_752 = 0;
x_753 = 0;
x_754 = 0;
if (lean_is_scalar(x_750)) {
 x_755 = lean_alloc_ctor(1, 4, 8);
} else {
 x_755 = x_750;
}
lean_ctor_set(x_755, 0, x_675);
lean_ctor_set(x_755, 1, x_748);
lean_ctor_set(x_755, 2, x_749);
lean_ctor_set(x_755, 3, x_747);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 6, x_751);
lean_ctor_set_uint32(x_755, sizeof(void*)*4, x_752);
lean_ctor_set_uint16(x_755, sizeof(void*)*4 + 4, x_753);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 7, x_754);
x_756 = 0;
x_757 = 0;
x_758 = 0;
x_759 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_759, 0, x_655);
lean_ctor_set(x_759, 1, x_656);
lean_ctor_set(x_759, 2, x_657);
lean_ctor_set(x_759, 3, x_755);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
return x_759;
}
else
{
uint8_t x_760; 
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*4 + 6);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; uint32_t x_769; uint16_t x_770; uint8_t x_771; lean_object* x_772; lean_object* x_773; uint32_t x_774; uint16_t x_775; uint8_t x_776; lean_object* x_777; uint32_t x_778; uint16_t x_779; uint8_t x_780; lean_object* x_781; 
x_761 = lean_ctor_get(x_674, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_674, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_763 = x_674;
} else {
 lean_dec_ref(x_674);
 x_763 = lean_box(0);
}
x_764 = lean_ctor_get(x_747, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_747, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_747, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_747, 3);
lean_inc(x_767);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 lean_ctor_release(x_747, 2);
 lean_ctor_release(x_747, 3);
 x_768 = x_747;
} else {
 lean_dec_ref(x_747);
 x_768 = lean_box(0);
}
x_769 = 0;
x_770 = 0;
x_771 = 0;
lean_inc(x_675);
if (lean_is_scalar(x_768)) {
 x_772 = lean_alloc_ctor(1, 4, 8);
} else {
 x_772 = x_768;
}
lean_ctor_set(x_772, 0, x_655);
lean_ctor_set(x_772, 1, x_656);
lean_ctor_set(x_772, 2, x_657);
lean_ctor_set(x_772, 3, x_675);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_773 = x_675;
} else {
 lean_dec_ref(x_675);
 x_773 = lean_box(0);
}
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_772, sizeof(void*)*4, x_769);
lean_ctor_set_uint16(x_772, sizeof(void*)*4 + 4, x_770);
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 7, x_771);
x_774 = 0;
x_775 = 0;
x_776 = 0;
if (lean_is_scalar(x_773)) {
 x_777 = lean_alloc_ctor(1, 4, 8);
} else {
 x_777 = x_773;
}
lean_ctor_set(x_777, 0, x_764);
lean_ctor_set(x_777, 1, x_765);
lean_ctor_set(x_777, 2, x_766);
lean_ctor_set(x_777, 3, x_767);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_777, sizeof(void*)*4, x_774);
lean_ctor_set_uint16(x_777, sizeof(void*)*4 + 4, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 7, x_776);
x_778 = 0;
x_779 = 0;
x_780 = 0;
if (lean_is_scalar(x_763)) {
 x_781 = lean_alloc_ctor(1, 4, 8);
} else {
 x_781 = x_763;
}
lean_ctor_set(x_781, 0, x_772);
lean_ctor_set(x_781, 1, x_761);
lean_ctor_set(x_781, 2, x_762);
lean_ctor_set(x_781, 3, x_777);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_781, sizeof(void*)*4, x_778);
lean_ctor_set_uint16(x_781, sizeof(void*)*4 + 4, x_779);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 7, x_780);
return x_781;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; uint32_t x_790; uint16_t x_791; uint8_t x_792; lean_object* x_793; uint8_t x_794; uint32_t x_795; uint16_t x_796; uint8_t x_797; lean_object* x_798; uint32_t x_799; uint16_t x_800; uint8_t x_801; lean_object* x_802; 
x_782 = lean_ctor_get(x_674, 1);
lean_inc(x_782);
x_783 = lean_ctor_get(x_674, 2);
lean_inc(x_783);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_784 = x_674;
} else {
 lean_dec_ref(x_674);
 x_784 = lean_box(0);
}
x_785 = lean_ctor_get(x_675, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_675, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_675, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_675, 3);
lean_inc(x_788);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_789 = x_675;
} else {
 lean_dec_ref(x_675);
 x_789 = lean_box(0);
}
x_790 = 0;
x_791 = 0;
x_792 = 0;
if (lean_is_scalar(x_789)) {
 x_793 = lean_alloc_ctor(1, 4, 8);
} else {
 x_793 = x_789;
}
lean_ctor_set(x_793, 0, x_785);
lean_ctor_set(x_793, 1, x_786);
lean_ctor_set(x_793, 2, x_787);
lean_ctor_set(x_793, 3, x_788);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_793, sizeof(void*)*4, x_790);
lean_ctor_set_uint16(x_793, sizeof(void*)*4 + 4, x_791);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 7, x_792);
x_794 = 0;
x_795 = 0;
x_796 = 0;
x_797 = 0;
if (lean_is_scalar(x_784)) {
 x_798 = lean_alloc_ctor(1, 4, 8);
} else {
 x_798 = x_784;
}
lean_ctor_set(x_798, 0, x_793);
lean_ctor_set(x_798, 1, x_782);
lean_ctor_set(x_798, 2, x_783);
lean_ctor_set(x_798, 3, x_747);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 6, x_794);
lean_ctor_set_uint32(x_798, sizeof(void*)*4, x_795);
lean_ctor_set_uint16(x_798, sizeof(void*)*4 + 4, x_796);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 7, x_797);
x_799 = 0;
x_800 = 0;
x_801 = 0;
x_802 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_802, 0, x_655);
lean_ctor_set(x_802, 1, x_656);
lean_ctor_set(x_802, 2, x_657);
lean_ctor_set(x_802, 3, x_798);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_802, sizeof(void*)*4, x_799);
lean_ctor_set_uint16(x_802, sizeof(void*)*4 + 4, x_800);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 7, x_801);
return x_802;
}
}
}
}
}
}
}
else
{
uint8_t x_803; 
x_803 = l_RBNode_isRed___rarg(x_655);
if (x_803 == 0)
{
lean_object* x_804; uint32_t x_805; uint16_t x_806; uint8_t x_807; lean_object* x_808; 
x_804 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_655, x_2, x_3);
x_805 = 0;
x_806 = 0;
x_807 = 0;
x_808 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_808, 0, x_804);
lean_ctor_set(x_808, 1, x_656);
lean_ctor_set(x_808, 2, x_657);
lean_ctor_set(x_808, 3, x_658);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_808, sizeof(void*)*4, x_805);
lean_ctor_set_uint16(x_808, sizeof(void*)*4 + 4, x_806);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 7, x_807);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_655, x_2, x_3);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_809, 3);
lean_inc(x_811);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; uint32_t x_816; uint16_t x_817; uint8_t x_818; lean_object* x_819; uint8_t x_820; uint32_t x_821; uint16_t x_822; uint8_t x_823; lean_object* x_824; 
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
x_813 = lean_ctor_get(x_809, 2);
lean_inc(x_813);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_814 = x_809;
} else {
 lean_dec_ref(x_809);
 x_814 = lean_box(0);
}
x_815 = 0;
x_816 = 0;
x_817 = 0;
x_818 = 0;
if (lean_is_scalar(x_814)) {
 x_819 = lean_alloc_ctor(1, 4, 8);
} else {
 x_819 = x_814;
}
lean_ctor_set(x_819, 0, x_811);
lean_ctor_set(x_819, 1, x_812);
lean_ctor_set(x_819, 2, x_813);
lean_ctor_set(x_819, 3, x_811);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 6, x_815);
lean_ctor_set_uint32(x_819, sizeof(void*)*4, x_816);
lean_ctor_set_uint16(x_819, sizeof(void*)*4 + 4, x_817);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 7, x_818);
x_820 = 1;
x_821 = 0;
x_822 = 0;
x_823 = 0;
x_824 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_824, 0, x_819);
lean_ctor_set(x_824, 1, x_656);
lean_ctor_set(x_824, 2, x_657);
lean_ctor_set(x_824, 3, x_658);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 6, x_820);
lean_ctor_set_uint32(x_824, sizeof(void*)*4, x_821);
lean_ctor_set_uint16(x_824, sizeof(void*)*4 + 4, x_822);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 7, x_823);
return x_824;
}
else
{
uint8_t x_825; 
x_825 = lean_ctor_get_uint8(x_811, sizeof(void*)*4 + 6);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; uint32_t x_835; uint16_t x_836; uint8_t x_837; lean_object* x_838; uint32_t x_839; uint16_t x_840; uint8_t x_841; lean_object* x_842; uint32_t x_843; uint16_t x_844; uint8_t x_845; lean_object* x_846; 
x_826 = lean_ctor_get(x_809, 1);
lean_inc(x_826);
x_827 = lean_ctor_get(x_809, 2);
lean_inc(x_827);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_828 = x_809;
} else {
 lean_dec_ref(x_809);
 x_828 = lean_box(0);
}
x_829 = lean_ctor_get(x_811, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_811, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_811, 2);
lean_inc(x_831);
x_832 = lean_ctor_get(x_811, 3);
lean_inc(x_832);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 lean_ctor_release(x_811, 2);
 lean_ctor_release(x_811, 3);
 x_833 = x_811;
} else {
 lean_dec_ref(x_811);
 x_833 = lean_box(0);
}
x_834 = 1;
x_835 = 0;
x_836 = 0;
x_837 = 0;
if (lean_is_scalar(x_833)) {
 x_838 = lean_alloc_ctor(1, 4, 8);
} else {
 x_838 = x_833;
}
lean_ctor_set(x_838, 0, x_810);
lean_ctor_set(x_838, 1, x_826);
lean_ctor_set(x_838, 2, x_827);
lean_ctor_set(x_838, 3, x_829);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_838, sizeof(void*)*4, x_835);
lean_ctor_set_uint16(x_838, sizeof(void*)*4 + 4, x_836);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 7, x_837);
x_839 = 0;
x_840 = 0;
x_841 = 0;
if (lean_is_scalar(x_828)) {
 x_842 = lean_alloc_ctor(1, 4, 8);
} else {
 x_842 = x_828;
}
lean_ctor_set(x_842, 0, x_832);
lean_ctor_set(x_842, 1, x_656);
lean_ctor_set(x_842, 2, x_657);
lean_ctor_set(x_842, 3, x_658);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_842, sizeof(void*)*4, x_839);
lean_ctor_set_uint16(x_842, sizeof(void*)*4 + 4, x_840);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 7, x_841);
x_843 = 0;
x_844 = 0;
x_845 = 0;
x_846 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_846, 0, x_838);
lean_ctor_set(x_846, 1, x_830);
lean_ctor_set(x_846, 2, x_831);
lean_ctor_set(x_846, 3, x_842);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_846, sizeof(void*)*4, x_843);
lean_ctor_set_uint16(x_846, sizeof(void*)*4 + 4, x_844);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 7, x_845);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; uint32_t x_851; uint16_t x_852; uint8_t x_853; lean_object* x_854; uint32_t x_855; uint16_t x_856; uint8_t x_857; lean_object* x_858; 
x_847 = lean_ctor_get(x_809, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_809, 2);
lean_inc(x_848);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_849 = x_809;
} else {
 lean_dec_ref(x_809);
 x_849 = lean_box(0);
}
x_850 = 0;
x_851 = 0;
x_852 = 0;
x_853 = 0;
if (lean_is_scalar(x_849)) {
 x_854 = lean_alloc_ctor(1, 4, 8);
} else {
 x_854 = x_849;
}
lean_ctor_set(x_854, 0, x_810);
lean_ctor_set(x_854, 1, x_847);
lean_ctor_set(x_854, 2, x_848);
lean_ctor_set(x_854, 3, x_811);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 6, x_850);
lean_ctor_set_uint32(x_854, sizeof(void*)*4, x_851);
lean_ctor_set_uint16(x_854, sizeof(void*)*4 + 4, x_852);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 7, x_853);
x_855 = 0;
x_856 = 0;
x_857 = 0;
x_858 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_858, 0, x_854);
lean_ctor_set(x_858, 1, x_656);
lean_ctor_set(x_858, 2, x_657);
lean_ctor_set(x_858, 3, x_658);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_858, sizeof(void*)*4, x_855);
lean_ctor_set_uint16(x_858, sizeof(void*)*4 + 4, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 7, x_857);
return x_858;
}
}
}
else
{
uint8_t x_859; 
x_859 = lean_ctor_get_uint8(x_810, sizeof(void*)*4 + 6);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; uint32_t x_870; uint16_t x_871; uint8_t x_872; lean_object* x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_860 = lean_ctor_get(x_809, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_809, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_809, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_863 = x_809;
} else {
 lean_dec_ref(x_809);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_810, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_810, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_810, 2);
lean_inc(x_866);
x_867 = lean_ctor_get(x_810, 3);
lean_inc(x_867);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_868 = x_810;
} else {
 lean_dec_ref(x_810);
 x_868 = lean_box(0);
}
x_869 = 1;
x_870 = 0;
x_871 = 0;
x_872 = 0;
if (lean_is_scalar(x_868)) {
 x_873 = lean_alloc_ctor(1, 4, 8);
} else {
 x_873 = x_868;
}
lean_ctor_set(x_873, 0, x_864);
lean_ctor_set(x_873, 1, x_865);
lean_ctor_set(x_873, 2, x_866);
lean_ctor_set(x_873, 3, x_867);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_873, sizeof(void*)*4, x_870);
lean_ctor_set_uint16(x_873, sizeof(void*)*4 + 4, x_871);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 7, x_872);
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_863)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_863;
}
lean_ctor_set(x_877, 0, x_862);
lean_ctor_set(x_877, 1, x_656);
lean_ctor_set(x_877, 2, x_657);
lean_ctor_set(x_877, 3, x_658);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_860);
lean_ctor_set(x_881, 2, x_861);
lean_ctor_set(x_881, 3, x_877);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
lean_object* x_882; 
x_882 = lean_ctor_get(x_809, 3);
lean_inc(x_882);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; uint32_t x_887; uint16_t x_888; uint8_t x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; 
x_883 = lean_ctor_get(x_809, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_809, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_885 = x_809;
} else {
 lean_dec_ref(x_809);
 x_885 = lean_box(0);
}
x_886 = 0;
x_887 = 0;
x_888 = 0;
x_889 = 0;
if (lean_is_scalar(x_885)) {
 x_890 = lean_alloc_ctor(1, 4, 8);
} else {
 x_890 = x_885;
}
lean_ctor_set(x_890, 0, x_810);
lean_ctor_set(x_890, 1, x_883);
lean_ctor_set(x_890, 2, x_884);
lean_ctor_set(x_890, 3, x_882);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 6, x_886);
lean_ctor_set_uint32(x_890, sizeof(void*)*4, x_887);
lean_ctor_set_uint16(x_890, sizeof(void*)*4 + 4, x_888);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 7, x_889);
x_891 = 0;
x_892 = 0;
x_893 = 0;
x_894 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_656);
lean_ctor_set(x_894, 2, x_657);
lean_ctor_set(x_894, 3, x_658);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
return x_894;
}
else
{
uint8_t x_895; 
x_895 = lean_ctor_get_uint8(x_882, sizeof(void*)*4 + 6);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint32_t x_904; uint16_t x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; uint32_t x_909; uint16_t x_910; uint8_t x_911; lean_object* x_912; uint32_t x_913; uint16_t x_914; uint8_t x_915; lean_object* x_916; 
x_896 = lean_ctor_get(x_809, 1);
lean_inc(x_896);
x_897 = lean_ctor_get(x_809, 2);
lean_inc(x_897);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_898 = x_809;
} else {
 lean_dec_ref(x_809);
 x_898 = lean_box(0);
}
x_899 = lean_ctor_get(x_882, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_882, 1);
lean_inc(x_900);
x_901 = lean_ctor_get(x_882, 2);
lean_inc(x_901);
x_902 = lean_ctor_get(x_882, 3);
lean_inc(x_902);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 lean_ctor_release(x_882, 2);
 lean_ctor_release(x_882, 3);
 x_903 = x_882;
} else {
 lean_dec_ref(x_882);
 x_903 = lean_box(0);
}
x_904 = 0;
x_905 = 0;
x_906 = 0;
lean_inc(x_810);
if (lean_is_scalar(x_903)) {
 x_907 = lean_alloc_ctor(1, 4, 8);
} else {
 x_907 = x_903;
}
lean_ctor_set(x_907, 0, x_810);
lean_ctor_set(x_907, 1, x_896);
lean_ctor_set(x_907, 2, x_897);
lean_ctor_set(x_907, 3, x_899);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_908 = x_810;
} else {
 lean_dec_ref(x_810);
 x_908 = lean_box(0);
}
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_907, sizeof(void*)*4, x_904);
lean_ctor_set_uint16(x_907, sizeof(void*)*4 + 4, x_905);
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 7, x_906);
x_909 = 0;
x_910 = 0;
x_911 = 0;
if (lean_is_scalar(x_908)) {
 x_912 = lean_alloc_ctor(1, 4, 8);
} else {
 x_912 = x_908;
}
lean_ctor_set(x_912, 0, x_902);
lean_ctor_set(x_912, 1, x_656);
lean_ctor_set(x_912, 2, x_657);
lean_ctor_set(x_912, 3, x_658);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_912, sizeof(void*)*4, x_909);
lean_ctor_set_uint16(x_912, sizeof(void*)*4 + 4, x_910);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 7, x_911);
x_913 = 0;
x_914 = 0;
x_915 = 0;
if (lean_is_scalar(x_898)) {
 x_916 = lean_alloc_ctor(1, 4, 8);
} else {
 x_916 = x_898;
}
lean_ctor_set(x_916, 0, x_907);
lean_ctor_set(x_916, 1, x_900);
lean_ctor_set(x_916, 2, x_901);
lean_ctor_set(x_916, 3, x_912);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_916, sizeof(void*)*4, x_913);
lean_ctor_set_uint16(x_916, sizeof(void*)*4 + 4, x_914);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 7, x_915);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint32_t x_925; uint16_t x_926; uint8_t x_927; lean_object* x_928; uint8_t x_929; uint32_t x_930; uint16_t x_931; uint8_t x_932; lean_object* x_933; uint32_t x_934; uint16_t x_935; uint8_t x_936; lean_object* x_937; 
x_917 = lean_ctor_get(x_809, 1);
lean_inc(x_917);
x_918 = lean_ctor_get(x_809, 2);
lean_inc(x_918);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_919 = x_809;
} else {
 lean_dec_ref(x_809);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_810, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_810, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_810, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_810, 3);
lean_inc(x_923);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_924 = x_810;
} else {
 lean_dec_ref(x_810);
 x_924 = lean_box(0);
}
x_925 = 0;
x_926 = 0;
x_927 = 0;
if (lean_is_scalar(x_924)) {
 x_928 = lean_alloc_ctor(1, 4, 8);
} else {
 x_928 = x_924;
}
lean_ctor_set(x_928, 0, x_920);
lean_ctor_set(x_928, 1, x_921);
lean_ctor_set(x_928, 2, x_922);
lean_ctor_set(x_928, 3, x_923);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_928, sizeof(void*)*4, x_925);
lean_ctor_set_uint16(x_928, sizeof(void*)*4 + 4, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 7, x_927);
x_929 = 0;
x_930 = 0;
x_931 = 0;
x_932 = 0;
if (lean_is_scalar(x_919)) {
 x_933 = lean_alloc_ctor(1, 4, 8);
} else {
 x_933 = x_919;
}
lean_ctor_set(x_933, 0, x_928);
lean_ctor_set(x_933, 1, x_917);
lean_ctor_set(x_933, 2, x_918);
lean_ctor_set(x_933, 3, x_882);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 6, x_929);
lean_ctor_set_uint32(x_933, sizeof(void*)*4, x_930);
lean_ctor_set_uint16(x_933, sizeof(void*)*4 + 4, x_931);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 7, x_932);
x_934 = 0;
x_935 = 0;
x_936 = 0;
x_937 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_937, 0, x_933);
lean_ctor_set(x_937, 1, x_656);
lean_ctor_set(x_937, 2, x_657);
lean_ctor_set(x_937, 3, x_658);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_937, sizeof(void*)*4, x_934);
lean_ctor_set_uint16(x_937, sizeof(void*)*4 + 4, x_935);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 7, x_936);
return x_937;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_box_uint32(x_2);
x_9 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_9, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_9, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*4 + 7, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_unbox_uint32(x_13);
x_17 = x_2 < x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = lean_unbox_uint32(x_13);
x_19 = x_18 < x_2;
if (x_19 == 0)
{
uint32_t x_20; uint16_t x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = 0;
x_21 = 0;
x_22 = 0;
x_23 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_20);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_21);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_22);
return x_1;
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_15, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 3, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; uint32_t x_29; uint16_t x_30; uint8_t x_31; 
x_28 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_12, x_2, x_3);
x_29 = 0;
x_30 = 0;
x_31 = 0;
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_29);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_30);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_31);
return x_1;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_36 = lean_unbox_uint32(x_33);
x_37 = x_2 < x_36;
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = lean_unbox_uint32(x_33);
x_39 = x_38 < x_2;
if (x_39 == 0)
{
uint32_t x_40; uint16_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_33);
x_40 = 0;
x_41 = 0;
x_42 = 0;
x_43 = lean_box_uint32(x_2);
x_44 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_44, sizeof(void*)*4, x_40);
lean_ctor_set_uint16(x_44, sizeof(void*)*4 + 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 7, x_42);
return x_44;
}
else
{
lean_object* x_45; uint32_t x_46; uint16_t x_47; uint8_t x_48; lean_object* x_49; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_35, x_2, x_3);
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_33);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_49, sizeof(void*)*4, x_46);
lean_ctor_set_uint16(x_49, sizeof(void*)*4 + 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 7, x_48);
return x_49;
}
}
else
{
lean_object* x_50; uint32_t x_51; uint16_t x_52; uint8_t x_53; lean_object* x_54; 
x_50 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_32, x_2, x_3);
x_51 = 0;
x_52 = 0;
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_34);
lean_ctor_set(x_54, 3, x_35);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_54, sizeof(void*)*4, x_51);
lean_ctor_set_uint16(x_54, sizeof(void*)*4 + 4, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 7, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint32_t x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
x_60 = lean_unbox_uint32(x_57);
x_61 = x_2 < x_60;
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = lean_unbox_uint32(x_57);
x_63 = x_62 < x_2;
if (x_63 == 0)
{
uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_58);
lean_dec(x_57);
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_67);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_64);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_66);
return x_1;
}
else
{
uint8_t x_68; 
x_68 = l_RBNode_isRed___rarg(x_59);
if (x_68 == 0)
{
lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; 
x_69 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_59, x_2, x_3);
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_1, 3, x_69);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_72);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_59, x_2, x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 3);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; uint8_t x_83; uint32_t x_84; uint16_t x_85; uint8_t x_86; 
x_77 = lean_ctor_get(x_73, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
lean_ctor_set(x_73, 0, x_75);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_82);
x_83 = 1;
x_84 = 0;
x_85 = 0;
x_86 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_83);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_84);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_86);
return x_1;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint32_t x_90; uint16_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint32_t x_95; uint16_t x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_73, 1);
x_88 = lean_ctor_get(x_73, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = 0;
x_90 = 0;
x_91 = 0;
x_92 = 0;
x_93 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_75);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 6, x_89);
lean_ctor_set_uint32(x_93, sizeof(void*)*4, x_90);
lean_ctor_set_uint16(x_93, sizeof(void*)*4 + 4, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*4 + 7, x_92);
x_94 = 1;
x_95 = 0;
x_96 = 0;
x_97 = 0;
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_94);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_95);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_97);
return x_1;
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_75, sizeof(void*)*4 + 6);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_73);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_73, 1);
x_101 = lean_ctor_get(x_73, 2);
x_102 = lean_ctor_get(x_73, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_73, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_75);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint32_t x_110; uint16_t x_111; uint8_t x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; uint32_t x_116; uint16_t x_117; uint8_t x_118; 
x_105 = lean_ctor_get(x_75, 0);
x_106 = lean_ctor_get(x_75, 1);
x_107 = lean_ctor_get(x_75, 2);
x_108 = lean_ctor_get(x_75, 3);
x_109 = 1;
x_110 = 0;
x_111 = 0;
x_112 = 0;
lean_ctor_set(x_75, 3, x_74);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_75, sizeof(void*)*4, x_110);
lean_ctor_set_uint16(x_75, sizeof(void*)*4 + 4, x_111);
lean_ctor_set_uint8(x_75, sizeof(void*)*4 + 7, x_112);
x_113 = 0;
x_114 = 0;
x_115 = 0;
lean_ctor_set(x_73, 3, x_108);
lean_ctor_set(x_73, 2, x_107);
lean_ctor_set(x_73, 1, x_106);
lean_ctor_set(x_73, 0, x_105);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_109);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_113);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_114);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_115);
x_116 = 0;
x_117 = 0;
x_118 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_116);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_118);
return x_1;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; uint32_t x_128; uint16_t x_129; uint8_t x_130; uint32_t x_131; uint16_t x_132; uint8_t x_133; 
x_119 = lean_ctor_get(x_75, 0);
x_120 = lean_ctor_get(x_75, 1);
x_121 = lean_ctor_get(x_75, 2);
x_122 = lean_ctor_get(x_75, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_75);
x_123 = 1;
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_127, 0, x_56);
lean_ctor_set(x_127, 1, x_57);
lean_ctor_set(x_127, 2, x_58);
lean_ctor_set(x_127, 3, x_74);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_127, sizeof(void*)*4, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*4 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 7, x_126);
x_128 = 0;
x_129 = 0;
x_130 = 0;
lean_ctor_set(x_73, 3, x_122);
lean_ctor_set(x_73, 2, x_121);
lean_ctor_set(x_73, 1, x_120);
lean_ctor_set(x_73, 0, x_119);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_123);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_128);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_129);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_130);
x_131 = 0;
x_132 = 0;
x_133 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_127);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_131);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_132);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_133);
return x_1;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint32_t x_142; uint16_t x_143; uint8_t x_144; lean_object* x_145; uint32_t x_146; uint16_t x_147; uint8_t x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_73, 1);
x_135 = lean_ctor_get(x_73, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_73);
x_136 = lean_ctor_get(x_75, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_75, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_75, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_75, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_140 = x_75;
} else {
 lean_dec_ref(x_75);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = 0;
x_143 = 0;
x_144 = 0;
if (lean_is_scalar(x_140)) {
 x_145 = lean_alloc_ctor(1, 4, 8);
} else {
 x_145 = x_140;
}
lean_ctor_set(x_145, 0, x_56);
lean_ctor_set(x_145, 1, x_57);
lean_ctor_set(x_145, 2, x_58);
lean_ctor_set(x_145, 3, x_74);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_145, sizeof(void*)*4, x_142);
lean_ctor_set_uint16(x_145, sizeof(void*)*4 + 4, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*4 + 7, x_144);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_137);
lean_ctor_set(x_149, 2, x_138);
lean_ctor_set(x_149, 3, x_139);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 6, x_141);
lean_ctor_set_uint32(x_149, sizeof(void*)*4, x_146);
lean_ctor_set_uint16(x_149, sizeof(void*)*4 + 4, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*4 + 7, x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_149);
lean_ctor_set(x_1, 2, x_135);
lean_ctor_set(x_1, 1, x_134);
lean_ctor_set(x_1, 0, x_145);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_73);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint32_t x_157; uint16_t x_158; uint8_t x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_154 = lean_ctor_get(x_73, 3);
lean_dec(x_154);
x_155 = lean_ctor_get(x_73, 0);
lean_dec(x_155);
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_156);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_157);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_158);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_159);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; uint32_t x_170; uint16_t x_171; uint8_t x_172; 
x_163 = lean_ctor_get(x_73, 1);
x_164 = lean_ctor_get(x_73, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_73);
x_165 = 0;
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_169, 0, x_74);
lean_ctor_set(x_169, 1, x_163);
lean_ctor_set(x_169, 2, x_164);
lean_ctor_set(x_169, 3, x_75);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 6, x_165);
lean_ctor_set_uint32(x_169, sizeof(void*)*4, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*4 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4 + 7, x_168);
x_170 = 0;
x_171 = 0;
x_172 = 0;
lean_ctor_set(x_1, 3, x_169);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_98);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_170);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_171);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_172);
return x_1;
}
}
}
}
else
{
uint8_t x_173; 
x_173 = lean_ctor_get_uint8(x_74, sizeof(void*)*4 + 6);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_73);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_73, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_74);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint32_t x_182; uint16_t x_183; uint8_t x_184; uint32_t x_185; uint16_t x_186; uint8_t x_187; uint32_t x_188; uint16_t x_189; uint8_t x_190; 
x_177 = lean_ctor_get(x_74, 0);
x_178 = lean_ctor_get(x_74, 1);
x_179 = lean_ctor_get(x_74, 2);
x_180 = lean_ctor_get(x_74, 3);
x_181 = 1;
x_182 = 0;
x_183 = 0;
x_184 = 0;
lean_ctor_set(x_74, 3, x_177);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_182);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_183);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_184);
x_185 = 0;
x_186 = 0;
x_187 = 0;
lean_ctor_set(x_73, 0, x_180);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_181);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_185);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_186);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_187);
x_188 = 0;
x_189 = 0;
x_190 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_179);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_74);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_188);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_190);
return x_1;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint32_t x_196; uint16_t x_197; uint8_t x_198; lean_object* x_199; uint32_t x_200; uint16_t x_201; uint8_t x_202; uint32_t x_203; uint16_t x_204; uint8_t x_205; 
x_191 = lean_ctor_get(x_74, 0);
x_192 = lean_ctor_get(x_74, 1);
x_193 = lean_ctor_get(x_74, 2);
x_194 = lean_ctor_get(x_74, 3);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_74);
x_195 = 1;
x_196 = 0;
x_197 = 0;
x_198 = 0;
x_199 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_199, 0, x_56);
lean_ctor_set(x_199, 1, x_57);
lean_ctor_set(x_199, 2, x_58);
lean_ctor_set(x_199, 3, x_191);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_199, sizeof(void*)*4, x_196);
lean_ctor_set_uint16(x_199, sizeof(void*)*4 + 4, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4 + 7, x_198);
x_200 = 0;
x_201 = 0;
x_202 = 0;
lean_ctor_set(x_73, 0, x_194);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_195);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_200);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_201);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_202);
x_203 = 0;
x_204 = 0;
x_205 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set(x_1, 2, x_193);
lean_ctor_set(x_1, 1, x_192);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_203);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_205);
return x_1;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint32_t x_215; uint16_t x_216; uint8_t x_217; lean_object* x_218; uint32_t x_219; uint16_t x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; 
x_206 = lean_ctor_get(x_73, 1);
x_207 = lean_ctor_get(x_73, 2);
x_208 = lean_ctor_get(x_73, 3);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_73);
x_209 = lean_ctor_get(x_74, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_74, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_74, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_74, 3);
lean_inc(x_212);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_213 = x_74;
} else {
 lean_dec_ref(x_74);
 x_213 = lean_box(0);
}
x_214 = 1;
x_215 = 0;
x_216 = 0;
x_217 = 0;
if (lean_is_scalar(x_213)) {
 x_218 = lean_alloc_ctor(1, 4, 8);
} else {
 x_218 = x_213;
}
lean_ctor_set(x_218, 0, x_56);
lean_ctor_set(x_218, 1, x_57);
lean_ctor_set(x_218, 2, x_58);
lean_ctor_set(x_218, 3, x_209);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_218, sizeof(void*)*4, x_215);
lean_ctor_set_uint16(x_218, sizeof(void*)*4 + 4, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 7, x_217);
x_219 = 0;
x_220 = 0;
x_221 = 0;
x_222 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_206);
lean_ctor_set(x_222, 2, x_207);
lean_ctor_set(x_222, 3, x_208);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 6, x_214);
lean_ctor_set_uint32(x_222, sizeof(void*)*4, x_219);
lean_ctor_set_uint16(x_222, sizeof(void*)*4 + 4, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*4 + 7, x_221);
x_223 = 0;
x_224 = 0;
x_225 = 0;
lean_ctor_set(x_1, 3, x_222);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_218);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_223);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_225);
return x_1;
}
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_73, 3);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_73);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; uint32_t x_231; uint16_t x_232; uint8_t x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_228 = lean_ctor_get(x_73, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_73, 0);
lean_dec(x_229);
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_230);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_231);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_232);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_233);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; uint32_t x_244; uint16_t x_245; uint8_t x_246; 
x_237 = lean_ctor_get(x_73, 1);
x_238 = lean_ctor_get(x_73, 2);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_73);
x_239 = 0;
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_243, 0, x_74);
lean_ctor_set(x_243, 1, x_237);
lean_ctor_set(x_243, 2, x_238);
lean_ctor_set(x_243, 3, x_226);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 6, x_239);
lean_ctor_set_uint32(x_243, sizeof(void*)*4, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*4 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*4 + 7, x_242);
x_244 = 0;
x_245 = 0;
x_246 = 0;
lean_ctor_set(x_1, 3, x_243);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_244);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_246);
return x_1;
}
}
else
{
uint8_t x_247; 
x_247 = lean_ctor_get_uint8(x_226, sizeof(void*)*4 + 6);
if (x_247 == 0)
{
uint8_t x_248; 
lean_free_object(x_1);
x_248 = !lean_is_exclusive(x_73);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_249 = lean_ctor_get(x_73, 3);
lean_dec(x_249);
x_250 = lean_ctor_get(x_73, 0);
lean_dec(x_250);
x_251 = !lean_is_exclusive(x_226);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint32_t x_256; uint16_t x_257; uint8_t x_258; uint8_t x_259; 
x_252 = lean_ctor_get(x_226, 0);
x_253 = lean_ctor_get(x_226, 1);
x_254 = lean_ctor_get(x_226, 2);
x_255 = lean_ctor_get(x_226, 3);
x_256 = 0;
x_257 = 0;
x_258 = 0;
lean_inc(x_74);
lean_ctor_set(x_226, 3, x_74);
lean_ctor_set(x_226, 2, x_58);
lean_ctor_set(x_226, 1, x_57);
lean_ctor_set(x_226, 0, x_56);
x_259 = !lean_is_exclusive(x_74);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; uint32_t x_267; uint16_t x_268; uint8_t x_269; 
x_260 = lean_ctor_get(x_74, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_74, 2);
lean_dec(x_261);
x_262 = lean_ctor_get(x_74, 1);
lean_dec(x_262);
x_263 = lean_ctor_get(x_74, 0);
lean_dec(x_263);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_74, 3, x_255);
lean_ctor_set(x_74, 2, x_254);
lean_ctor_set(x_74, 1, x_253);
lean_ctor_set(x_74, 0, x_252);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_266);
x_267 = 0;
x_268 = 0;
x_269 = 0;
lean_ctor_set(x_73, 3, x_74);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_267);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_268);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_269);
return x_73;
}
else
{
uint32_t x_270; uint16_t x_271; uint8_t x_272; lean_object* x_273; uint32_t x_274; uint16_t x_275; uint8_t x_276; 
lean_dec(x_74);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_226, sizeof(void*)*4, x_256);
lean_ctor_set_uint16(x_226, sizeof(void*)*4 + 4, x_257);
lean_ctor_set_uint8(x_226, sizeof(void*)*4 + 7, x_258);
x_270 = 0;
x_271 = 0;
x_272 = 0;
x_273 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_273, 0, x_252);
lean_ctor_set(x_273, 1, x_253);
lean_ctor_set(x_273, 2, x_254);
lean_ctor_set(x_273, 3, x_255);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_273, sizeof(void*)*4, x_270);
lean_ctor_set_uint16(x_273, sizeof(void*)*4 + 4, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*4 + 7, x_272);
x_274 = 0;
x_275 = 0;
x_276 = 0;
lean_ctor_set(x_73, 3, x_273);
lean_ctor_set(x_73, 0, x_226);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_274);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_275);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_276);
return x_73;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint32_t x_281; uint16_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; uint32_t x_286; uint16_t x_287; uint8_t x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; 
x_277 = lean_ctor_get(x_226, 0);
x_278 = lean_ctor_get(x_226, 1);
x_279 = lean_ctor_get(x_226, 2);
x_280 = lean_ctor_get(x_226, 3);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_226);
x_281 = 0;
x_282 = 0;
x_283 = 0;
lean_inc(x_74);
x_284 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_284, 0, x_56);
lean_ctor_set(x_284, 1, x_57);
lean_ctor_set(x_284, 2, x_58);
lean_ctor_set(x_284, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_285 = x_74;
} else {
 lean_dec_ref(x_74);
 x_285 = lean_box(0);
}
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_284, sizeof(void*)*4, x_281);
lean_ctor_set_uint16(x_284, sizeof(void*)*4 + 4, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*4 + 7, x_283);
x_286 = 0;
x_287 = 0;
x_288 = 0;
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(1, 4, 8);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_277);
lean_ctor_set(x_289, 1, x_278);
lean_ctor_set(x_289, 2, x_279);
lean_ctor_set(x_289, 3, x_280);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_289, sizeof(void*)*4, x_286);
lean_ctor_set_uint16(x_289, sizeof(void*)*4 + 4, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*4 + 7, x_288);
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_ctor_set(x_73, 3, x_289);
lean_ctor_set(x_73, 0, x_284);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_292);
return x_73;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint32_t x_300; uint16_t x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint32_t x_305; uint16_t x_306; uint8_t x_307; lean_object* x_308; uint32_t x_309; uint16_t x_310; uint8_t x_311; lean_object* x_312; 
x_293 = lean_ctor_get(x_73, 1);
x_294 = lean_ctor_get(x_73, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_73);
x_295 = lean_ctor_get(x_226, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_226, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_226, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_226, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 x_299 = x_226;
} else {
 lean_dec_ref(x_226);
 x_299 = lean_box(0);
}
x_300 = 0;
x_301 = 0;
x_302 = 0;
lean_inc(x_74);
if (lean_is_scalar(x_299)) {
 x_303 = lean_alloc_ctor(1, 4, 8);
} else {
 x_303 = x_299;
}
lean_ctor_set(x_303, 0, x_56);
lean_ctor_set(x_303, 1, x_57);
lean_ctor_set(x_303, 2, x_58);
lean_ctor_set(x_303, 3, x_74);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_304 = x_74;
} else {
 lean_dec_ref(x_74);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_303, sizeof(void*)*4, x_300);
lean_ctor_set_uint16(x_303, sizeof(void*)*4 + 4, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*4 + 7, x_302);
x_305 = 0;
x_306 = 0;
x_307 = 0;
if (lean_is_scalar(x_304)) {
 x_308 = lean_alloc_ctor(1, 4, 8);
} else {
 x_308 = x_304;
}
lean_ctor_set(x_308, 0, x_295);
lean_ctor_set(x_308, 1, x_296);
lean_ctor_set(x_308, 2, x_297);
lean_ctor_set(x_308, 3, x_298);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 6, x_173);
lean_ctor_set_uint32(x_308, sizeof(void*)*4, x_305);
lean_ctor_set_uint16(x_308, sizeof(void*)*4 + 4, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*4 + 7, x_307);
x_309 = 0;
x_310 = 0;
x_311 = 0;
x_312 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_312, 0, x_303);
lean_ctor_set(x_312, 1, x_293);
lean_ctor_set(x_312, 2, x_294);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_312, sizeof(void*)*4, x_309);
lean_ctor_set_uint16(x_312, sizeof(void*)*4 + 4, x_310);
lean_ctor_set_uint8(x_312, sizeof(void*)*4 + 7, x_311);
return x_312;
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_73);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_73, 3);
lean_dec(x_314);
x_315 = lean_ctor_get(x_73, 0);
lean_dec(x_315);
x_316 = !lean_is_exclusive(x_74);
if (x_316 == 0)
{
uint32_t x_317; uint16_t x_318; uint8_t x_319; uint8_t x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; uint32_t x_324; uint16_t x_325; uint8_t x_326; 
x_317 = 0;
x_318 = 0;
x_319 = 0;
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_74, sizeof(void*)*4, x_317);
lean_ctor_set_uint16(x_74, sizeof(void*)*4 + 4, x_318);
lean_ctor_set_uint8(x_74, sizeof(void*)*4 + 7, x_319);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = 0;
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_320);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_323);
x_324 = 0;
x_325 = 0;
x_326 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_324);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_326);
return x_1;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; uint8_t x_335; uint32_t x_336; uint16_t x_337; uint8_t x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; 
x_327 = lean_ctor_get(x_74, 0);
x_328 = lean_ctor_get(x_74, 1);
x_329 = lean_ctor_get(x_74, 2);
x_330 = lean_ctor_get(x_74, 3);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_74);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_334, 0, x_327);
lean_ctor_set(x_334, 1, x_328);
lean_ctor_set(x_334, 2, x_329);
lean_ctor_set(x_334, 3, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_334, sizeof(void*)*4, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*4 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*4 + 7, x_333);
x_335 = 0;
x_336 = 0;
x_337 = 0;
x_338 = 0;
lean_ctor_set(x_73, 0, x_334);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 6, x_335);
lean_ctor_set_uint32(x_73, sizeof(void*)*4, x_336);
lean_ctor_set_uint16(x_73, sizeof(void*)*4 + 4, x_337);
lean_ctor_set_uint8(x_73, sizeof(void*)*4 + 7, x_338);
x_339 = 0;
x_340 = 0;
x_341 = 0;
lean_ctor_set(x_1, 3, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_341);
return x_1;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint32_t x_349; uint16_t x_350; uint8_t x_351; lean_object* x_352; uint8_t x_353; uint32_t x_354; uint16_t x_355; uint8_t x_356; lean_object* x_357; uint32_t x_358; uint16_t x_359; uint8_t x_360; 
x_342 = lean_ctor_get(x_73, 1);
x_343 = lean_ctor_get(x_73, 2);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_73);
x_344 = lean_ctor_get(x_74, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_74, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_74, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_74, 3);
lean_inc(x_347);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_348 = x_74;
} else {
 lean_dec_ref(x_74);
 x_348 = lean_box(0);
}
x_349 = 0;
x_350 = 0;
x_351 = 0;
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(1, 4, 8);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_345);
lean_ctor_set(x_352, 2, x_346);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_352, sizeof(void*)*4, x_349);
lean_ctor_set_uint16(x_352, sizeof(void*)*4 + 4, x_350);
lean_ctor_set_uint8(x_352, sizeof(void*)*4 + 7, x_351);
x_353 = 0;
x_354 = 0;
x_355 = 0;
x_356 = 0;
x_357 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_342);
lean_ctor_set(x_357, 2, x_343);
lean_ctor_set(x_357, 3, x_226);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_353);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_354);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_356);
x_358 = 0;
x_359 = 0;
x_360 = 0;
lean_ctor_set(x_1, 3, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_247);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_358);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_359);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_360);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_361; 
x_361 = l_RBNode_isRed___rarg(x_56);
if (x_361 == 0)
{
lean_object* x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; 
x_362 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_56, x_2, x_3);
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_1, 0, x_362);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_365);
return x_1;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_56, x_2, x_3);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_366, 3);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_366);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; uint8_t x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; 
x_370 = lean_ctor_get(x_366, 3);
lean_dec(x_370);
x_371 = lean_ctor_get(x_366, 0);
lean_dec(x_371);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
lean_ctor_set(x_366, 0, x_368);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_375);
x_376 = 1;
x_377 = 0;
x_378 = 0;
x_379 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_376);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_377);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_378);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_379);
return x_1;
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; uint8_t x_387; uint32_t x_388; uint16_t x_389; uint8_t x_390; 
x_380 = lean_ctor_get(x_366, 1);
x_381 = lean_ctor_get(x_366, 2);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_366);
x_382 = 0;
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_386, 0, x_368);
lean_ctor_set(x_386, 1, x_380);
lean_ctor_set(x_386, 2, x_381);
lean_ctor_set(x_386, 3, x_368);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 6, x_382);
lean_ctor_set_uint32(x_386, sizeof(void*)*4, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*4 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4 + 7, x_385);
x_387 = 1;
x_388 = 0;
x_389 = 0;
x_390 = 0;
lean_ctor_set(x_1, 0, x_386);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_387);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_388);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_389);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_390);
return x_1;
}
}
else
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_368, sizeof(void*)*4 + 6);
if (x_391 == 0)
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_366);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_393 = lean_ctor_get(x_366, 1);
x_394 = lean_ctor_get(x_366, 2);
x_395 = lean_ctor_get(x_366, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_366, 0);
lean_dec(x_396);
x_397 = !lean_is_exclusive(x_368);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; uint32_t x_403; uint16_t x_404; uint8_t x_405; uint32_t x_406; uint16_t x_407; uint8_t x_408; uint32_t x_409; uint16_t x_410; uint8_t x_411; 
x_398 = lean_ctor_get(x_368, 0);
x_399 = lean_ctor_get(x_368, 1);
x_400 = lean_ctor_get(x_368, 2);
x_401 = lean_ctor_get(x_368, 3);
x_402 = 1;
x_403 = 0;
x_404 = 0;
x_405 = 0;
lean_ctor_set(x_368, 3, x_398);
lean_ctor_set(x_368, 2, x_394);
lean_ctor_set(x_368, 1, x_393);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_368, sizeof(void*)*4, x_403);
lean_ctor_set_uint16(x_368, sizeof(void*)*4 + 4, x_404);
lean_ctor_set_uint8(x_368, sizeof(void*)*4 + 7, x_405);
x_406 = 0;
x_407 = 0;
x_408 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_401);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_402);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_406);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_407);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_408);
x_409 = 0;
x_410 = 0;
x_411 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_400);
lean_ctor_set(x_1, 1, x_399);
lean_ctor_set(x_1, 0, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_409);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_411);
return x_1;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; uint32_t x_417; uint16_t x_418; uint8_t x_419; lean_object* x_420; uint32_t x_421; uint16_t x_422; uint8_t x_423; uint32_t x_424; uint16_t x_425; uint8_t x_426; 
x_412 = lean_ctor_get(x_368, 0);
x_413 = lean_ctor_get(x_368, 1);
x_414 = lean_ctor_get(x_368, 2);
x_415 = lean_ctor_get(x_368, 3);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_368);
x_416 = 1;
x_417 = 0;
x_418 = 0;
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_420, 0, x_367);
lean_ctor_set(x_420, 1, x_393);
lean_ctor_set(x_420, 2, x_394);
lean_ctor_set(x_420, 3, x_412);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_420, sizeof(void*)*4, x_417);
lean_ctor_set_uint16(x_420, sizeof(void*)*4 + 4, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4 + 7, x_419);
x_421 = 0;
x_422 = 0;
x_423 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_415);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_416);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_421);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_422);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_423);
x_424 = 0;
x_425 = 0;
x_426 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_414);
lean_ctor_set(x_1, 1, x_413);
lean_ctor_set(x_1, 0, x_420);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_424);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_425);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_426);
return x_1;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_427 = lean_ctor_get(x_366, 1);
x_428 = lean_ctor_get(x_366, 2);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_366);
x_429 = lean_ctor_get(x_368, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_368, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_368, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_368, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 x_433 = x_368;
} else {
 lean_dec_ref(x_368);
 x_433 = lean_box(0);
}
x_434 = 1;
x_435 = 0;
x_436 = 0;
x_437 = 0;
if (lean_is_scalar(x_433)) {
 x_438 = lean_alloc_ctor(1, 4, 8);
} else {
 x_438 = x_433;
}
lean_ctor_set(x_438, 0, x_367);
lean_ctor_set(x_438, 1, x_427);
lean_ctor_set(x_438, 2, x_428);
lean_ctor_set(x_438, 3, x_429);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_438, sizeof(void*)*4, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*4 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*4 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_442, 0, x_432);
lean_ctor_set(x_442, 1, x_57);
lean_ctor_set(x_442, 2, x_58);
lean_ctor_set(x_442, 3, x_59);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 6, x_434);
lean_ctor_set_uint32(x_442, sizeof(void*)*4, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*4 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*4 + 7, x_441);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 3, x_442);
lean_ctor_set(x_1, 2, x_431);
lean_ctor_set(x_1, 1, x_430);
lean_ctor_set(x_1, 0, x_438);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
}
else
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_366);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint32_t x_450; uint16_t x_451; uint8_t x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_447 = lean_ctor_get(x_366, 3);
lean_dec(x_447);
x_448 = lean_ctor_get(x_366, 0);
lean_dec(x_448);
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_449);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_450);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_451);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_452);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; 
x_456 = lean_ctor_get(x_366, 1);
x_457 = lean_ctor_get(x_366, 2);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_366);
x_458 = 0;
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_462, 0, x_367);
lean_ctor_set(x_462, 1, x_456);
lean_ctor_set(x_462, 2, x_457);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 6, x_458);
lean_ctor_set_uint32(x_462, sizeof(void*)*4, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*4 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*4 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
lean_ctor_set(x_1, 0, x_462);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_391);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_463);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_464);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_465);
return x_1;
}
}
}
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_367, sizeof(void*)*4 + 6);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_366);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_468 = lean_ctor_get(x_366, 1);
x_469 = lean_ctor_get(x_366, 2);
x_470 = lean_ctor_get(x_366, 3);
x_471 = lean_ctor_get(x_366, 0);
lean_dec(x_471);
x_472 = !lean_is_exclusive(x_367);
if (x_472 == 0)
{
uint8_t x_473; uint32_t x_474; uint16_t x_475; uint8_t x_476; uint32_t x_477; uint16_t x_478; uint8_t x_479; uint32_t x_480; uint16_t x_481; uint8_t x_482; 
x_473 = 1;
x_474 = 0;
x_475 = 0;
x_476 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_474);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_475);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_476);
x_477 = 0;
x_478 = 0;
x_479 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_473);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_477);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_478);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_479);
x_480 = 0;
x_481 = 0;
x_482 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_367);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_480);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_482);
return x_1;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; uint32_t x_488; uint16_t x_489; uint8_t x_490; lean_object* x_491; uint32_t x_492; uint16_t x_493; uint8_t x_494; uint32_t x_495; uint16_t x_496; uint8_t x_497; 
x_483 = lean_ctor_get(x_367, 0);
x_484 = lean_ctor_get(x_367, 1);
x_485 = lean_ctor_get(x_367, 2);
x_486 = lean_ctor_get(x_367, 3);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_367);
x_487 = 1;
x_488 = 0;
x_489 = 0;
x_490 = 0;
x_491 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_491, 0, x_483);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_485);
lean_ctor_set(x_491, 3, x_486);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_491, sizeof(void*)*4, x_488);
lean_ctor_set_uint16(x_491, sizeof(void*)*4 + 4, x_489);
lean_ctor_set_uint8(x_491, sizeof(void*)*4 + 7, x_490);
x_492 = 0;
x_493 = 0;
x_494 = 0;
lean_ctor_set(x_366, 3, x_59);
lean_ctor_set(x_366, 2, x_58);
lean_ctor_set(x_366, 1, x_57);
lean_ctor_set(x_366, 0, x_470);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_487);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_492);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_493);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_494);
x_495 = 0;
x_496 = 0;
x_497 = 0;
lean_ctor_set(x_1, 3, x_366);
lean_ctor_set(x_1, 2, x_469);
lean_ctor_set(x_1, 1, x_468);
lean_ctor_set(x_1, 0, x_491);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_495);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_496);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_497);
return x_1;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; uint32_t x_507; uint16_t x_508; uint8_t x_509; lean_object* x_510; uint32_t x_511; uint16_t x_512; uint8_t x_513; lean_object* x_514; uint32_t x_515; uint16_t x_516; uint8_t x_517; 
x_498 = lean_ctor_get(x_366, 1);
x_499 = lean_ctor_get(x_366, 2);
x_500 = lean_ctor_get(x_366, 3);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_366);
x_501 = lean_ctor_get(x_367, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_367, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_367, 2);
lean_inc(x_503);
x_504 = lean_ctor_get(x_367, 3);
lean_inc(x_504);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_505 = x_367;
} else {
 lean_dec_ref(x_367);
 x_505 = lean_box(0);
}
x_506 = 1;
x_507 = 0;
x_508 = 0;
x_509 = 0;
if (lean_is_scalar(x_505)) {
 x_510 = lean_alloc_ctor(1, 4, 8);
} else {
 x_510 = x_505;
}
lean_ctor_set(x_510, 0, x_501);
lean_ctor_set(x_510, 1, x_502);
lean_ctor_set(x_510, 2, x_503);
lean_ctor_set(x_510, 3, x_504);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_510, sizeof(void*)*4, x_507);
lean_ctor_set_uint16(x_510, sizeof(void*)*4 + 4, x_508);
lean_ctor_set_uint8(x_510, sizeof(void*)*4 + 7, x_509);
x_511 = 0;
x_512 = 0;
x_513 = 0;
x_514 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_57);
lean_ctor_set(x_514, 2, x_58);
lean_ctor_set(x_514, 3, x_59);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 6, x_506);
lean_ctor_set_uint32(x_514, sizeof(void*)*4, x_511);
lean_ctor_set_uint16(x_514, sizeof(void*)*4 + 4, x_512);
lean_ctor_set_uint8(x_514, sizeof(void*)*4 + 7, x_513);
x_515 = 0;
x_516 = 0;
x_517 = 0;
lean_ctor_set(x_1, 3, x_514);
lean_ctor_set(x_1, 2, x_499);
lean_ctor_set(x_1, 1, x_498);
lean_ctor_set(x_1, 0, x_510);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_515);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_516);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_517);
return x_1;
}
}
else
{
lean_object* x_518; 
x_518 = lean_ctor_get(x_366, 3);
lean_inc(x_518);
if (lean_obj_tag(x_518) == 0)
{
uint8_t x_519; 
x_519 = !lean_is_exclusive(x_366);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint32_t x_523; uint16_t x_524; uint8_t x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_520 = lean_ctor_get(x_366, 3);
lean_dec(x_520);
x_521 = lean_ctor_get(x_366, 0);
lean_dec(x_521);
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_522);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_523);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_524);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_525);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; uint32_t x_536; uint16_t x_537; uint8_t x_538; 
x_529 = lean_ctor_get(x_366, 1);
x_530 = lean_ctor_get(x_366, 2);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_366);
x_531 = 0;
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_535, 0, x_367);
lean_ctor_set(x_535, 1, x_529);
lean_ctor_set(x_535, 2, x_530);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 6, x_531);
lean_ctor_set_uint32(x_535, sizeof(void*)*4, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*4 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*4 + 7, x_534);
x_536 = 0;
x_537 = 0;
x_538 = 0;
lean_ctor_set(x_1, 0, x_535);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_536);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_537);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_538);
return x_1;
}
}
else
{
uint8_t x_539; 
x_539 = lean_ctor_get_uint8(x_518, sizeof(void*)*4 + 6);
if (x_539 == 0)
{
uint8_t x_540; 
lean_free_object(x_1);
x_540 = !lean_is_exclusive(x_366);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_541 = lean_ctor_get(x_366, 1);
x_542 = lean_ctor_get(x_366, 2);
x_543 = lean_ctor_get(x_366, 3);
lean_dec(x_543);
x_544 = lean_ctor_get(x_366, 0);
lean_dec(x_544);
x_545 = !lean_is_exclusive(x_518);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint32_t x_550; uint16_t x_551; uint8_t x_552; uint8_t x_553; 
x_546 = lean_ctor_get(x_518, 0);
x_547 = lean_ctor_get(x_518, 1);
x_548 = lean_ctor_get(x_518, 2);
x_549 = lean_ctor_get(x_518, 3);
x_550 = 0;
x_551 = 0;
x_552 = 0;
lean_inc(x_367);
lean_ctor_set(x_518, 3, x_546);
lean_ctor_set(x_518, 2, x_542);
lean_ctor_set(x_518, 1, x_541);
lean_ctor_set(x_518, 0, x_367);
x_553 = !lean_is_exclusive(x_367);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; uint32_t x_561; uint16_t x_562; uint8_t x_563; 
x_554 = lean_ctor_get(x_367, 3);
lean_dec(x_554);
x_555 = lean_ctor_get(x_367, 2);
lean_dec(x_555);
x_556 = lean_ctor_get(x_367, 1);
lean_dec(x_556);
x_557 = lean_ctor_get(x_367, 0);
lean_dec(x_557);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_367, 3, x_59);
lean_ctor_set(x_367, 2, x_58);
lean_ctor_set(x_367, 1, x_57);
lean_ctor_set(x_367, 0, x_549);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_560);
x_561 = 0;
x_562 = 0;
x_563 = 0;
lean_ctor_set(x_366, 3, x_367);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_561);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_562);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_563);
return x_366;
}
else
{
uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; uint32_t x_568; uint16_t x_569; uint8_t x_570; 
lean_dec(x_367);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_518, sizeof(void*)*4, x_550);
lean_ctor_set_uint16(x_518, sizeof(void*)*4 + 4, x_551);
lean_ctor_set_uint8(x_518, sizeof(void*)*4 + 7, x_552);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_567, 0, x_549);
lean_ctor_set(x_567, 1, x_57);
lean_ctor_set(x_567, 2, x_58);
lean_ctor_set(x_567, 3, x_59);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_567, sizeof(void*)*4, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*4 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*4 + 7, x_566);
x_568 = 0;
x_569 = 0;
x_570 = 0;
lean_ctor_set(x_366, 3, x_567);
lean_ctor_set(x_366, 2, x_548);
lean_ctor_set(x_366, 1, x_547);
lean_ctor_set(x_366, 0, x_518);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_568);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_569);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_570);
return x_366;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint32_t x_575; uint16_t x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; uint32_t x_580; uint16_t x_581; uint8_t x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; 
x_571 = lean_ctor_get(x_518, 0);
x_572 = lean_ctor_get(x_518, 1);
x_573 = lean_ctor_get(x_518, 2);
x_574 = lean_ctor_get(x_518, 3);
lean_inc(x_574);
lean_inc(x_573);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_518);
x_575 = 0;
x_576 = 0;
x_577 = 0;
lean_inc(x_367);
x_578 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_578, 0, x_367);
lean_ctor_set(x_578, 1, x_541);
lean_ctor_set(x_578, 2, x_542);
lean_ctor_set(x_578, 3, x_571);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_579 = x_367;
} else {
 lean_dec_ref(x_367);
 x_579 = lean_box(0);
}
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_578, sizeof(void*)*4, x_575);
lean_ctor_set_uint16(x_578, sizeof(void*)*4 + 4, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*4 + 7, x_577);
x_580 = 0;
x_581 = 0;
x_582 = 0;
if (lean_is_scalar(x_579)) {
 x_583 = lean_alloc_ctor(1, 4, 8);
} else {
 x_583 = x_579;
}
lean_ctor_set(x_583, 0, x_574);
lean_ctor_set(x_583, 1, x_57);
lean_ctor_set(x_583, 2, x_58);
lean_ctor_set(x_583, 3, x_59);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_583, sizeof(void*)*4, x_580);
lean_ctor_set_uint16(x_583, sizeof(void*)*4 + 4, x_581);
lean_ctor_set_uint8(x_583, sizeof(void*)*4 + 7, x_582);
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_ctor_set(x_366, 3, x_583);
lean_ctor_set(x_366, 2, x_573);
lean_ctor_set(x_366, 1, x_572);
lean_ctor_set(x_366, 0, x_578);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_586);
return x_366;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint32_t x_594; uint16_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; uint32_t x_603; uint16_t x_604; uint8_t x_605; lean_object* x_606; 
x_587 = lean_ctor_get(x_366, 1);
x_588 = lean_ctor_get(x_366, 2);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_366);
x_589 = lean_ctor_get(x_518, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_518, 1);
lean_inc(x_590);
x_591 = lean_ctor_get(x_518, 2);
lean_inc(x_591);
x_592 = lean_ctor_get(x_518, 3);
lean_inc(x_592);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 lean_ctor_release(x_518, 3);
 x_593 = x_518;
} else {
 lean_dec_ref(x_518);
 x_593 = lean_box(0);
}
x_594 = 0;
x_595 = 0;
x_596 = 0;
lean_inc(x_367);
if (lean_is_scalar(x_593)) {
 x_597 = lean_alloc_ctor(1, 4, 8);
} else {
 x_597 = x_593;
}
lean_ctor_set(x_597, 0, x_367);
lean_ctor_set(x_597, 1, x_587);
lean_ctor_set(x_597, 2, x_588);
lean_ctor_set(x_597, 3, x_589);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_598 = x_367;
} else {
 lean_dec_ref(x_367);
 x_598 = lean_box(0);
}
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_597, sizeof(void*)*4, x_594);
lean_ctor_set_uint16(x_597, sizeof(void*)*4 + 4, x_595);
lean_ctor_set_uint8(x_597, sizeof(void*)*4 + 7, x_596);
x_599 = 0;
x_600 = 0;
x_601 = 0;
if (lean_is_scalar(x_598)) {
 x_602 = lean_alloc_ctor(1, 4, 8);
} else {
 x_602 = x_598;
}
lean_ctor_set(x_602, 0, x_592);
lean_ctor_set(x_602, 1, x_57);
lean_ctor_set(x_602, 2, x_58);
lean_ctor_set(x_602, 3, x_59);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 6, x_466);
lean_ctor_set_uint32(x_602, sizeof(void*)*4, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*4 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*4 + 7, x_601);
x_603 = 0;
x_604 = 0;
x_605 = 0;
x_606 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_606, 0, x_597);
lean_ctor_set(x_606, 1, x_590);
lean_ctor_set(x_606, 2, x_591);
lean_ctor_set(x_606, 3, x_602);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_606, sizeof(void*)*4, x_603);
lean_ctor_set_uint16(x_606, sizeof(void*)*4 + 4, x_604);
lean_ctor_set_uint8(x_606, sizeof(void*)*4 + 7, x_605);
return x_606;
}
}
else
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_366);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_ctor_get(x_366, 3);
lean_dec(x_608);
x_609 = lean_ctor_get(x_366, 0);
lean_dec(x_609);
x_610 = !lean_is_exclusive(x_367);
if (x_610 == 0)
{
uint32_t x_611; uint16_t x_612; uint8_t x_613; uint8_t x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; uint32_t x_618; uint16_t x_619; uint8_t x_620; 
x_611 = 0;
x_612 = 0;
x_613 = 0;
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_367, sizeof(void*)*4, x_611);
lean_ctor_set_uint16(x_367, sizeof(void*)*4 + 4, x_612);
lean_ctor_set_uint8(x_367, sizeof(void*)*4 + 7, x_613);
x_614 = 0;
x_615 = 0;
x_616 = 0;
x_617 = 0;
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_614);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_617);
x_618 = 0;
x_619 = 0;
x_620 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_618);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_619);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_620);
return x_1;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint32_t x_625; uint16_t x_626; uint8_t x_627; lean_object* x_628; uint8_t x_629; uint32_t x_630; uint16_t x_631; uint8_t x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; 
x_621 = lean_ctor_get(x_367, 0);
x_622 = lean_ctor_get(x_367, 1);
x_623 = lean_ctor_get(x_367, 2);
x_624 = lean_ctor_get(x_367, 3);
lean_inc(x_624);
lean_inc(x_623);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_367);
x_625 = 0;
x_626 = 0;
x_627 = 0;
x_628 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_628, 0, x_621);
lean_ctor_set(x_628, 1, x_622);
lean_ctor_set(x_628, 2, x_623);
lean_ctor_set(x_628, 3, x_624);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_628, sizeof(void*)*4, x_625);
lean_ctor_set_uint16(x_628, sizeof(void*)*4 + 4, x_626);
lean_ctor_set_uint8(x_628, sizeof(void*)*4 + 7, x_627);
x_629 = 0;
x_630 = 0;
x_631 = 0;
x_632 = 0;
lean_ctor_set(x_366, 0, x_628);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 6, x_629);
lean_ctor_set_uint32(x_366, sizeof(void*)*4, x_630);
lean_ctor_set_uint16(x_366, sizeof(void*)*4 + 4, x_631);
lean_ctor_set_uint8(x_366, sizeof(void*)*4 + 7, x_632);
x_633 = 0;
x_634 = 0;
x_635 = 0;
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_635);
return x_1;
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; uint32_t x_643; uint16_t x_644; uint8_t x_645; lean_object* x_646; uint8_t x_647; uint32_t x_648; uint16_t x_649; uint8_t x_650; lean_object* x_651; uint32_t x_652; uint16_t x_653; uint8_t x_654; 
x_636 = lean_ctor_get(x_366, 1);
x_637 = lean_ctor_get(x_366, 2);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_366);
x_638 = lean_ctor_get(x_367, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_367, 1);
lean_inc(x_639);
x_640 = lean_ctor_get(x_367, 2);
lean_inc(x_640);
x_641 = lean_ctor_get(x_367, 3);
lean_inc(x_641);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 x_642 = x_367;
} else {
 lean_dec_ref(x_367);
 x_642 = lean_box(0);
}
x_643 = 0;
x_644 = 0;
x_645 = 0;
if (lean_is_scalar(x_642)) {
 x_646 = lean_alloc_ctor(1, 4, 8);
} else {
 x_646 = x_642;
}
lean_ctor_set(x_646, 0, x_638);
lean_ctor_set(x_646, 1, x_639);
lean_ctor_set(x_646, 2, x_640);
lean_ctor_set(x_646, 3, x_641);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_646, sizeof(void*)*4, x_643);
lean_ctor_set_uint16(x_646, sizeof(void*)*4 + 4, x_644);
lean_ctor_set_uint8(x_646, sizeof(void*)*4 + 7, x_645);
x_647 = 0;
x_648 = 0;
x_649 = 0;
x_650 = 0;
x_651 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_651, 0, x_646);
lean_ctor_set(x_651, 1, x_636);
lean_ctor_set(x_651, 2, x_637);
lean_ctor_set(x_651, 3, x_518);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 6, x_647);
lean_ctor_set_uint32(x_651, sizeof(void*)*4, x_648);
lean_ctor_set_uint16(x_651, sizeof(void*)*4 + 4, x_649);
lean_ctor_set_uint8(x_651, sizeof(void*)*4 + 7, x_650);
x_652 = 0;
x_653 = 0;
x_654 = 0;
lean_ctor_set(x_1, 0, x_651);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_539);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_652);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_653);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_654);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint32_t x_659; uint8_t x_660; 
x_655 = lean_ctor_get(x_1, 0);
x_656 = lean_ctor_get(x_1, 1);
x_657 = lean_ctor_get(x_1, 2);
x_658 = lean_ctor_get(x_1, 3);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_1);
x_659 = lean_unbox_uint32(x_656);
x_660 = x_2 < x_659;
if (x_660 == 0)
{
uint32_t x_661; uint8_t x_662; 
x_661 = lean_unbox_uint32(x_656);
x_662 = x_661 < x_2;
if (x_662 == 0)
{
uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_657);
lean_dec(x_656);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_box_uint32(x_2);
x_667 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_667, 0, x_655);
lean_ctor_set(x_667, 1, x_666);
lean_ctor_set(x_667, 2, x_3);
lean_ctor_set(x_667, 3, x_658);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_667, sizeof(void*)*4, x_663);
lean_ctor_set_uint16(x_667, sizeof(void*)*4 + 4, x_664);
lean_ctor_set_uint8(x_667, sizeof(void*)*4 + 7, x_665);
return x_667;
}
else
{
uint8_t x_668; 
x_668 = l_RBNode_isRed___rarg(x_658);
if (x_668 == 0)
{
lean_object* x_669; uint32_t x_670; uint16_t x_671; uint8_t x_672; lean_object* x_673; 
x_669 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_658, x_2, x_3);
x_670 = 0;
x_671 = 0;
x_672 = 0;
x_673 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_673, 0, x_655);
lean_ctor_set(x_673, 1, x_656);
lean_ctor_set(x_673, 2, x_657);
lean_ctor_set(x_673, 3, x_669);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_673, sizeof(void*)*4, x_670);
lean_ctor_set_uint16(x_673, sizeof(void*)*4 + 4, x_671);
lean_ctor_set_uint8(x_673, sizeof(void*)*4 + 7, x_672);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; 
x_674 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_658, x_2, x_3);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; 
x_676 = lean_ctor_get(x_674, 3);
lean_inc(x_676);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; uint32_t x_681; uint16_t x_682; uint8_t x_683; lean_object* x_684; uint8_t x_685; uint32_t x_686; uint16_t x_687; uint8_t x_688; lean_object* x_689; 
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 2);
lean_inc(x_678);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_679 = x_674;
} else {
 lean_dec_ref(x_674);
 x_679 = lean_box(0);
}
x_680 = 0;
x_681 = 0;
x_682 = 0;
x_683 = 0;
if (lean_is_scalar(x_679)) {
 x_684 = lean_alloc_ctor(1, 4, 8);
} else {
 x_684 = x_679;
}
lean_ctor_set(x_684, 0, x_676);
lean_ctor_set(x_684, 1, x_677);
lean_ctor_set(x_684, 2, x_678);
lean_ctor_set(x_684, 3, x_676);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 6, x_680);
lean_ctor_set_uint32(x_684, sizeof(void*)*4, x_681);
lean_ctor_set_uint16(x_684, sizeof(void*)*4 + 4, x_682);
lean_ctor_set_uint8(x_684, sizeof(void*)*4 + 7, x_683);
x_685 = 1;
x_686 = 0;
x_687 = 0;
x_688 = 0;
x_689 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_689, 0, x_655);
lean_ctor_set(x_689, 1, x_656);
lean_ctor_set(x_689, 2, x_657);
lean_ctor_set(x_689, 3, x_684);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 6, x_685);
lean_ctor_set_uint32(x_689, sizeof(void*)*4, x_686);
lean_ctor_set_uint16(x_689, sizeof(void*)*4 + 4, x_687);
lean_ctor_set_uint8(x_689, sizeof(void*)*4 + 7, x_688);
return x_689;
}
else
{
uint8_t x_690; 
x_690 = lean_ctor_get_uint8(x_676, sizeof(void*)*4 + 6);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; uint32_t x_700; uint16_t x_701; uint8_t x_702; lean_object* x_703; uint32_t x_704; uint16_t x_705; uint8_t x_706; lean_object* x_707; uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; 
x_691 = lean_ctor_get(x_674, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_674, 2);
lean_inc(x_692);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_693 = x_674;
} else {
 lean_dec_ref(x_674);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_676, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_676, 1);
lean_inc(x_695);
x_696 = lean_ctor_get(x_676, 2);
lean_inc(x_696);
x_697 = lean_ctor_get(x_676, 3);
lean_inc(x_697);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 lean_ctor_release(x_676, 2);
 lean_ctor_release(x_676, 3);
 x_698 = x_676;
} else {
 lean_dec_ref(x_676);
 x_698 = lean_box(0);
}
x_699 = 1;
x_700 = 0;
x_701 = 0;
x_702 = 0;
if (lean_is_scalar(x_698)) {
 x_703 = lean_alloc_ctor(1, 4, 8);
} else {
 x_703 = x_698;
}
lean_ctor_set(x_703, 0, x_655);
lean_ctor_set(x_703, 1, x_656);
lean_ctor_set(x_703, 2, x_657);
lean_ctor_set(x_703, 3, x_675);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_703, sizeof(void*)*4, x_700);
lean_ctor_set_uint16(x_703, sizeof(void*)*4 + 4, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*4 + 7, x_702);
x_704 = 0;
x_705 = 0;
x_706 = 0;
if (lean_is_scalar(x_693)) {
 x_707 = lean_alloc_ctor(1, 4, 8);
} else {
 x_707 = x_693;
}
lean_ctor_set(x_707, 0, x_694);
lean_ctor_set(x_707, 1, x_695);
lean_ctor_set(x_707, 2, x_696);
lean_ctor_set(x_707, 3, x_697);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 6, x_699);
lean_ctor_set_uint32(x_707, sizeof(void*)*4, x_704);
lean_ctor_set_uint16(x_707, sizeof(void*)*4 + 4, x_705);
lean_ctor_set_uint8(x_707, sizeof(void*)*4 + 7, x_706);
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_711, 0, x_703);
lean_ctor_set(x_711, 1, x_691);
lean_ctor_set(x_711, 2, x_692);
lean_ctor_set(x_711, 3, x_707);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_711, sizeof(void*)*4, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*4 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*4 + 7, x_710);
return x_711;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint32_t x_716; uint16_t x_717; uint8_t x_718; lean_object* x_719; uint32_t x_720; uint16_t x_721; uint8_t x_722; lean_object* x_723; 
x_712 = lean_ctor_get(x_674, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_674, 2);
lean_inc(x_713);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_714 = x_674;
} else {
 lean_dec_ref(x_674);
 x_714 = lean_box(0);
}
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = 0;
if (lean_is_scalar(x_714)) {
 x_719 = lean_alloc_ctor(1, 4, 8);
} else {
 x_719 = x_714;
}
lean_ctor_set(x_719, 0, x_675);
lean_ctor_set(x_719, 1, x_712);
lean_ctor_set(x_719, 2, x_713);
lean_ctor_set(x_719, 3, x_676);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 6, x_715);
lean_ctor_set_uint32(x_719, sizeof(void*)*4, x_716);
lean_ctor_set_uint16(x_719, sizeof(void*)*4 + 4, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*4 + 7, x_718);
x_720 = 0;
x_721 = 0;
x_722 = 0;
x_723 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_723, 0, x_655);
lean_ctor_set(x_723, 1, x_656);
lean_ctor_set(x_723, 2, x_657);
lean_ctor_set(x_723, 3, x_719);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 6, x_690);
lean_ctor_set_uint32(x_723, sizeof(void*)*4, x_720);
lean_ctor_set_uint16(x_723, sizeof(void*)*4 + 4, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*4 + 7, x_722);
return x_723;
}
}
}
else
{
uint8_t x_724; 
x_724 = lean_ctor_get_uint8(x_675, sizeof(void*)*4 + 6);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; uint32_t x_735; uint16_t x_736; uint8_t x_737; lean_object* x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_725 = lean_ctor_get(x_674, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_674, 2);
lean_inc(x_726);
x_727 = lean_ctor_get(x_674, 3);
lean_inc(x_727);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_728 = x_674;
} else {
 lean_dec_ref(x_674);
 x_728 = lean_box(0);
}
x_729 = lean_ctor_get(x_675, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_675, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_675, 2);
lean_inc(x_731);
x_732 = lean_ctor_get(x_675, 3);
lean_inc(x_732);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_733 = x_675;
} else {
 lean_dec_ref(x_675);
 x_733 = lean_box(0);
}
x_734 = 1;
x_735 = 0;
x_736 = 0;
x_737 = 0;
if (lean_is_scalar(x_733)) {
 x_738 = lean_alloc_ctor(1, 4, 8);
} else {
 x_738 = x_733;
}
lean_ctor_set(x_738, 0, x_655);
lean_ctor_set(x_738, 1, x_656);
lean_ctor_set(x_738, 2, x_657);
lean_ctor_set(x_738, 3, x_729);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_738, sizeof(void*)*4, x_735);
lean_ctor_set_uint16(x_738, sizeof(void*)*4 + 4, x_736);
lean_ctor_set_uint8(x_738, sizeof(void*)*4 + 7, x_737);
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_728)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_728;
}
lean_ctor_set(x_742, 0, x_732);
lean_ctor_set(x_742, 1, x_725);
lean_ctor_set(x_742, 2, x_726);
lean_ctor_set(x_742, 3, x_727);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_734);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_738);
lean_ctor_set(x_746, 1, x_730);
lean_ctor_set(x_746, 2, x_731);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
lean_object* x_747; 
x_747 = lean_ctor_get(x_674, 3);
lean_inc(x_747);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; uint32_t x_752; uint16_t x_753; uint8_t x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; 
x_748 = lean_ctor_get(x_674, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_674, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_750 = x_674;
} else {
 lean_dec_ref(x_674);
 x_750 = lean_box(0);
}
x_751 = 0;
x_752 = 0;
x_753 = 0;
x_754 = 0;
if (lean_is_scalar(x_750)) {
 x_755 = lean_alloc_ctor(1, 4, 8);
} else {
 x_755 = x_750;
}
lean_ctor_set(x_755, 0, x_675);
lean_ctor_set(x_755, 1, x_748);
lean_ctor_set(x_755, 2, x_749);
lean_ctor_set(x_755, 3, x_747);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 6, x_751);
lean_ctor_set_uint32(x_755, sizeof(void*)*4, x_752);
lean_ctor_set_uint16(x_755, sizeof(void*)*4 + 4, x_753);
lean_ctor_set_uint8(x_755, sizeof(void*)*4 + 7, x_754);
x_756 = 0;
x_757 = 0;
x_758 = 0;
x_759 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_759, 0, x_655);
lean_ctor_set(x_759, 1, x_656);
lean_ctor_set(x_759, 2, x_657);
lean_ctor_set(x_759, 3, x_755);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
return x_759;
}
else
{
uint8_t x_760; 
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*4 + 6);
if (x_760 == 0)
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; uint32_t x_769; uint16_t x_770; uint8_t x_771; lean_object* x_772; lean_object* x_773; uint32_t x_774; uint16_t x_775; uint8_t x_776; lean_object* x_777; uint32_t x_778; uint16_t x_779; uint8_t x_780; lean_object* x_781; 
x_761 = lean_ctor_get(x_674, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_674, 2);
lean_inc(x_762);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_763 = x_674;
} else {
 lean_dec_ref(x_674);
 x_763 = lean_box(0);
}
x_764 = lean_ctor_get(x_747, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_747, 1);
lean_inc(x_765);
x_766 = lean_ctor_get(x_747, 2);
lean_inc(x_766);
x_767 = lean_ctor_get(x_747, 3);
lean_inc(x_767);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 lean_ctor_release(x_747, 2);
 lean_ctor_release(x_747, 3);
 x_768 = x_747;
} else {
 lean_dec_ref(x_747);
 x_768 = lean_box(0);
}
x_769 = 0;
x_770 = 0;
x_771 = 0;
lean_inc(x_675);
if (lean_is_scalar(x_768)) {
 x_772 = lean_alloc_ctor(1, 4, 8);
} else {
 x_772 = x_768;
}
lean_ctor_set(x_772, 0, x_655);
lean_ctor_set(x_772, 1, x_656);
lean_ctor_set(x_772, 2, x_657);
lean_ctor_set(x_772, 3, x_675);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_773 = x_675;
} else {
 lean_dec_ref(x_675);
 x_773 = lean_box(0);
}
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_772, sizeof(void*)*4, x_769);
lean_ctor_set_uint16(x_772, sizeof(void*)*4 + 4, x_770);
lean_ctor_set_uint8(x_772, sizeof(void*)*4 + 7, x_771);
x_774 = 0;
x_775 = 0;
x_776 = 0;
if (lean_is_scalar(x_773)) {
 x_777 = lean_alloc_ctor(1, 4, 8);
} else {
 x_777 = x_773;
}
lean_ctor_set(x_777, 0, x_764);
lean_ctor_set(x_777, 1, x_765);
lean_ctor_set(x_777, 2, x_766);
lean_ctor_set(x_777, 3, x_767);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 6, x_724);
lean_ctor_set_uint32(x_777, sizeof(void*)*4, x_774);
lean_ctor_set_uint16(x_777, sizeof(void*)*4 + 4, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*4 + 7, x_776);
x_778 = 0;
x_779 = 0;
x_780 = 0;
if (lean_is_scalar(x_763)) {
 x_781 = lean_alloc_ctor(1, 4, 8);
} else {
 x_781 = x_763;
}
lean_ctor_set(x_781, 0, x_772);
lean_ctor_set(x_781, 1, x_761);
lean_ctor_set(x_781, 2, x_762);
lean_ctor_set(x_781, 3, x_777);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_781, sizeof(void*)*4, x_778);
lean_ctor_set_uint16(x_781, sizeof(void*)*4 + 4, x_779);
lean_ctor_set_uint8(x_781, sizeof(void*)*4 + 7, x_780);
return x_781;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; uint32_t x_790; uint16_t x_791; uint8_t x_792; lean_object* x_793; uint8_t x_794; uint32_t x_795; uint16_t x_796; uint8_t x_797; lean_object* x_798; uint32_t x_799; uint16_t x_800; uint8_t x_801; lean_object* x_802; 
x_782 = lean_ctor_get(x_674, 1);
lean_inc(x_782);
x_783 = lean_ctor_get(x_674, 2);
lean_inc(x_783);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 lean_ctor_release(x_674, 2);
 lean_ctor_release(x_674, 3);
 x_784 = x_674;
} else {
 lean_dec_ref(x_674);
 x_784 = lean_box(0);
}
x_785 = lean_ctor_get(x_675, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_675, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_675, 2);
lean_inc(x_787);
x_788 = lean_ctor_get(x_675, 3);
lean_inc(x_788);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 lean_ctor_release(x_675, 2);
 lean_ctor_release(x_675, 3);
 x_789 = x_675;
} else {
 lean_dec_ref(x_675);
 x_789 = lean_box(0);
}
x_790 = 0;
x_791 = 0;
x_792 = 0;
if (lean_is_scalar(x_789)) {
 x_793 = lean_alloc_ctor(1, 4, 8);
} else {
 x_793 = x_789;
}
lean_ctor_set(x_793, 0, x_785);
lean_ctor_set(x_793, 1, x_786);
lean_ctor_set(x_793, 2, x_787);
lean_ctor_set(x_793, 3, x_788);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_793, sizeof(void*)*4, x_790);
lean_ctor_set_uint16(x_793, sizeof(void*)*4 + 4, x_791);
lean_ctor_set_uint8(x_793, sizeof(void*)*4 + 7, x_792);
x_794 = 0;
x_795 = 0;
x_796 = 0;
x_797 = 0;
if (lean_is_scalar(x_784)) {
 x_798 = lean_alloc_ctor(1, 4, 8);
} else {
 x_798 = x_784;
}
lean_ctor_set(x_798, 0, x_793);
lean_ctor_set(x_798, 1, x_782);
lean_ctor_set(x_798, 2, x_783);
lean_ctor_set(x_798, 3, x_747);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 6, x_794);
lean_ctor_set_uint32(x_798, sizeof(void*)*4, x_795);
lean_ctor_set_uint16(x_798, sizeof(void*)*4 + 4, x_796);
lean_ctor_set_uint8(x_798, sizeof(void*)*4 + 7, x_797);
x_799 = 0;
x_800 = 0;
x_801 = 0;
x_802 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_802, 0, x_655);
lean_ctor_set(x_802, 1, x_656);
lean_ctor_set(x_802, 2, x_657);
lean_ctor_set(x_802, 3, x_798);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 6, x_760);
lean_ctor_set_uint32(x_802, sizeof(void*)*4, x_799);
lean_ctor_set_uint16(x_802, sizeof(void*)*4 + 4, x_800);
lean_ctor_set_uint8(x_802, sizeof(void*)*4 + 7, x_801);
return x_802;
}
}
}
}
}
}
}
else
{
uint8_t x_803; 
x_803 = l_RBNode_isRed___rarg(x_655);
if (x_803 == 0)
{
lean_object* x_804; uint32_t x_805; uint16_t x_806; uint8_t x_807; lean_object* x_808; 
x_804 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_655, x_2, x_3);
x_805 = 0;
x_806 = 0;
x_807 = 0;
x_808 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_808, 0, x_804);
lean_ctor_set(x_808, 1, x_656);
lean_ctor_set(x_808, 2, x_657);
lean_ctor_set(x_808, 3, x_658);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 6, x_10);
lean_ctor_set_uint32(x_808, sizeof(void*)*4, x_805);
lean_ctor_set_uint16(x_808, sizeof(void*)*4 + 4, x_806);
lean_ctor_set_uint8(x_808, sizeof(void*)*4 + 7, x_807);
return x_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_655, x_2, x_3);
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_809, 3);
lean_inc(x_811);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; uint32_t x_816; uint16_t x_817; uint8_t x_818; lean_object* x_819; uint8_t x_820; uint32_t x_821; uint16_t x_822; uint8_t x_823; lean_object* x_824; 
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
x_813 = lean_ctor_get(x_809, 2);
lean_inc(x_813);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_814 = x_809;
} else {
 lean_dec_ref(x_809);
 x_814 = lean_box(0);
}
x_815 = 0;
x_816 = 0;
x_817 = 0;
x_818 = 0;
if (lean_is_scalar(x_814)) {
 x_819 = lean_alloc_ctor(1, 4, 8);
} else {
 x_819 = x_814;
}
lean_ctor_set(x_819, 0, x_811);
lean_ctor_set(x_819, 1, x_812);
lean_ctor_set(x_819, 2, x_813);
lean_ctor_set(x_819, 3, x_811);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 6, x_815);
lean_ctor_set_uint32(x_819, sizeof(void*)*4, x_816);
lean_ctor_set_uint16(x_819, sizeof(void*)*4 + 4, x_817);
lean_ctor_set_uint8(x_819, sizeof(void*)*4 + 7, x_818);
x_820 = 1;
x_821 = 0;
x_822 = 0;
x_823 = 0;
x_824 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_824, 0, x_819);
lean_ctor_set(x_824, 1, x_656);
lean_ctor_set(x_824, 2, x_657);
lean_ctor_set(x_824, 3, x_658);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 6, x_820);
lean_ctor_set_uint32(x_824, sizeof(void*)*4, x_821);
lean_ctor_set_uint16(x_824, sizeof(void*)*4 + 4, x_822);
lean_ctor_set_uint8(x_824, sizeof(void*)*4 + 7, x_823);
return x_824;
}
else
{
uint8_t x_825; 
x_825 = lean_ctor_get_uint8(x_811, sizeof(void*)*4 + 6);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; uint32_t x_835; uint16_t x_836; uint8_t x_837; lean_object* x_838; uint32_t x_839; uint16_t x_840; uint8_t x_841; lean_object* x_842; uint32_t x_843; uint16_t x_844; uint8_t x_845; lean_object* x_846; 
x_826 = lean_ctor_get(x_809, 1);
lean_inc(x_826);
x_827 = lean_ctor_get(x_809, 2);
lean_inc(x_827);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_828 = x_809;
} else {
 lean_dec_ref(x_809);
 x_828 = lean_box(0);
}
x_829 = lean_ctor_get(x_811, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_811, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_811, 2);
lean_inc(x_831);
x_832 = lean_ctor_get(x_811, 3);
lean_inc(x_832);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 lean_ctor_release(x_811, 2);
 lean_ctor_release(x_811, 3);
 x_833 = x_811;
} else {
 lean_dec_ref(x_811);
 x_833 = lean_box(0);
}
x_834 = 1;
x_835 = 0;
x_836 = 0;
x_837 = 0;
if (lean_is_scalar(x_833)) {
 x_838 = lean_alloc_ctor(1, 4, 8);
} else {
 x_838 = x_833;
}
lean_ctor_set(x_838, 0, x_810);
lean_ctor_set(x_838, 1, x_826);
lean_ctor_set(x_838, 2, x_827);
lean_ctor_set(x_838, 3, x_829);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_838, sizeof(void*)*4, x_835);
lean_ctor_set_uint16(x_838, sizeof(void*)*4 + 4, x_836);
lean_ctor_set_uint8(x_838, sizeof(void*)*4 + 7, x_837);
x_839 = 0;
x_840 = 0;
x_841 = 0;
if (lean_is_scalar(x_828)) {
 x_842 = lean_alloc_ctor(1, 4, 8);
} else {
 x_842 = x_828;
}
lean_ctor_set(x_842, 0, x_832);
lean_ctor_set(x_842, 1, x_656);
lean_ctor_set(x_842, 2, x_657);
lean_ctor_set(x_842, 3, x_658);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 6, x_834);
lean_ctor_set_uint32(x_842, sizeof(void*)*4, x_839);
lean_ctor_set_uint16(x_842, sizeof(void*)*4 + 4, x_840);
lean_ctor_set_uint8(x_842, sizeof(void*)*4 + 7, x_841);
x_843 = 0;
x_844 = 0;
x_845 = 0;
x_846 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_846, 0, x_838);
lean_ctor_set(x_846, 1, x_830);
lean_ctor_set(x_846, 2, x_831);
lean_ctor_set(x_846, 3, x_842);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_846, sizeof(void*)*4, x_843);
lean_ctor_set_uint16(x_846, sizeof(void*)*4 + 4, x_844);
lean_ctor_set_uint8(x_846, sizeof(void*)*4 + 7, x_845);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; uint32_t x_851; uint16_t x_852; uint8_t x_853; lean_object* x_854; uint32_t x_855; uint16_t x_856; uint8_t x_857; lean_object* x_858; 
x_847 = lean_ctor_get(x_809, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_809, 2);
lean_inc(x_848);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_849 = x_809;
} else {
 lean_dec_ref(x_809);
 x_849 = lean_box(0);
}
x_850 = 0;
x_851 = 0;
x_852 = 0;
x_853 = 0;
if (lean_is_scalar(x_849)) {
 x_854 = lean_alloc_ctor(1, 4, 8);
} else {
 x_854 = x_849;
}
lean_ctor_set(x_854, 0, x_810);
lean_ctor_set(x_854, 1, x_847);
lean_ctor_set(x_854, 2, x_848);
lean_ctor_set(x_854, 3, x_811);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 6, x_850);
lean_ctor_set_uint32(x_854, sizeof(void*)*4, x_851);
lean_ctor_set_uint16(x_854, sizeof(void*)*4 + 4, x_852);
lean_ctor_set_uint8(x_854, sizeof(void*)*4 + 7, x_853);
x_855 = 0;
x_856 = 0;
x_857 = 0;
x_858 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_858, 0, x_854);
lean_ctor_set(x_858, 1, x_656);
lean_ctor_set(x_858, 2, x_657);
lean_ctor_set(x_858, 3, x_658);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 6, x_825);
lean_ctor_set_uint32(x_858, sizeof(void*)*4, x_855);
lean_ctor_set_uint16(x_858, sizeof(void*)*4 + 4, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*4 + 7, x_857);
return x_858;
}
}
}
else
{
uint8_t x_859; 
x_859 = lean_ctor_get_uint8(x_810, sizeof(void*)*4 + 6);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; uint32_t x_870; uint16_t x_871; uint8_t x_872; lean_object* x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_860 = lean_ctor_get(x_809, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_809, 2);
lean_inc(x_861);
x_862 = lean_ctor_get(x_809, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_863 = x_809;
} else {
 lean_dec_ref(x_809);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_810, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_810, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_810, 2);
lean_inc(x_866);
x_867 = lean_ctor_get(x_810, 3);
lean_inc(x_867);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_868 = x_810;
} else {
 lean_dec_ref(x_810);
 x_868 = lean_box(0);
}
x_869 = 1;
x_870 = 0;
x_871 = 0;
x_872 = 0;
if (lean_is_scalar(x_868)) {
 x_873 = lean_alloc_ctor(1, 4, 8);
} else {
 x_873 = x_868;
}
lean_ctor_set(x_873, 0, x_864);
lean_ctor_set(x_873, 1, x_865);
lean_ctor_set(x_873, 2, x_866);
lean_ctor_set(x_873, 3, x_867);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_873, sizeof(void*)*4, x_870);
lean_ctor_set_uint16(x_873, sizeof(void*)*4 + 4, x_871);
lean_ctor_set_uint8(x_873, sizeof(void*)*4 + 7, x_872);
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_863)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_863;
}
lean_ctor_set(x_877, 0, x_862);
lean_ctor_set(x_877, 1, x_656);
lean_ctor_set(x_877, 2, x_657);
lean_ctor_set(x_877, 3, x_658);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_869);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_873);
lean_ctor_set(x_881, 1, x_860);
lean_ctor_set(x_881, 2, x_861);
lean_ctor_set(x_881, 3, x_877);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
lean_object* x_882; 
x_882 = lean_ctor_get(x_809, 3);
lean_inc(x_882);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; uint8_t x_886; uint32_t x_887; uint16_t x_888; uint8_t x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; 
x_883 = lean_ctor_get(x_809, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_809, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_885 = x_809;
} else {
 lean_dec_ref(x_809);
 x_885 = lean_box(0);
}
x_886 = 0;
x_887 = 0;
x_888 = 0;
x_889 = 0;
if (lean_is_scalar(x_885)) {
 x_890 = lean_alloc_ctor(1, 4, 8);
} else {
 x_890 = x_885;
}
lean_ctor_set(x_890, 0, x_810);
lean_ctor_set(x_890, 1, x_883);
lean_ctor_set(x_890, 2, x_884);
lean_ctor_set(x_890, 3, x_882);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 6, x_886);
lean_ctor_set_uint32(x_890, sizeof(void*)*4, x_887);
lean_ctor_set_uint16(x_890, sizeof(void*)*4 + 4, x_888);
lean_ctor_set_uint8(x_890, sizeof(void*)*4 + 7, x_889);
x_891 = 0;
x_892 = 0;
x_893 = 0;
x_894 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_894, 0, x_890);
lean_ctor_set(x_894, 1, x_656);
lean_ctor_set(x_894, 2, x_657);
lean_ctor_set(x_894, 3, x_658);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
return x_894;
}
else
{
uint8_t x_895; 
x_895 = lean_ctor_get_uint8(x_882, sizeof(void*)*4 + 6);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint32_t x_904; uint16_t x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; uint32_t x_909; uint16_t x_910; uint8_t x_911; lean_object* x_912; uint32_t x_913; uint16_t x_914; uint8_t x_915; lean_object* x_916; 
x_896 = lean_ctor_get(x_809, 1);
lean_inc(x_896);
x_897 = lean_ctor_get(x_809, 2);
lean_inc(x_897);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_898 = x_809;
} else {
 lean_dec_ref(x_809);
 x_898 = lean_box(0);
}
x_899 = lean_ctor_get(x_882, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_882, 1);
lean_inc(x_900);
x_901 = lean_ctor_get(x_882, 2);
lean_inc(x_901);
x_902 = lean_ctor_get(x_882, 3);
lean_inc(x_902);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 lean_ctor_release(x_882, 2);
 lean_ctor_release(x_882, 3);
 x_903 = x_882;
} else {
 lean_dec_ref(x_882);
 x_903 = lean_box(0);
}
x_904 = 0;
x_905 = 0;
x_906 = 0;
lean_inc(x_810);
if (lean_is_scalar(x_903)) {
 x_907 = lean_alloc_ctor(1, 4, 8);
} else {
 x_907 = x_903;
}
lean_ctor_set(x_907, 0, x_810);
lean_ctor_set(x_907, 1, x_896);
lean_ctor_set(x_907, 2, x_897);
lean_ctor_set(x_907, 3, x_899);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_908 = x_810;
} else {
 lean_dec_ref(x_810);
 x_908 = lean_box(0);
}
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_907, sizeof(void*)*4, x_904);
lean_ctor_set_uint16(x_907, sizeof(void*)*4 + 4, x_905);
lean_ctor_set_uint8(x_907, sizeof(void*)*4 + 7, x_906);
x_909 = 0;
x_910 = 0;
x_911 = 0;
if (lean_is_scalar(x_908)) {
 x_912 = lean_alloc_ctor(1, 4, 8);
} else {
 x_912 = x_908;
}
lean_ctor_set(x_912, 0, x_902);
lean_ctor_set(x_912, 1, x_656);
lean_ctor_set(x_912, 2, x_657);
lean_ctor_set(x_912, 3, x_658);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 6, x_859);
lean_ctor_set_uint32(x_912, sizeof(void*)*4, x_909);
lean_ctor_set_uint16(x_912, sizeof(void*)*4 + 4, x_910);
lean_ctor_set_uint8(x_912, sizeof(void*)*4 + 7, x_911);
x_913 = 0;
x_914 = 0;
x_915 = 0;
if (lean_is_scalar(x_898)) {
 x_916 = lean_alloc_ctor(1, 4, 8);
} else {
 x_916 = x_898;
}
lean_ctor_set(x_916, 0, x_907);
lean_ctor_set(x_916, 1, x_900);
lean_ctor_set(x_916, 2, x_901);
lean_ctor_set(x_916, 3, x_912);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_916, sizeof(void*)*4, x_913);
lean_ctor_set_uint16(x_916, sizeof(void*)*4 + 4, x_914);
lean_ctor_set_uint8(x_916, sizeof(void*)*4 + 7, x_915);
return x_916;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint32_t x_925; uint16_t x_926; uint8_t x_927; lean_object* x_928; uint8_t x_929; uint32_t x_930; uint16_t x_931; uint8_t x_932; lean_object* x_933; uint32_t x_934; uint16_t x_935; uint8_t x_936; lean_object* x_937; 
x_917 = lean_ctor_get(x_809, 1);
lean_inc(x_917);
x_918 = lean_ctor_get(x_809, 2);
lean_inc(x_918);
if (lean_is_exclusive(x_809)) {
 lean_ctor_release(x_809, 0);
 lean_ctor_release(x_809, 1);
 lean_ctor_release(x_809, 2);
 lean_ctor_release(x_809, 3);
 x_919 = x_809;
} else {
 lean_dec_ref(x_809);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_810, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_810, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_810, 2);
lean_inc(x_922);
x_923 = lean_ctor_get(x_810, 3);
lean_inc(x_923);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 lean_ctor_release(x_810, 2);
 lean_ctor_release(x_810, 3);
 x_924 = x_810;
} else {
 lean_dec_ref(x_810);
 x_924 = lean_box(0);
}
x_925 = 0;
x_926 = 0;
x_927 = 0;
if (lean_is_scalar(x_924)) {
 x_928 = lean_alloc_ctor(1, 4, 8);
} else {
 x_928 = x_924;
}
lean_ctor_set(x_928, 0, x_920);
lean_ctor_set(x_928, 1, x_921);
lean_ctor_set(x_928, 2, x_922);
lean_ctor_set(x_928, 3, x_923);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_928, sizeof(void*)*4, x_925);
lean_ctor_set_uint16(x_928, sizeof(void*)*4 + 4, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*4 + 7, x_927);
x_929 = 0;
x_930 = 0;
x_931 = 0;
x_932 = 0;
if (lean_is_scalar(x_919)) {
 x_933 = lean_alloc_ctor(1, 4, 8);
} else {
 x_933 = x_919;
}
lean_ctor_set(x_933, 0, x_928);
lean_ctor_set(x_933, 1, x_917);
lean_ctor_set(x_933, 2, x_918);
lean_ctor_set(x_933, 3, x_882);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 6, x_929);
lean_ctor_set_uint32(x_933, sizeof(void*)*4, x_930);
lean_ctor_set_uint16(x_933, sizeof(void*)*4 + 4, x_931);
lean_ctor_set_uint8(x_933, sizeof(void*)*4 + 7, x_932);
x_934 = 0;
x_935 = 0;
x_936 = 0;
x_937 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_937, 0, x_933);
lean_ctor_set(x_937, 1, x_656);
lean_ctor_set(x_937, 2, x_657);
lean_ctor_set(x_937, 3, x_658);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 6, x_895);
lean_ctor_set_uint32(x_937, sizeof(void*)*4, x_934);
lean_ctor_set_uint16(x_937, sizeof(void*)*4 + 4, x_935);
lean_ctor_set_uint8(x_937, sizeof(void*)*4 + 7, x_936);
return x_937;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_string_utf8_at_end(x_1, x_4);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_string_utf8_get(x_1, x_4);
x_10 = lean_string_utf8_next(x_1, x_4);
lean_inc(x_7);
x_11 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg(x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_10);
lean_dec(x_10);
x_13 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg(x_7, x_9, x_12);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(x_1, x_2, x_14, x_10);
lean_dec(x_10);
x_16 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg(x_7, x_9, x_15);
lean_ctor_set(x_3, 1, x_16);
return x_3;
}
}
else
{
lean_object* x_17; 
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_string_utf8_at_end(x_1, x_4);
if (x_20 == 0)
{
uint32_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_utf8_get(x_1, x_4);
x_22 = lean_string_utf8_next(x_1, x_4);
lean_inc(x_19);
x_23 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg(x_19, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l___private_Init_Lean_Data_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_22);
lean_dec(x_22);
x_25 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg(x_19, x_21, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(x_1, x_2, x_27, x_22);
lean_dec(x_22);
x_29 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg(x_19, x_21, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
return x_32;
}
}
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_insert___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__5___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_2__insertAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_2__insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_2__insertAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_Trie_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Lean_Data_Trie_2__insertAux___main___rarg(x_2, x_3, x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Parser_Trie_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Trie_insert___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_insert___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Trie_insert___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_string_utf8_at_end(x_1, x_3);
if (x_6 == 0)
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_string_utf8_get(x_1, x_3);
x_8 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_9 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg(x_5, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_2 = x_11;
x_3 = x_8;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_3__findAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_3__findAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_3__findAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_3__findAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_3__findAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_3__findAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_3__findAux___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_Trie_find___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Lean_Data_Trie_3__findAux___main___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Parser_Trie_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Trie_find___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_find___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Parser_Trie_find___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_4__updtAcc___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_4__updtAcc___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Data_Trie_4__updtAcc___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unbox_uint32(x_5);
x_9 = x_2 < x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
lean_dec(x_4);
x_10 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_11 = x_10 < x_2;
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_string_utf8_at_end(x_1, x_3);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_8 = l___private_Init_Lean_Data_Trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean_dec(x_4);
x_9 = lean_string_utf8_get(x_1, x_3);
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_11 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg(x_6, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
return x_8;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_2 = x_12;
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l___private_Init_Lean_Data_Trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean_dec(x_4);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Data_Trie_5__matchPrefixAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Init_Lean_Data_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_Trie_matchPrefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Trie_matchPrefix___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Trie_matchPrefix___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint32_t x_8; uint16_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint16_t x_14; uint8_t x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 0;
x_8 = 0;
x_9 = 0;
x_10 = 0;
lean_inc(x_2);
lean_inc(x_6);
x_11 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*2 + 6, x_7);
lean_ctor_set_uint32(x_11, sizeof(void*)*2, x_8);
lean_ctor_set_uint16(x_11, sizeof(void*)*2 + 4, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2 + 7, x_10);
x_12 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_4, x_2);
x_13 = 0;
x_14 = 0;
x_15 = 0;
x_16 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 6, x_7);
lean_ctor_set_uint32(x_16, sizeof(void*)*2, x_13);
lean_ctor_set_uint16(x_16, sizeof(void*)*2 + 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 7, x_15);
return x_16;
}
}
}
}
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2___rarg(x_1, x_3);
x_8 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_11, x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg(x_5);
x_15 = lean_box(1);
x_16 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_14, x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_format_group(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_1 = x_21;
x_2 = x_6;
goto _start;
}
}
}
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = l_RBNode_fold___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__2___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Data_Trie_6__toStringAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Data_Trie_6__toStringAux___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Init_Lean_Data_Trie_6__toStringAux___main___rarg(x_1);
x_3 = lean_box(1);
x_4 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Options_empty;
x_6 = l_Lean_Format_pretty(x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Parser_Trie_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_Trie_HasToString___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_RBMap(lean_object*);
lean_object* initialize_Init_Lean_Data_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_Trie(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Trie_empty___closed__1 = _init_l_Lean_Parser_Trie_empty___closed__1();
lean_mark_persistent(l_Lean_Parser_Trie_empty___closed__1);
l_Lean_Parser_Trie_HasEmptyc___closed__1 = _init_l_Lean_Parser_Trie_HasEmptyc___closed__1();
lean_mark_persistent(l_Lean_Parser_Trie_HasEmptyc___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
