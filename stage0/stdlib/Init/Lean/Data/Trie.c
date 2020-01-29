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
uint8_t l_coeDecidableEq(uint8_t);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; 
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
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_4);
x_11 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_12 = x_11 < x_2;
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box_uint32(x_2);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_unbox_uint32(x_10);
x_17 = x_16 < x_2;
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; 
x_20 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_20);
return x_1;
}
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = lean_unbox_uint32(x_23);
x_27 = x_2 < x_26;
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = lean_unbox_uint32(x_23);
x_30 = x_29 < x_2;
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_box_uint32(x_2);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_25, x_2, x_3);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_22, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_unbox_uint32(x_40);
x_44 = x_2 < x_43;
x_45 = l_coeDecidableEq(x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_unbox_uint32(x_40);
x_47 = x_46 < x_2;
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_40);
x_49 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_49);
return x_1;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_RBNode_isRed___rarg(x_42);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_42, x_2, x_3);
lean_ctor_set(x_1, 3, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_42, x_2, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = 0;
lean_ctor_set(x_53, 0, x_55);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_59);
x_60 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_53, 1);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = 1;
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_53, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
x_75 = lean_ctor_get(x_55, 2);
x_76 = lean_ctor_get(x_55, 3);
x_77 = 1;
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_77);
lean_ctor_set(x_53, 3, x_76);
lean_ctor_set(x_53, 2, x_75);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_73);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_77);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_55, 0);
x_79 = lean_ctor_get(x_55, 1);
x_80 = lean_ctor_get(x_55, 2);
x_81 = lean_ctor_get(x_55, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_55);
x_82 = 1;
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_40);
lean_ctor_set(x_83, 2, x_41);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
lean_ctor_set(x_53, 3, x_81);
lean_ctor_set(x_53, 2, x_80);
lean_ctor_set(x_53, 1, x_79);
lean_ctor_set(x_53, 0, x_78);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_82);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_53, 1);
x_85 = lean_ctor_get(x_53, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_ctor_get(x_55, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_55, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_55, 3);
lean_inc(x_89);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_90 = x_55;
} else {
 lean_dec_ref(x_55);
 x_90 = lean_box(0);
}
x_91 = 1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(1, 4, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_39);
lean_ctor_set(x_92, 1, x_40);
lean_ctor_set(x_92, 2, x_41);
lean_ctor_set(x_92, 3, x_54);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_91);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_85);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_92);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_53, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_53, 0);
lean_dec(x_96);
x_97 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_97);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_53, 1);
x_99 = lean_ctor_get(x_53, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_53);
x_100 = 0;
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_55);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_101);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
}
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_53);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_53, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_54);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_54, 0);
x_107 = lean_ctor_get(x_54, 1);
x_108 = lean_ctor_get(x_54, 2);
x_109 = lean_ctor_get(x_54, 3);
x_110 = 1;
lean_ctor_set(x_54, 3, x_106);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_110);
lean_ctor_set(x_53, 0, x_109);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_110);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_108);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_54, 0);
x_112 = lean_ctor_get(x_54, 1);
x_113 = lean_ctor_get(x_54, 2);
x_114 = lean_ctor_get(x_54, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_54);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_39);
lean_ctor_set(x_116, 1, x_40);
lean_ctor_set(x_116, 2, x_41);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
lean_ctor_set(x_53, 0, x_114);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_53, 1);
x_118 = lean_ctor_get(x_53, 2);
x_119 = lean_ctor_get(x_53, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_53);
x_120 = lean_ctor_get(x_54, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_54, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_54, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_54, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_124 = x_54;
} else {
 lean_dec_ref(x_54);
 x_124 = lean_box(0);
}
x_125 = 1;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 4, 1);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_40);
lean_ctor_set(x_126, 2, x_41);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_117);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_127);
lean_ctor_set(x_1, 2, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_53, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_53);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_53, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_53, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_132);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_53, 1);
x_134 = lean_ctor_get(x_53, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_53);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_54);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_128);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_137 == 0)
{
uint8_t x_138; 
lean_free_object(x_1);
x_138 = !lean_is_exclusive(x_53);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_53, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_53, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_128);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
x_144 = lean_ctor_get(x_128, 2);
x_145 = lean_ctor_get(x_128, 3);
lean_inc(x_54);
lean_ctor_set(x_128, 3, x_54);
lean_ctor_set(x_128, 2, x_41);
lean_ctor_set(x_128, 1, x_40);
lean_ctor_set(x_128, 0, x_39);
x_146 = !lean_is_exclusive(x_54);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_54, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_54, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_54, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_54, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
lean_ctor_set(x_54, 3, x_145);
lean_ctor_set(x_54, 2, x_144);
lean_ctor_set(x_54, 1, x_143);
lean_ctor_set(x_54, 0, x_142);
lean_ctor_set(x_53, 3, x_54);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
else
{
lean_object* x_151; 
lean_dec(x_54);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_145);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_151);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_128, 0);
x_153 = lean_ctor_get(x_128, 1);
x_154 = lean_ctor_get(x_128, 2);
x_155 = lean_ctor_get(x_128, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_128);
lean_inc(x_54);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_39);
lean_ctor_set(x_156, 1, x_40);
lean_ctor_set(x_156, 2, x_41);
lean_ctor_set(x_156, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_157 = x_54;
} else {
 lean_dec_ref(x_54);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_154);
lean_ctor_set(x_158, 3, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_158);
lean_ctor_set(x_53, 0, x_156);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_53, 1);
x_160 = lean_ctor_get(x_53, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_53);
x_161 = lean_ctor_get(x_128, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_128, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_128, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_128, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_165 = x_128;
} else {
 lean_dec_ref(x_128);
 x_165 = lean_box(0);
}
lean_inc(x_54);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_39);
lean_ctor_set(x_166, 1, x_40);
lean_ctor_set(x_166, 2, x_41);
lean_ctor_set(x_166, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_167 = x_54;
} else {
 lean_dec_ref(x_54);
 x_167 = lean_box(0);
}
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_102);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_169, 2, x_160);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_137);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_53);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_53, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_53, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_54);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_137);
x_174 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_174);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_54, 0);
x_176 = lean_ctor_get(x_54, 1);
x_177 = lean_ctor_get(x_54, 2);
x_178 = lean_ctor_get(x_54, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_54);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_137);
x_180 = 0;
lean_ctor_set(x_53, 0, x_179);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_180);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_53, 1);
x_182 = lean_ctor_get(x_53, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_53);
x_183 = lean_ctor_get(x_54, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_54, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_54, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_54, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_187 = x_54;
} else {
 lean_dec_ref(x_54);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_137);
x_189 = 0;
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_128);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_189);
lean_ctor_set(x_1, 3, x_190);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
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
uint8_t x_191; uint8_t x_192; 
x_191 = l_RBNode_isRed___rarg(x_39);
x_192 = l_coeDecidableEq(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_39, x_2, x_3);
lean_ctor_set(x_1, 0, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_39, x_2, x_3);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_194, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_194, 0);
lean_dec(x_199);
x_200 = 0;
lean_ctor_set(x_194, 0, x_196);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_200);
x_201 = 1;
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_194, 1);
x_203 = lean_ctor_get(x_194, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_194);
x_204 = 0;
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_196);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_204);
x_206 = 1;
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_206);
return x_1;
}
}
else
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_194, 1);
x_210 = lean_ctor_get(x_194, 2);
x_211 = lean_ctor_get(x_194, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_194, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_196);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_196, 0);
x_215 = lean_ctor_get(x_196, 1);
x_216 = lean_ctor_get(x_196, 2);
x_217 = lean_ctor_get(x_196, 3);
x_218 = 1;
lean_ctor_set(x_196, 3, x_214);
lean_ctor_set(x_196, 2, x_210);
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_218);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_217);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_218);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_216);
lean_ctor_set(x_1, 1, x_215);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_196, 0);
x_220 = lean_ctor_get(x_196, 1);
x_221 = lean_ctor_get(x_196, 2);
x_222 = lean_ctor_get(x_196, 3);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_196);
x_223 = 1;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_195);
lean_ctor_set(x_224, 1, x_209);
lean_ctor_set(x_224, 2, x_210);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_222);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_194, 1);
x_226 = lean_ctor_get(x_194, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_194);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_40);
lean_ctor_set(x_234, 2, x_41);
lean_ctor_set(x_234, 3, x_42);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_194);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_194, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 0);
lean_dec(x_237);
x_238 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_238);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_194, 1);
x_240 = lean_ctor_get(x_194, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_194);
x_241 = 0;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_195);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_196);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_194);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_194, 1);
x_246 = lean_ctor_get(x_194, 2);
x_247 = lean_ctor_get(x_194, 3);
x_248 = lean_ctor_get(x_194, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_195);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_250);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_250);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_195, 0);
x_252 = lean_ctor_get(x_195, 1);
x_253 = lean_ctor_get(x_195, 2);
x_254 = lean_ctor_get(x_195, 3);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_195);
x_255 = 1;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_257 = lean_ctor_get(x_194, 1);
x_258 = lean_ctor_get(x_194, 2);
x_259 = lean_ctor_get(x_194, 3);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_194);
x_260 = lean_ctor_get(x_195, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_195, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_195, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_195, 3);
lean_inc(x_263);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_264 = x_195;
} else {
 lean_dec_ref(x_195);
 x_264 = lean_box(0);
}
x_265 = 1;
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(1, 4, 1);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_261);
lean_ctor_set(x_266, 2, x_262);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
x_267 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_40);
lean_ctor_set(x_267, 2, x_41);
lean_ctor_set(x_267, 3, x_42);
lean_ctor_set_uint8(x_267, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 3, x_267);
lean_ctor_set(x_1, 2, x_258);
lean_ctor_set(x_1, 1, x_257);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_194, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_194);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_194, 3);
lean_dec(x_270);
x_271 = lean_ctor_get(x_194, 0);
lean_dec(x_271);
x_272 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_272);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_194, 1);
x_274 = lean_ctor_get(x_194, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_194);
x_275 = 0;
x_276 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_276, 0, x_195);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_274);
lean_ctor_set(x_276, 3, x_268);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_276);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
uint8_t x_277; 
x_277 = lean_ctor_get_uint8(x_268, sizeof(void*)*4);
if (x_277 == 0)
{
uint8_t x_278; 
lean_free_object(x_1);
x_278 = !lean_is_exclusive(x_194);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_194, 1);
x_280 = lean_ctor_get(x_194, 2);
x_281 = lean_ctor_get(x_194, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_194, 0);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_268);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_268, 0);
x_285 = lean_ctor_get(x_268, 1);
x_286 = lean_ctor_get(x_268, 2);
x_287 = lean_ctor_get(x_268, 3);
lean_inc(x_195);
lean_ctor_set(x_268, 3, x_284);
lean_ctor_set(x_268, 2, x_280);
lean_ctor_set(x_268, 1, x_279);
lean_ctor_set(x_268, 0, x_195);
x_288 = !lean_is_exclusive(x_195);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_195, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_195, 2);
lean_dec(x_290);
x_291 = lean_ctor_get(x_195, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_195, 0);
lean_dec(x_292);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
lean_ctor_set(x_195, 3, x_42);
lean_ctor_set(x_195, 2, x_41);
lean_ctor_set(x_195, 1, x_40);
lean_ctor_set(x_195, 0, x_287);
lean_ctor_set(x_194, 3, x_195);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
else
{
lean_object* x_293; 
lean_dec(x_195);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_40);
lean_ctor_set(x_293, 2, x_41);
lean_ctor_set(x_293, 3, x_42);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_293);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_268, 0);
x_295 = lean_ctor_get(x_268, 1);
x_296 = lean_ctor_get(x_268, 2);
x_297 = lean_ctor_get(x_268, 3);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_268);
lean_inc(x_195);
x_298 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_298, 0, x_195);
lean_ctor_set(x_298, 1, x_279);
lean_ctor_set(x_298, 2, x_280);
lean_ctor_set(x_298, 3, x_294);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_299 = x_195;
} else {
 lean_dec_ref(x_195);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_40);
lean_ctor_set(x_300, 2, x_41);
lean_ctor_set(x_300, 3, x_42);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_300);
lean_ctor_set(x_194, 2, x_296);
lean_ctor_set(x_194, 1, x_295);
lean_ctor_set(x_194, 0, x_298);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = lean_ctor_get(x_194, 1);
x_302 = lean_ctor_get(x_194, 2);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_194);
x_303 = lean_ctor_get(x_268, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_268, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_268, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_268, 3);
lean_inc(x_306);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_307 = x_268;
} else {
 lean_dec_ref(x_268);
 x_307 = lean_box(0);
}
lean_inc(x_195);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_195);
lean_ctor_set(x_308, 1, x_301);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_303);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_309 = x_195;
} else {
 lean_dec_ref(x_195);
 x_309 = lean_box(0);
}
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 4, 1);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_40);
lean_ctor_set(x_310, 2, x_41);
lean_ctor_set(x_310, 3, x_42);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_243);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_277);
return x_311;
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_194);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_ctor_get(x_194, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_194, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_195);
if (x_315 == 0)
{
uint8_t x_316; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_277);
x_316 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_316);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_317 = lean_ctor_get(x_195, 0);
x_318 = lean_ctor_get(x_195, 1);
x_319 = lean_ctor_get(x_195, 2);
x_320 = lean_ctor_get(x_195, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_195);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_317);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
lean_ctor_set(x_321, 3, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_277);
x_322 = 0;
lean_ctor_set(x_194, 0, x_321);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_322);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_194, 1);
x_324 = lean_ctor_get(x_194, 2);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_194);
x_325 = lean_ctor_get(x_195, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_195, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_195, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_195, 3);
lean_inc(x_328);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_329 = x_195;
} else {
 lean_dec_ref(x_195);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_330, 2, x_327);
lean_ctor_set(x_330, 3, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_277);
x_331 = 0;
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_323);
lean_ctor_set(x_332, 2, x_324);
lean_ctor_set(x_332, 3, x_268);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
lean_ctor_set(x_1, 0, x_332);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
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
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint32_t x_337; uint8_t x_338; uint8_t x_339; 
x_333 = lean_ctor_get(x_1, 0);
x_334 = lean_ctor_get(x_1, 1);
x_335 = lean_ctor_get(x_1, 2);
x_336 = lean_ctor_get(x_1, 3);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_1);
x_337 = lean_unbox_uint32(x_334);
x_338 = x_2 < x_337;
x_339 = l_coeDecidableEq(x_338);
if (x_339 == 0)
{
uint32_t x_340; uint8_t x_341; uint8_t x_342; 
x_340 = lean_unbox_uint32(x_334);
x_341 = x_340 < x_2;
x_342 = l_coeDecidableEq(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_335);
lean_dec(x_334);
x_343 = lean_box_uint32(x_2);
x_344 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_344, 0, x_333);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_3);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_7);
return x_344;
}
else
{
uint8_t x_345; uint8_t x_346; 
x_345 = l_RBNode_isRed___rarg(x_336);
x_346 = l_coeDecidableEq(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_336, x_2, x_3);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_333);
lean_ctor_set(x_348, 1, x_334);
lean_ctor_set(x_348, 2, x_335);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_336, x_2, x_3);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_349, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_354 = x_349;
} else {
 lean_dec_ref(x_349);
 x_354 = lean_box(0);
}
x_355 = 0;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_351);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
x_357 = 1;
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_333);
lean_ctor_set(x_358, 1, x_334);
lean_ctor_set(x_358, 2, x_335);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
return x_358;
}
else
{
uint8_t x_359; 
x_359 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 2);
lean_inc(x_361);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_362 = x_349;
} else {
 lean_dec_ref(x_349);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_351, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_367 = x_351;
} else {
 lean_dec_ref(x_351);
 x_367 = lean_box(0);
}
x_368 = 1;
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_333);
lean_ctor_set(x_369, 1, x_334);
lean_ctor_set(x_369, 2, x_335);
lean_ctor_set(x_369, 3, x_350);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_368);
if (lean_is_scalar(x_362)) {
 x_370 = lean_alloc_ctor(1, 4, 1);
} else {
 x_370 = x_362;
}
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_364);
lean_ctor_set(x_370, 2, x_365);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_368);
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_361);
lean_ctor_set(x_371, 3, x_370);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_359);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_349, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_349, 2);
lean_inc(x_373);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_374 = x_349;
} else {
 lean_dec_ref(x_349);
 x_374 = lean_box(0);
}
x_375 = 0;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_350);
lean_ctor_set(x_376, 1, x_372);
lean_ctor_set(x_376, 2, x_373);
lean_ctor_set(x_376, 3, x_351);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
x_377 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_377, 0, x_333);
lean_ctor_set(x_377, 1, x_334);
lean_ctor_set(x_377, 2, x_335);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_359);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_379 = lean_ctor_get(x_349, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_382 = x_349;
} else {
 lean_dec_ref(x_349);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_350, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_350, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_350, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_387 = x_350;
} else {
 lean_dec_ref(x_350);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_333);
lean_ctor_set(x_389, 1, x_334);
lean_ctor_set(x_389, 2, x_335);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_384);
lean_ctor_set(x_391, 2, x_385);
lean_ctor_set(x_391, 3, x_390);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_378);
return x_391;
}
else
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_349, 3);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_349, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_349, 2);
lean_inc(x_394);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_395 = x_349;
} else {
 lean_dec_ref(x_349);
 x_395 = lean_box(0);
}
x_396 = 0;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_350);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_397, 2, x_394);
lean_ctor_set(x_397, 3, x_392);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_333);
lean_ctor_set(x_398, 1, x_334);
lean_ctor_set(x_398, 2, x_335);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_378);
return x_398;
}
else
{
uint8_t x_399; 
x_399 = lean_ctor_get_uint8(x_392, sizeof(void*)*4);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_400 = lean_ctor_get(x_349, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_349, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_402 = x_349;
} else {
 lean_dec_ref(x_349);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_392, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_392, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_392, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_392, 3);
lean_inc(x_406);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_407 = x_392;
} else {
 lean_dec_ref(x_392);
 x_407 = lean_box(0);
}
lean_inc(x_350);
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_333);
lean_ctor_set(x_408, 1, x_334);
lean_ctor_set(x_408, 2, x_335);
lean_ctor_set(x_408, 3, x_350);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_409 = x_350;
} else {
 lean_dec_ref(x_350);
 x_409 = lean_box(0);
}
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_403);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set(x_410, 2, x_405);
lean_ctor_set(x_410, 3, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_402)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_402;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_400);
lean_ctor_set(x_411, 2, x_401);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_399);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_414 = x_349;
} else {
 lean_dec_ref(x_349);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_350, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_350, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_350, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_350, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_419 = x_350;
} else {
 lean_dec_ref(x_350);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_399);
x_421 = 0;
if (lean_is_scalar(x_414)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_414;
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_412);
lean_ctor_set(x_422, 2, x_413);
lean_ctor_set(x_422, 3, x_392);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_333);
lean_ctor_set(x_423, 1, x_334);
lean_ctor_set(x_423, 2, x_335);
lean_ctor_set(x_423, 3, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_399);
return x_423;
}
}
}
}
}
}
}
else
{
uint8_t x_424; uint8_t x_425; 
x_424 = l_RBNode_isRed___rarg(x_333);
x_425 = l_coeDecidableEq(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_333, x_2, x_3);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_334);
lean_ctor_set(x_427, 2, x_335);
lean_ctor_set(x_427, 3, x_336);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_7);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_333, x_2, x_3);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 3);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 2);
lean_inc(x_432);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_433 = x_428;
} else {
 lean_dec_ref(x_428);
 x_433 = lean_box(0);
}
x_434 = 0;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_432);
lean_ctor_set(x_435, 3, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_334);
lean_ctor_set(x_437, 2, x_335);
lean_ctor_set(x_437, 3, x_336);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_430, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_430, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_430, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_430, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_446 = x_430;
} else {
 lean_dec_ref(x_430);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_429);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_334);
lean_ctor_set(x_449, 2, x_335);
lean_ctor_set(x_449, 3, x_336);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_444);
lean_ctor_set(x_450, 3, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_438);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_428, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_428, 2);
lean_inc(x_452);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_453 = x_428;
} else {
 lean_dec_ref(x_428);
 x_453 = lean_box(0);
}
x_454 = 0;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_429);
lean_ctor_set(x_455, 1, x_451);
lean_ctor_set(x_455, 2, x_452);
lean_ctor_set(x_455, 3, x_430);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_334);
lean_ctor_set(x_456, 2, x_335);
lean_ctor_set(x_456, 3, x_336);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_438);
return x_456;
}
}
}
else
{
uint8_t x_457; 
x_457 = lean_ctor_get_uint8(x_429, sizeof(void*)*4);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_458 = lean_ctor_get(x_428, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_428, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_428, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_461 = x_428;
} else {
 lean_dec_ref(x_428);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_429, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_429, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_429, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_429, 3);
lean_inc(x_465);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_466 = x_429;
} else {
 lean_dec_ref(x_429);
 x_466 = lean_box(0);
}
x_467 = 1;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_462);
lean_ctor_set(x_468, 1, x_463);
lean_ctor_set(x_468, 2, x_464);
lean_ctor_set(x_468, 3, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
if (lean_is_scalar(x_461)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_461;
}
lean_ctor_set(x_469, 0, x_460);
lean_ctor_set(x_469, 1, x_334);
lean_ctor_set(x_469, 2, x_335);
lean_ctor_set(x_469, 3, x_336);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_467);
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_458);
lean_ctor_set(x_470, 2, x_459);
lean_ctor_set(x_470, 3, x_469);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_457);
return x_470;
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_428, 3);
lean_inc(x_471);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_472 = lean_ctor_get(x_428, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_428, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_474 = x_428;
} else {
 lean_dec_ref(x_428);
 x_474 = lean_box(0);
}
x_475 = 0;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_474;
}
lean_ctor_set(x_476, 0, x_429);
lean_ctor_set(x_476, 1, x_472);
lean_ctor_set(x_476, 2, x_473);
lean_ctor_set(x_476, 3, x_471);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_334);
lean_ctor_set(x_477, 2, x_335);
lean_ctor_set(x_477, 3, x_336);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_457);
return x_477;
}
else
{
uint8_t x_478; 
x_478 = lean_ctor_get_uint8(x_471, sizeof(void*)*4);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_428, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_428, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_481 = x_428;
} else {
 lean_dec_ref(x_428);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_471, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_471, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_471, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_471, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 x_486 = x_471;
} else {
 lean_dec_ref(x_471);
 x_486 = lean_box(0);
}
lean_inc(x_429);
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_429);
lean_ctor_set(x_487, 1, x_479);
lean_ctor_set(x_487, 2, x_480);
lean_ctor_set(x_487, 3, x_482);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_488 = x_429;
} else {
 lean_dec_ref(x_429);
 x_488 = lean_box(0);
}
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_334);
lean_ctor_set(x_489, 2, x_335);
lean_ctor_set(x_489, 3, x_336);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_481)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_481;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_483);
lean_ctor_set(x_490, 2, x_484);
lean_ctor_set(x_490, 3, x_489);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_478);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_491 = lean_ctor_get(x_428, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_428, 2);
lean_inc(x_492);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_493 = x_428;
} else {
 lean_dec_ref(x_428);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_429, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_429, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_429, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_429, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_498 = x_429;
} else {
 lean_dec_ref(x_429);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_495);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_497);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_478);
x_500 = 0;
if (lean_is_scalar(x_493)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_493;
}
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_491);
lean_ctor_set(x_501, 2, x_492);
lean_ctor_set(x_501, 3, x_471);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_334);
lean_ctor_set(x_502, 2, x_335);
lean_ctor_set(x_502, 3, x_336);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_478);
return x_502;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box_uint32(x_2);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_unbox_uint32(x_10);
x_17 = x_16 < x_2;
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; 
x_20 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_20);
return x_1;
}
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = lean_unbox_uint32(x_23);
x_27 = x_2 < x_26;
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = lean_unbox_uint32(x_23);
x_30 = x_29 < x_2;
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_box_uint32(x_2);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_25, x_2, x_3);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_22, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_unbox_uint32(x_40);
x_44 = x_2 < x_43;
x_45 = l_coeDecidableEq(x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_unbox_uint32(x_40);
x_47 = x_46 < x_2;
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_40);
x_49 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_49);
return x_1;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_RBNode_isRed___rarg(x_42);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_42, x_2, x_3);
lean_ctor_set(x_1, 3, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_42, x_2, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = 0;
lean_ctor_set(x_53, 0, x_55);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_59);
x_60 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_53, 1);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = 1;
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_53, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
x_75 = lean_ctor_get(x_55, 2);
x_76 = lean_ctor_get(x_55, 3);
x_77 = 1;
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_77);
lean_ctor_set(x_53, 3, x_76);
lean_ctor_set(x_53, 2, x_75);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_73);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_77);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_55, 0);
x_79 = lean_ctor_get(x_55, 1);
x_80 = lean_ctor_get(x_55, 2);
x_81 = lean_ctor_get(x_55, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_55);
x_82 = 1;
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_40);
lean_ctor_set(x_83, 2, x_41);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
lean_ctor_set(x_53, 3, x_81);
lean_ctor_set(x_53, 2, x_80);
lean_ctor_set(x_53, 1, x_79);
lean_ctor_set(x_53, 0, x_78);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_82);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_53, 1);
x_85 = lean_ctor_get(x_53, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_ctor_get(x_55, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_55, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_55, 3);
lean_inc(x_89);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_90 = x_55;
} else {
 lean_dec_ref(x_55);
 x_90 = lean_box(0);
}
x_91 = 1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(1, 4, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_39);
lean_ctor_set(x_92, 1, x_40);
lean_ctor_set(x_92, 2, x_41);
lean_ctor_set(x_92, 3, x_54);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_91);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_85);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_92);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_53, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_53, 0);
lean_dec(x_96);
x_97 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_97);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_53, 1);
x_99 = lean_ctor_get(x_53, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_53);
x_100 = 0;
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_55);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_101);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
}
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_53);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_53, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_54);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_54, 0);
x_107 = lean_ctor_get(x_54, 1);
x_108 = lean_ctor_get(x_54, 2);
x_109 = lean_ctor_get(x_54, 3);
x_110 = 1;
lean_ctor_set(x_54, 3, x_106);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_110);
lean_ctor_set(x_53, 0, x_109);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_110);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_108);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_54, 0);
x_112 = lean_ctor_get(x_54, 1);
x_113 = lean_ctor_get(x_54, 2);
x_114 = lean_ctor_get(x_54, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_54);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_39);
lean_ctor_set(x_116, 1, x_40);
lean_ctor_set(x_116, 2, x_41);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
lean_ctor_set(x_53, 0, x_114);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_53, 1);
x_118 = lean_ctor_get(x_53, 2);
x_119 = lean_ctor_get(x_53, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_53);
x_120 = lean_ctor_get(x_54, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_54, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_54, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_54, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_124 = x_54;
} else {
 lean_dec_ref(x_54);
 x_124 = lean_box(0);
}
x_125 = 1;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 4, 1);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_40);
lean_ctor_set(x_126, 2, x_41);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_117);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_127);
lean_ctor_set(x_1, 2, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_53, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_53);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_53, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_53, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_132);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_53, 1);
x_134 = lean_ctor_get(x_53, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_53);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_54);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_128);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_137 == 0)
{
uint8_t x_138; 
lean_free_object(x_1);
x_138 = !lean_is_exclusive(x_53);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_53, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_53, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_128);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
x_144 = lean_ctor_get(x_128, 2);
x_145 = lean_ctor_get(x_128, 3);
lean_inc(x_54);
lean_ctor_set(x_128, 3, x_54);
lean_ctor_set(x_128, 2, x_41);
lean_ctor_set(x_128, 1, x_40);
lean_ctor_set(x_128, 0, x_39);
x_146 = !lean_is_exclusive(x_54);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_54, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_54, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_54, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_54, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
lean_ctor_set(x_54, 3, x_145);
lean_ctor_set(x_54, 2, x_144);
lean_ctor_set(x_54, 1, x_143);
lean_ctor_set(x_54, 0, x_142);
lean_ctor_set(x_53, 3, x_54);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
else
{
lean_object* x_151; 
lean_dec(x_54);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_145);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_151);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_128, 0);
x_153 = lean_ctor_get(x_128, 1);
x_154 = lean_ctor_get(x_128, 2);
x_155 = lean_ctor_get(x_128, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_128);
lean_inc(x_54);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_39);
lean_ctor_set(x_156, 1, x_40);
lean_ctor_set(x_156, 2, x_41);
lean_ctor_set(x_156, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_157 = x_54;
} else {
 lean_dec_ref(x_54);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_154);
lean_ctor_set(x_158, 3, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_158);
lean_ctor_set(x_53, 0, x_156);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_53, 1);
x_160 = lean_ctor_get(x_53, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_53);
x_161 = lean_ctor_get(x_128, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_128, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_128, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_128, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_165 = x_128;
} else {
 lean_dec_ref(x_128);
 x_165 = lean_box(0);
}
lean_inc(x_54);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_39);
lean_ctor_set(x_166, 1, x_40);
lean_ctor_set(x_166, 2, x_41);
lean_ctor_set(x_166, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_167 = x_54;
} else {
 lean_dec_ref(x_54);
 x_167 = lean_box(0);
}
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_102);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_169, 2, x_160);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_137);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_53);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_53, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_53, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_54);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_137);
x_174 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_174);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_54, 0);
x_176 = lean_ctor_get(x_54, 1);
x_177 = lean_ctor_get(x_54, 2);
x_178 = lean_ctor_get(x_54, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_54);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_137);
x_180 = 0;
lean_ctor_set(x_53, 0, x_179);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_180);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_53, 1);
x_182 = lean_ctor_get(x_53, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_53);
x_183 = lean_ctor_get(x_54, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_54, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_54, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_54, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_187 = x_54;
} else {
 lean_dec_ref(x_54);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_137);
x_189 = 0;
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_128);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_189);
lean_ctor_set(x_1, 3, x_190);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
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
uint8_t x_191; uint8_t x_192; 
x_191 = l_RBNode_isRed___rarg(x_39);
x_192 = l_coeDecidableEq(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_39, x_2, x_3);
lean_ctor_set(x_1, 0, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_39, x_2, x_3);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_194, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_194, 0);
lean_dec(x_199);
x_200 = 0;
lean_ctor_set(x_194, 0, x_196);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_200);
x_201 = 1;
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_194, 1);
x_203 = lean_ctor_get(x_194, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_194);
x_204 = 0;
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_196);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_204);
x_206 = 1;
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_206);
return x_1;
}
}
else
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_194, 1);
x_210 = lean_ctor_get(x_194, 2);
x_211 = lean_ctor_get(x_194, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_194, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_196);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_196, 0);
x_215 = lean_ctor_get(x_196, 1);
x_216 = lean_ctor_get(x_196, 2);
x_217 = lean_ctor_get(x_196, 3);
x_218 = 1;
lean_ctor_set(x_196, 3, x_214);
lean_ctor_set(x_196, 2, x_210);
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_218);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_217);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_218);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_216);
lean_ctor_set(x_1, 1, x_215);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_196, 0);
x_220 = lean_ctor_get(x_196, 1);
x_221 = lean_ctor_get(x_196, 2);
x_222 = lean_ctor_get(x_196, 3);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_196);
x_223 = 1;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_195);
lean_ctor_set(x_224, 1, x_209);
lean_ctor_set(x_224, 2, x_210);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_222);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_194, 1);
x_226 = lean_ctor_get(x_194, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_194);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_40);
lean_ctor_set(x_234, 2, x_41);
lean_ctor_set(x_234, 3, x_42);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_194);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_194, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 0);
lean_dec(x_237);
x_238 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_238);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_194, 1);
x_240 = lean_ctor_get(x_194, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_194);
x_241 = 0;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_195);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_196);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_194);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_194, 1);
x_246 = lean_ctor_get(x_194, 2);
x_247 = lean_ctor_get(x_194, 3);
x_248 = lean_ctor_get(x_194, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_195);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_250);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_250);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_195, 0);
x_252 = lean_ctor_get(x_195, 1);
x_253 = lean_ctor_get(x_195, 2);
x_254 = lean_ctor_get(x_195, 3);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_195);
x_255 = 1;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_257 = lean_ctor_get(x_194, 1);
x_258 = lean_ctor_get(x_194, 2);
x_259 = lean_ctor_get(x_194, 3);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_194);
x_260 = lean_ctor_get(x_195, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_195, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_195, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_195, 3);
lean_inc(x_263);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_264 = x_195;
} else {
 lean_dec_ref(x_195);
 x_264 = lean_box(0);
}
x_265 = 1;
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(1, 4, 1);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_261);
lean_ctor_set(x_266, 2, x_262);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
x_267 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_40);
lean_ctor_set(x_267, 2, x_41);
lean_ctor_set(x_267, 3, x_42);
lean_ctor_set_uint8(x_267, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 3, x_267);
lean_ctor_set(x_1, 2, x_258);
lean_ctor_set(x_1, 1, x_257);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_194, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_194);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_194, 3);
lean_dec(x_270);
x_271 = lean_ctor_get(x_194, 0);
lean_dec(x_271);
x_272 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_272);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_194, 1);
x_274 = lean_ctor_get(x_194, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_194);
x_275 = 0;
x_276 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_276, 0, x_195);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_274);
lean_ctor_set(x_276, 3, x_268);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_276);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
uint8_t x_277; 
x_277 = lean_ctor_get_uint8(x_268, sizeof(void*)*4);
if (x_277 == 0)
{
uint8_t x_278; 
lean_free_object(x_1);
x_278 = !lean_is_exclusive(x_194);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_194, 1);
x_280 = lean_ctor_get(x_194, 2);
x_281 = lean_ctor_get(x_194, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_194, 0);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_268);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_268, 0);
x_285 = lean_ctor_get(x_268, 1);
x_286 = lean_ctor_get(x_268, 2);
x_287 = lean_ctor_get(x_268, 3);
lean_inc(x_195);
lean_ctor_set(x_268, 3, x_284);
lean_ctor_set(x_268, 2, x_280);
lean_ctor_set(x_268, 1, x_279);
lean_ctor_set(x_268, 0, x_195);
x_288 = !lean_is_exclusive(x_195);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_195, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_195, 2);
lean_dec(x_290);
x_291 = lean_ctor_get(x_195, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_195, 0);
lean_dec(x_292);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
lean_ctor_set(x_195, 3, x_42);
lean_ctor_set(x_195, 2, x_41);
lean_ctor_set(x_195, 1, x_40);
lean_ctor_set(x_195, 0, x_287);
lean_ctor_set(x_194, 3, x_195);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
else
{
lean_object* x_293; 
lean_dec(x_195);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_40);
lean_ctor_set(x_293, 2, x_41);
lean_ctor_set(x_293, 3, x_42);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_293);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_268, 0);
x_295 = lean_ctor_get(x_268, 1);
x_296 = lean_ctor_get(x_268, 2);
x_297 = lean_ctor_get(x_268, 3);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_268);
lean_inc(x_195);
x_298 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_298, 0, x_195);
lean_ctor_set(x_298, 1, x_279);
lean_ctor_set(x_298, 2, x_280);
lean_ctor_set(x_298, 3, x_294);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_299 = x_195;
} else {
 lean_dec_ref(x_195);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_40);
lean_ctor_set(x_300, 2, x_41);
lean_ctor_set(x_300, 3, x_42);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_300);
lean_ctor_set(x_194, 2, x_296);
lean_ctor_set(x_194, 1, x_295);
lean_ctor_set(x_194, 0, x_298);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = lean_ctor_get(x_194, 1);
x_302 = lean_ctor_get(x_194, 2);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_194);
x_303 = lean_ctor_get(x_268, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_268, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_268, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_268, 3);
lean_inc(x_306);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_307 = x_268;
} else {
 lean_dec_ref(x_268);
 x_307 = lean_box(0);
}
lean_inc(x_195);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_195);
lean_ctor_set(x_308, 1, x_301);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_303);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_309 = x_195;
} else {
 lean_dec_ref(x_195);
 x_309 = lean_box(0);
}
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 4, 1);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_40);
lean_ctor_set(x_310, 2, x_41);
lean_ctor_set(x_310, 3, x_42);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_243);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_277);
return x_311;
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_194);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_ctor_get(x_194, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_194, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_195);
if (x_315 == 0)
{
uint8_t x_316; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_277);
x_316 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_316);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_317 = lean_ctor_get(x_195, 0);
x_318 = lean_ctor_get(x_195, 1);
x_319 = lean_ctor_get(x_195, 2);
x_320 = lean_ctor_get(x_195, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_195);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_317);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
lean_ctor_set(x_321, 3, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_277);
x_322 = 0;
lean_ctor_set(x_194, 0, x_321);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_322);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_194, 1);
x_324 = lean_ctor_get(x_194, 2);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_194);
x_325 = lean_ctor_get(x_195, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_195, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_195, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_195, 3);
lean_inc(x_328);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_329 = x_195;
} else {
 lean_dec_ref(x_195);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_330, 2, x_327);
lean_ctor_set(x_330, 3, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_277);
x_331 = 0;
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_323);
lean_ctor_set(x_332, 2, x_324);
lean_ctor_set(x_332, 3, x_268);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
lean_ctor_set(x_1, 0, x_332);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
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
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint32_t x_337; uint8_t x_338; uint8_t x_339; 
x_333 = lean_ctor_get(x_1, 0);
x_334 = lean_ctor_get(x_1, 1);
x_335 = lean_ctor_get(x_1, 2);
x_336 = lean_ctor_get(x_1, 3);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_1);
x_337 = lean_unbox_uint32(x_334);
x_338 = x_2 < x_337;
x_339 = l_coeDecidableEq(x_338);
if (x_339 == 0)
{
uint32_t x_340; uint8_t x_341; uint8_t x_342; 
x_340 = lean_unbox_uint32(x_334);
x_341 = x_340 < x_2;
x_342 = l_coeDecidableEq(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_335);
lean_dec(x_334);
x_343 = lean_box_uint32(x_2);
x_344 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_344, 0, x_333);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_3);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_7);
return x_344;
}
else
{
uint8_t x_345; uint8_t x_346; 
x_345 = l_RBNode_isRed___rarg(x_336);
x_346 = l_coeDecidableEq(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_336, x_2, x_3);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_333);
lean_ctor_set(x_348, 1, x_334);
lean_ctor_set(x_348, 2, x_335);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_336, x_2, x_3);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_349, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_354 = x_349;
} else {
 lean_dec_ref(x_349);
 x_354 = lean_box(0);
}
x_355 = 0;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_351);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
x_357 = 1;
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_333);
lean_ctor_set(x_358, 1, x_334);
lean_ctor_set(x_358, 2, x_335);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
return x_358;
}
else
{
uint8_t x_359; 
x_359 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 2);
lean_inc(x_361);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_362 = x_349;
} else {
 lean_dec_ref(x_349);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_351, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_367 = x_351;
} else {
 lean_dec_ref(x_351);
 x_367 = lean_box(0);
}
x_368 = 1;
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_333);
lean_ctor_set(x_369, 1, x_334);
lean_ctor_set(x_369, 2, x_335);
lean_ctor_set(x_369, 3, x_350);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_368);
if (lean_is_scalar(x_362)) {
 x_370 = lean_alloc_ctor(1, 4, 1);
} else {
 x_370 = x_362;
}
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_364);
lean_ctor_set(x_370, 2, x_365);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_368);
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_361);
lean_ctor_set(x_371, 3, x_370);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_359);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_349, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_349, 2);
lean_inc(x_373);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_374 = x_349;
} else {
 lean_dec_ref(x_349);
 x_374 = lean_box(0);
}
x_375 = 0;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_350);
lean_ctor_set(x_376, 1, x_372);
lean_ctor_set(x_376, 2, x_373);
lean_ctor_set(x_376, 3, x_351);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
x_377 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_377, 0, x_333);
lean_ctor_set(x_377, 1, x_334);
lean_ctor_set(x_377, 2, x_335);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_359);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_379 = lean_ctor_get(x_349, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_382 = x_349;
} else {
 lean_dec_ref(x_349);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_350, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_350, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_350, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_387 = x_350;
} else {
 lean_dec_ref(x_350);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_333);
lean_ctor_set(x_389, 1, x_334);
lean_ctor_set(x_389, 2, x_335);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_384);
lean_ctor_set(x_391, 2, x_385);
lean_ctor_set(x_391, 3, x_390);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_378);
return x_391;
}
else
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_349, 3);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_349, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_349, 2);
lean_inc(x_394);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_395 = x_349;
} else {
 lean_dec_ref(x_349);
 x_395 = lean_box(0);
}
x_396 = 0;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_350);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_397, 2, x_394);
lean_ctor_set(x_397, 3, x_392);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_333);
lean_ctor_set(x_398, 1, x_334);
lean_ctor_set(x_398, 2, x_335);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_378);
return x_398;
}
else
{
uint8_t x_399; 
x_399 = lean_ctor_get_uint8(x_392, sizeof(void*)*4);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_400 = lean_ctor_get(x_349, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_349, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_402 = x_349;
} else {
 lean_dec_ref(x_349);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_392, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_392, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_392, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_392, 3);
lean_inc(x_406);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_407 = x_392;
} else {
 lean_dec_ref(x_392);
 x_407 = lean_box(0);
}
lean_inc(x_350);
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_333);
lean_ctor_set(x_408, 1, x_334);
lean_ctor_set(x_408, 2, x_335);
lean_ctor_set(x_408, 3, x_350);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_409 = x_350;
} else {
 lean_dec_ref(x_350);
 x_409 = lean_box(0);
}
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_403);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set(x_410, 2, x_405);
lean_ctor_set(x_410, 3, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_402)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_402;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_400);
lean_ctor_set(x_411, 2, x_401);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_399);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_414 = x_349;
} else {
 lean_dec_ref(x_349);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_350, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_350, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_350, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_350, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_419 = x_350;
} else {
 lean_dec_ref(x_350);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_399);
x_421 = 0;
if (lean_is_scalar(x_414)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_414;
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_412);
lean_ctor_set(x_422, 2, x_413);
lean_ctor_set(x_422, 3, x_392);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_333);
lean_ctor_set(x_423, 1, x_334);
lean_ctor_set(x_423, 2, x_335);
lean_ctor_set(x_423, 3, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_399);
return x_423;
}
}
}
}
}
}
}
else
{
uint8_t x_424; uint8_t x_425; 
x_424 = l_RBNode_isRed___rarg(x_333);
x_425 = l_coeDecidableEq(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_333, x_2, x_3);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_334);
lean_ctor_set(x_427, 2, x_335);
lean_ctor_set(x_427, 3, x_336);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_7);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_333, x_2, x_3);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 3);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 2);
lean_inc(x_432);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_433 = x_428;
} else {
 lean_dec_ref(x_428);
 x_433 = lean_box(0);
}
x_434 = 0;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_432);
lean_ctor_set(x_435, 3, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_334);
lean_ctor_set(x_437, 2, x_335);
lean_ctor_set(x_437, 3, x_336);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_430, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_430, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_430, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_430, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_446 = x_430;
} else {
 lean_dec_ref(x_430);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_429);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_334);
lean_ctor_set(x_449, 2, x_335);
lean_ctor_set(x_449, 3, x_336);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_444);
lean_ctor_set(x_450, 3, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_438);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_428, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_428, 2);
lean_inc(x_452);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_453 = x_428;
} else {
 lean_dec_ref(x_428);
 x_453 = lean_box(0);
}
x_454 = 0;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_429);
lean_ctor_set(x_455, 1, x_451);
lean_ctor_set(x_455, 2, x_452);
lean_ctor_set(x_455, 3, x_430);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_334);
lean_ctor_set(x_456, 2, x_335);
lean_ctor_set(x_456, 3, x_336);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_438);
return x_456;
}
}
}
else
{
uint8_t x_457; 
x_457 = lean_ctor_get_uint8(x_429, sizeof(void*)*4);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_458 = lean_ctor_get(x_428, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_428, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_428, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_461 = x_428;
} else {
 lean_dec_ref(x_428);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_429, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_429, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_429, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_429, 3);
lean_inc(x_465);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_466 = x_429;
} else {
 lean_dec_ref(x_429);
 x_466 = lean_box(0);
}
x_467 = 1;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_462);
lean_ctor_set(x_468, 1, x_463);
lean_ctor_set(x_468, 2, x_464);
lean_ctor_set(x_468, 3, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
if (lean_is_scalar(x_461)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_461;
}
lean_ctor_set(x_469, 0, x_460);
lean_ctor_set(x_469, 1, x_334);
lean_ctor_set(x_469, 2, x_335);
lean_ctor_set(x_469, 3, x_336);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_467);
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_458);
lean_ctor_set(x_470, 2, x_459);
lean_ctor_set(x_470, 3, x_469);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_457);
return x_470;
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_428, 3);
lean_inc(x_471);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_472 = lean_ctor_get(x_428, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_428, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_474 = x_428;
} else {
 lean_dec_ref(x_428);
 x_474 = lean_box(0);
}
x_475 = 0;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_474;
}
lean_ctor_set(x_476, 0, x_429);
lean_ctor_set(x_476, 1, x_472);
lean_ctor_set(x_476, 2, x_473);
lean_ctor_set(x_476, 3, x_471);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_334);
lean_ctor_set(x_477, 2, x_335);
lean_ctor_set(x_477, 3, x_336);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_457);
return x_477;
}
else
{
uint8_t x_478; 
x_478 = lean_ctor_get_uint8(x_471, sizeof(void*)*4);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_428, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_428, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_481 = x_428;
} else {
 lean_dec_ref(x_428);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_471, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_471, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_471, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_471, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 x_486 = x_471;
} else {
 lean_dec_ref(x_471);
 x_486 = lean_box(0);
}
lean_inc(x_429);
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_429);
lean_ctor_set(x_487, 1, x_479);
lean_ctor_set(x_487, 2, x_480);
lean_ctor_set(x_487, 3, x_482);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_488 = x_429;
} else {
 lean_dec_ref(x_429);
 x_488 = lean_box(0);
}
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_334);
lean_ctor_set(x_489, 2, x_335);
lean_ctor_set(x_489, 3, x_336);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_481)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_481;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_483);
lean_ctor_set(x_490, 2, x_484);
lean_ctor_set(x_490, 3, x_489);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_478);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_491 = lean_ctor_get(x_428, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_428, 2);
lean_inc(x_492);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_493 = x_428;
} else {
 lean_dec_ref(x_428);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_429, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_429, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_429, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_429, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_498 = x_429;
} else {
 lean_dec_ref(x_429);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_495);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_497);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_478);
x_500 = 0;
if (lean_is_scalar(x_493)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_493;
}
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_491);
lean_ctor_set(x_501, 2, x_492);
lean_ctor_set(x_501, 3, x_471);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_334);
lean_ctor_set(x_502, 2, x_335);
lean_ctor_set(x_502, 3, x_336);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_478);
return x_502;
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
uint8_t x_4; uint8_t x_5; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__3___rarg(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__4___rarg(x_1, x_2, x_3);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box_uint32(x_2);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_unbox_uint32(x_10);
x_17 = x_16 < x_2;
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; 
x_20 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_20);
return x_1;
}
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = lean_unbox_uint32(x_23);
x_27 = x_2 < x_26;
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = lean_unbox_uint32(x_23);
x_30 = x_29 < x_2;
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_box_uint32(x_2);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_25, x_2, x_3);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_22, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_unbox_uint32(x_40);
x_44 = x_2 < x_43;
x_45 = l_coeDecidableEq(x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_unbox_uint32(x_40);
x_47 = x_46 < x_2;
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_40);
x_49 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_49);
return x_1;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_RBNode_isRed___rarg(x_42);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_42, x_2, x_3);
lean_ctor_set(x_1, 3, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_42, x_2, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = 0;
lean_ctor_set(x_53, 0, x_55);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_59);
x_60 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_53, 1);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = 1;
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_53, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
x_75 = lean_ctor_get(x_55, 2);
x_76 = lean_ctor_get(x_55, 3);
x_77 = 1;
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_77);
lean_ctor_set(x_53, 3, x_76);
lean_ctor_set(x_53, 2, x_75);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_73);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_77);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_55, 0);
x_79 = lean_ctor_get(x_55, 1);
x_80 = lean_ctor_get(x_55, 2);
x_81 = lean_ctor_get(x_55, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_55);
x_82 = 1;
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_40);
lean_ctor_set(x_83, 2, x_41);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
lean_ctor_set(x_53, 3, x_81);
lean_ctor_set(x_53, 2, x_80);
lean_ctor_set(x_53, 1, x_79);
lean_ctor_set(x_53, 0, x_78);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_82);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_53, 1);
x_85 = lean_ctor_get(x_53, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_ctor_get(x_55, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_55, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_55, 3);
lean_inc(x_89);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_90 = x_55;
} else {
 lean_dec_ref(x_55);
 x_90 = lean_box(0);
}
x_91 = 1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(1, 4, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_39);
lean_ctor_set(x_92, 1, x_40);
lean_ctor_set(x_92, 2, x_41);
lean_ctor_set(x_92, 3, x_54);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_91);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_85);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_92);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_53, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_53, 0);
lean_dec(x_96);
x_97 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_97);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_53, 1);
x_99 = lean_ctor_get(x_53, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_53);
x_100 = 0;
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_55);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_101);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
}
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_53);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_53, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_54);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_54, 0);
x_107 = lean_ctor_get(x_54, 1);
x_108 = lean_ctor_get(x_54, 2);
x_109 = lean_ctor_get(x_54, 3);
x_110 = 1;
lean_ctor_set(x_54, 3, x_106);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_110);
lean_ctor_set(x_53, 0, x_109);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_110);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_108);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_54, 0);
x_112 = lean_ctor_get(x_54, 1);
x_113 = lean_ctor_get(x_54, 2);
x_114 = lean_ctor_get(x_54, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_54);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_39);
lean_ctor_set(x_116, 1, x_40);
lean_ctor_set(x_116, 2, x_41);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
lean_ctor_set(x_53, 0, x_114);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_53, 1);
x_118 = lean_ctor_get(x_53, 2);
x_119 = lean_ctor_get(x_53, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_53);
x_120 = lean_ctor_get(x_54, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_54, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_54, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_54, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_124 = x_54;
} else {
 lean_dec_ref(x_54);
 x_124 = lean_box(0);
}
x_125 = 1;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 4, 1);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_40);
lean_ctor_set(x_126, 2, x_41);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_117);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_127);
lean_ctor_set(x_1, 2, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_53, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_53);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_53, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_53, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_132);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_53, 1);
x_134 = lean_ctor_get(x_53, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_53);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_54);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_128);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_137 == 0)
{
uint8_t x_138; 
lean_free_object(x_1);
x_138 = !lean_is_exclusive(x_53);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_53, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_53, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_128);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
x_144 = lean_ctor_get(x_128, 2);
x_145 = lean_ctor_get(x_128, 3);
lean_inc(x_54);
lean_ctor_set(x_128, 3, x_54);
lean_ctor_set(x_128, 2, x_41);
lean_ctor_set(x_128, 1, x_40);
lean_ctor_set(x_128, 0, x_39);
x_146 = !lean_is_exclusive(x_54);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_54, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_54, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_54, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_54, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
lean_ctor_set(x_54, 3, x_145);
lean_ctor_set(x_54, 2, x_144);
lean_ctor_set(x_54, 1, x_143);
lean_ctor_set(x_54, 0, x_142);
lean_ctor_set(x_53, 3, x_54);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
else
{
lean_object* x_151; 
lean_dec(x_54);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_145);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_151);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_128, 0);
x_153 = lean_ctor_get(x_128, 1);
x_154 = lean_ctor_get(x_128, 2);
x_155 = lean_ctor_get(x_128, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_128);
lean_inc(x_54);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_39);
lean_ctor_set(x_156, 1, x_40);
lean_ctor_set(x_156, 2, x_41);
lean_ctor_set(x_156, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_157 = x_54;
} else {
 lean_dec_ref(x_54);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_154);
lean_ctor_set(x_158, 3, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_158);
lean_ctor_set(x_53, 0, x_156);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_53, 1);
x_160 = lean_ctor_get(x_53, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_53);
x_161 = lean_ctor_get(x_128, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_128, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_128, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_128, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_165 = x_128;
} else {
 lean_dec_ref(x_128);
 x_165 = lean_box(0);
}
lean_inc(x_54);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_39);
lean_ctor_set(x_166, 1, x_40);
lean_ctor_set(x_166, 2, x_41);
lean_ctor_set(x_166, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_167 = x_54;
} else {
 lean_dec_ref(x_54);
 x_167 = lean_box(0);
}
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_102);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_169, 2, x_160);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_137);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_53);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_53, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_53, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_54);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_137);
x_174 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_174);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_54, 0);
x_176 = lean_ctor_get(x_54, 1);
x_177 = lean_ctor_get(x_54, 2);
x_178 = lean_ctor_get(x_54, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_54);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_137);
x_180 = 0;
lean_ctor_set(x_53, 0, x_179);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_180);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_53, 1);
x_182 = lean_ctor_get(x_53, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_53);
x_183 = lean_ctor_get(x_54, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_54, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_54, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_54, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_187 = x_54;
} else {
 lean_dec_ref(x_54);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_137);
x_189 = 0;
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_128);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_189);
lean_ctor_set(x_1, 3, x_190);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
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
uint8_t x_191; uint8_t x_192; 
x_191 = l_RBNode_isRed___rarg(x_39);
x_192 = l_coeDecidableEq(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_39, x_2, x_3);
lean_ctor_set(x_1, 0, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_39, x_2, x_3);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_194, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_194, 0);
lean_dec(x_199);
x_200 = 0;
lean_ctor_set(x_194, 0, x_196);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_200);
x_201 = 1;
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_194, 1);
x_203 = lean_ctor_get(x_194, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_194);
x_204 = 0;
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_196);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_204);
x_206 = 1;
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_206);
return x_1;
}
}
else
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_194, 1);
x_210 = lean_ctor_get(x_194, 2);
x_211 = lean_ctor_get(x_194, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_194, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_196);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_196, 0);
x_215 = lean_ctor_get(x_196, 1);
x_216 = lean_ctor_get(x_196, 2);
x_217 = lean_ctor_get(x_196, 3);
x_218 = 1;
lean_ctor_set(x_196, 3, x_214);
lean_ctor_set(x_196, 2, x_210);
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_218);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_217);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_218);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_216);
lean_ctor_set(x_1, 1, x_215);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_196, 0);
x_220 = lean_ctor_get(x_196, 1);
x_221 = lean_ctor_get(x_196, 2);
x_222 = lean_ctor_get(x_196, 3);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_196);
x_223 = 1;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_195);
lean_ctor_set(x_224, 1, x_209);
lean_ctor_set(x_224, 2, x_210);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_222);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_194, 1);
x_226 = lean_ctor_get(x_194, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_194);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_40);
lean_ctor_set(x_234, 2, x_41);
lean_ctor_set(x_234, 3, x_42);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_194);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_194, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 0);
lean_dec(x_237);
x_238 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_238);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_194, 1);
x_240 = lean_ctor_get(x_194, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_194);
x_241 = 0;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_195);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_196);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_194);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_194, 1);
x_246 = lean_ctor_get(x_194, 2);
x_247 = lean_ctor_get(x_194, 3);
x_248 = lean_ctor_get(x_194, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_195);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_250);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_250);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_195, 0);
x_252 = lean_ctor_get(x_195, 1);
x_253 = lean_ctor_get(x_195, 2);
x_254 = lean_ctor_get(x_195, 3);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_195);
x_255 = 1;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_257 = lean_ctor_get(x_194, 1);
x_258 = lean_ctor_get(x_194, 2);
x_259 = lean_ctor_get(x_194, 3);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_194);
x_260 = lean_ctor_get(x_195, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_195, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_195, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_195, 3);
lean_inc(x_263);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_264 = x_195;
} else {
 lean_dec_ref(x_195);
 x_264 = lean_box(0);
}
x_265 = 1;
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(1, 4, 1);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_261);
lean_ctor_set(x_266, 2, x_262);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
x_267 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_40);
lean_ctor_set(x_267, 2, x_41);
lean_ctor_set(x_267, 3, x_42);
lean_ctor_set_uint8(x_267, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 3, x_267);
lean_ctor_set(x_1, 2, x_258);
lean_ctor_set(x_1, 1, x_257);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_194, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_194);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_194, 3);
lean_dec(x_270);
x_271 = lean_ctor_get(x_194, 0);
lean_dec(x_271);
x_272 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_272);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_194, 1);
x_274 = lean_ctor_get(x_194, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_194);
x_275 = 0;
x_276 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_276, 0, x_195);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_274);
lean_ctor_set(x_276, 3, x_268);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_276);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
uint8_t x_277; 
x_277 = lean_ctor_get_uint8(x_268, sizeof(void*)*4);
if (x_277 == 0)
{
uint8_t x_278; 
lean_free_object(x_1);
x_278 = !lean_is_exclusive(x_194);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_194, 1);
x_280 = lean_ctor_get(x_194, 2);
x_281 = lean_ctor_get(x_194, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_194, 0);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_268);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_268, 0);
x_285 = lean_ctor_get(x_268, 1);
x_286 = lean_ctor_get(x_268, 2);
x_287 = lean_ctor_get(x_268, 3);
lean_inc(x_195);
lean_ctor_set(x_268, 3, x_284);
lean_ctor_set(x_268, 2, x_280);
lean_ctor_set(x_268, 1, x_279);
lean_ctor_set(x_268, 0, x_195);
x_288 = !lean_is_exclusive(x_195);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_195, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_195, 2);
lean_dec(x_290);
x_291 = lean_ctor_get(x_195, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_195, 0);
lean_dec(x_292);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
lean_ctor_set(x_195, 3, x_42);
lean_ctor_set(x_195, 2, x_41);
lean_ctor_set(x_195, 1, x_40);
lean_ctor_set(x_195, 0, x_287);
lean_ctor_set(x_194, 3, x_195);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
else
{
lean_object* x_293; 
lean_dec(x_195);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_40);
lean_ctor_set(x_293, 2, x_41);
lean_ctor_set(x_293, 3, x_42);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_293);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_268, 0);
x_295 = lean_ctor_get(x_268, 1);
x_296 = lean_ctor_get(x_268, 2);
x_297 = lean_ctor_get(x_268, 3);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_268);
lean_inc(x_195);
x_298 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_298, 0, x_195);
lean_ctor_set(x_298, 1, x_279);
lean_ctor_set(x_298, 2, x_280);
lean_ctor_set(x_298, 3, x_294);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_299 = x_195;
} else {
 lean_dec_ref(x_195);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_40);
lean_ctor_set(x_300, 2, x_41);
lean_ctor_set(x_300, 3, x_42);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_300);
lean_ctor_set(x_194, 2, x_296);
lean_ctor_set(x_194, 1, x_295);
lean_ctor_set(x_194, 0, x_298);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = lean_ctor_get(x_194, 1);
x_302 = lean_ctor_get(x_194, 2);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_194);
x_303 = lean_ctor_get(x_268, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_268, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_268, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_268, 3);
lean_inc(x_306);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_307 = x_268;
} else {
 lean_dec_ref(x_268);
 x_307 = lean_box(0);
}
lean_inc(x_195);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_195);
lean_ctor_set(x_308, 1, x_301);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_303);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_309 = x_195;
} else {
 lean_dec_ref(x_195);
 x_309 = lean_box(0);
}
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 4, 1);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_40);
lean_ctor_set(x_310, 2, x_41);
lean_ctor_set(x_310, 3, x_42);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_243);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_277);
return x_311;
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_194);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_ctor_get(x_194, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_194, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_195);
if (x_315 == 0)
{
uint8_t x_316; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_277);
x_316 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_316);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_317 = lean_ctor_get(x_195, 0);
x_318 = lean_ctor_get(x_195, 1);
x_319 = lean_ctor_get(x_195, 2);
x_320 = lean_ctor_get(x_195, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_195);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_317);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
lean_ctor_set(x_321, 3, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_277);
x_322 = 0;
lean_ctor_set(x_194, 0, x_321);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_322);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_194, 1);
x_324 = lean_ctor_get(x_194, 2);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_194);
x_325 = lean_ctor_get(x_195, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_195, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_195, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_195, 3);
lean_inc(x_328);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_329 = x_195;
} else {
 lean_dec_ref(x_195);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_330, 2, x_327);
lean_ctor_set(x_330, 3, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_277);
x_331 = 0;
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_323);
lean_ctor_set(x_332, 2, x_324);
lean_ctor_set(x_332, 3, x_268);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
lean_ctor_set(x_1, 0, x_332);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
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
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint32_t x_337; uint8_t x_338; uint8_t x_339; 
x_333 = lean_ctor_get(x_1, 0);
x_334 = lean_ctor_get(x_1, 1);
x_335 = lean_ctor_get(x_1, 2);
x_336 = lean_ctor_get(x_1, 3);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_1);
x_337 = lean_unbox_uint32(x_334);
x_338 = x_2 < x_337;
x_339 = l_coeDecidableEq(x_338);
if (x_339 == 0)
{
uint32_t x_340; uint8_t x_341; uint8_t x_342; 
x_340 = lean_unbox_uint32(x_334);
x_341 = x_340 < x_2;
x_342 = l_coeDecidableEq(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_335);
lean_dec(x_334);
x_343 = lean_box_uint32(x_2);
x_344 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_344, 0, x_333);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_3);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_7);
return x_344;
}
else
{
uint8_t x_345; uint8_t x_346; 
x_345 = l_RBNode_isRed___rarg(x_336);
x_346 = l_coeDecidableEq(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_336, x_2, x_3);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_333);
lean_ctor_set(x_348, 1, x_334);
lean_ctor_set(x_348, 2, x_335);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_336, x_2, x_3);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_349, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_354 = x_349;
} else {
 lean_dec_ref(x_349);
 x_354 = lean_box(0);
}
x_355 = 0;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_351);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
x_357 = 1;
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_333);
lean_ctor_set(x_358, 1, x_334);
lean_ctor_set(x_358, 2, x_335);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
return x_358;
}
else
{
uint8_t x_359; 
x_359 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 2);
lean_inc(x_361);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_362 = x_349;
} else {
 lean_dec_ref(x_349);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_351, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_367 = x_351;
} else {
 lean_dec_ref(x_351);
 x_367 = lean_box(0);
}
x_368 = 1;
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_333);
lean_ctor_set(x_369, 1, x_334);
lean_ctor_set(x_369, 2, x_335);
lean_ctor_set(x_369, 3, x_350);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_368);
if (lean_is_scalar(x_362)) {
 x_370 = lean_alloc_ctor(1, 4, 1);
} else {
 x_370 = x_362;
}
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_364);
lean_ctor_set(x_370, 2, x_365);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_368);
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_361);
lean_ctor_set(x_371, 3, x_370);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_359);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_349, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_349, 2);
lean_inc(x_373);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_374 = x_349;
} else {
 lean_dec_ref(x_349);
 x_374 = lean_box(0);
}
x_375 = 0;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_350);
lean_ctor_set(x_376, 1, x_372);
lean_ctor_set(x_376, 2, x_373);
lean_ctor_set(x_376, 3, x_351);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
x_377 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_377, 0, x_333);
lean_ctor_set(x_377, 1, x_334);
lean_ctor_set(x_377, 2, x_335);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_359);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_379 = lean_ctor_get(x_349, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_382 = x_349;
} else {
 lean_dec_ref(x_349);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_350, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_350, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_350, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_387 = x_350;
} else {
 lean_dec_ref(x_350);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_333);
lean_ctor_set(x_389, 1, x_334);
lean_ctor_set(x_389, 2, x_335);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_384);
lean_ctor_set(x_391, 2, x_385);
lean_ctor_set(x_391, 3, x_390);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_378);
return x_391;
}
else
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_349, 3);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_349, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_349, 2);
lean_inc(x_394);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_395 = x_349;
} else {
 lean_dec_ref(x_349);
 x_395 = lean_box(0);
}
x_396 = 0;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_350);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_397, 2, x_394);
lean_ctor_set(x_397, 3, x_392);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_333);
lean_ctor_set(x_398, 1, x_334);
lean_ctor_set(x_398, 2, x_335);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_378);
return x_398;
}
else
{
uint8_t x_399; 
x_399 = lean_ctor_get_uint8(x_392, sizeof(void*)*4);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_400 = lean_ctor_get(x_349, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_349, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_402 = x_349;
} else {
 lean_dec_ref(x_349);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_392, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_392, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_392, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_392, 3);
lean_inc(x_406);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_407 = x_392;
} else {
 lean_dec_ref(x_392);
 x_407 = lean_box(0);
}
lean_inc(x_350);
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_333);
lean_ctor_set(x_408, 1, x_334);
lean_ctor_set(x_408, 2, x_335);
lean_ctor_set(x_408, 3, x_350);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_409 = x_350;
} else {
 lean_dec_ref(x_350);
 x_409 = lean_box(0);
}
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_403);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set(x_410, 2, x_405);
lean_ctor_set(x_410, 3, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_402)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_402;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_400);
lean_ctor_set(x_411, 2, x_401);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_399);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_414 = x_349;
} else {
 lean_dec_ref(x_349);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_350, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_350, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_350, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_350, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_419 = x_350;
} else {
 lean_dec_ref(x_350);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_399);
x_421 = 0;
if (lean_is_scalar(x_414)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_414;
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_412);
lean_ctor_set(x_422, 2, x_413);
lean_ctor_set(x_422, 3, x_392);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_333);
lean_ctor_set(x_423, 1, x_334);
lean_ctor_set(x_423, 2, x_335);
lean_ctor_set(x_423, 3, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_399);
return x_423;
}
}
}
}
}
}
}
else
{
uint8_t x_424; uint8_t x_425; 
x_424 = l_RBNode_isRed___rarg(x_333);
x_425 = l_coeDecidableEq(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_333, x_2, x_3);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_334);
lean_ctor_set(x_427, 2, x_335);
lean_ctor_set(x_427, 3, x_336);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_7);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_333, x_2, x_3);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 3);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 2);
lean_inc(x_432);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_433 = x_428;
} else {
 lean_dec_ref(x_428);
 x_433 = lean_box(0);
}
x_434 = 0;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_432);
lean_ctor_set(x_435, 3, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_334);
lean_ctor_set(x_437, 2, x_335);
lean_ctor_set(x_437, 3, x_336);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_430, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_430, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_430, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_430, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_446 = x_430;
} else {
 lean_dec_ref(x_430);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_429);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_334);
lean_ctor_set(x_449, 2, x_335);
lean_ctor_set(x_449, 3, x_336);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_444);
lean_ctor_set(x_450, 3, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_438);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_428, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_428, 2);
lean_inc(x_452);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_453 = x_428;
} else {
 lean_dec_ref(x_428);
 x_453 = lean_box(0);
}
x_454 = 0;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_429);
lean_ctor_set(x_455, 1, x_451);
lean_ctor_set(x_455, 2, x_452);
lean_ctor_set(x_455, 3, x_430);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_334);
lean_ctor_set(x_456, 2, x_335);
lean_ctor_set(x_456, 3, x_336);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_438);
return x_456;
}
}
}
else
{
uint8_t x_457; 
x_457 = lean_ctor_get_uint8(x_429, sizeof(void*)*4);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_458 = lean_ctor_get(x_428, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_428, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_428, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_461 = x_428;
} else {
 lean_dec_ref(x_428);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_429, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_429, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_429, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_429, 3);
lean_inc(x_465);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_466 = x_429;
} else {
 lean_dec_ref(x_429);
 x_466 = lean_box(0);
}
x_467 = 1;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_462);
lean_ctor_set(x_468, 1, x_463);
lean_ctor_set(x_468, 2, x_464);
lean_ctor_set(x_468, 3, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
if (lean_is_scalar(x_461)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_461;
}
lean_ctor_set(x_469, 0, x_460);
lean_ctor_set(x_469, 1, x_334);
lean_ctor_set(x_469, 2, x_335);
lean_ctor_set(x_469, 3, x_336);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_467);
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_458);
lean_ctor_set(x_470, 2, x_459);
lean_ctor_set(x_470, 3, x_469);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_457);
return x_470;
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_428, 3);
lean_inc(x_471);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_472 = lean_ctor_get(x_428, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_428, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_474 = x_428;
} else {
 lean_dec_ref(x_428);
 x_474 = lean_box(0);
}
x_475 = 0;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_474;
}
lean_ctor_set(x_476, 0, x_429);
lean_ctor_set(x_476, 1, x_472);
lean_ctor_set(x_476, 2, x_473);
lean_ctor_set(x_476, 3, x_471);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_334);
lean_ctor_set(x_477, 2, x_335);
lean_ctor_set(x_477, 3, x_336);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_457);
return x_477;
}
else
{
uint8_t x_478; 
x_478 = lean_ctor_get_uint8(x_471, sizeof(void*)*4);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_428, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_428, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_481 = x_428;
} else {
 lean_dec_ref(x_428);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_471, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_471, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_471, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_471, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 x_486 = x_471;
} else {
 lean_dec_ref(x_471);
 x_486 = lean_box(0);
}
lean_inc(x_429);
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_429);
lean_ctor_set(x_487, 1, x_479);
lean_ctor_set(x_487, 2, x_480);
lean_ctor_set(x_487, 3, x_482);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_488 = x_429;
} else {
 lean_dec_ref(x_429);
 x_488 = lean_box(0);
}
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_334);
lean_ctor_set(x_489, 2, x_335);
lean_ctor_set(x_489, 3, x_336);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_481)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_481;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_483);
lean_ctor_set(x_490, 2, x_484);
lean_ctor_set(x_490, 3, x_489);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_478);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_491 = lean_ctor_get(x_428, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_428, 2);
lean_inc(x_492);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_493 = x_428;
} else {
 lean_dec_ref(x_428);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_429, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_429, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_429, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_429, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_498 = x_429;
} else {
 lean_dec_ref(x_429);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_495);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_497);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_478);
x_500 = 0;
if (lean_is_scalar(x_493)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_493;
}
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_491);
lean_ctor_set(x_501, 2, x_492);
lean_ctor_set(x_501, 3, x_471);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_334);
lean_ctor_set(x_502, 2, x_335);
lean_ctor_set(x_502, 3, x_336);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_478);
return x_502;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = lean_box_uint32(x_2);
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_unbox_uint32(x_10);
x_17 = x_16 < x_2;
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
x_19 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
else
{
lean_object* x_20; 
x_20 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_20);
return x_1;
}
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_26 = lean_unbox_uint32(x_23);
x_27 = x_2 < x_26;
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; uint8_t x_31; 
x_29 = lean_unbox_uint32(x_23);
x_30 = x_29 < x_2;
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_box_uint32(x_2);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_25, x_2, x_3);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_22, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_1, 1);
x_41 = lean_ctor_get(x_1, 2);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_unbox_uint32(x_40);
x_44 = x_2 < x_43;
x_45 = l_coeDecidableEq(x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; uint8_t x_48; 
x_46 = lean_unbox_uint32(x_40);
x_47 = x_46 < x_2;
x_48 = l_coeDecidableEq(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_40);
x_49 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_49);
return x_1;
}
else
{
uint8_t x_50; uint8_t x_51; 
x_50 = l_RBNode_isRed___rarg(x_42);
x_51 = l_coeDecidableEq(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_42, x_2, x_3);
lean_ctor_set(x_1, 3, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_42, x_2, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 3);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_53, 0);
lean_dec(x_58);
x_59 = 0;
lean_ctor_set(x_53, 0, x_55);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_59);
x_60 = 1;
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_60);
return x_1;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_53, 1);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = 0;
x_64 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = 1;
lean_ctor_set(x_1, 3, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
}
else
{
uint8_t x_66; 
x_66 = lean_ctor_get_uint8(x_55, sizeof(void*)*4);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_ctor_get(x_53, 2);
x_70 = lean_ctor_get(x_53, 3);
lean_dec(x_70);
x_71 = lean_ctor_get(x_53, 0);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_55);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
x_75 = lean_ctor_get(x_55, 2);
x_76 = lean_ctor_get(x_55, 3);
x_77 = 1;
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_77);
lean_ctor_set(x_53, 3, x_76);
lean_ctor_set(x_53, 2, x_75);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_73);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_77);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_55, 0);
x_79 = lean_ctor_get(x_55, 1);
x_80 = lean_ctor_get(x_55, 2);
x_81 = lean_ctor_get(x_55, 3);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_55);
x_82 = 1;
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_40);
lean_ctor_set(x_83, 2, x_41);
lean_ctor_set(x_83, 3, x_54);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
lean_ctor_set(x_53, 3, x_81);
lean_ctor_set(x_53, 2, x_80);
lean_ctor_set(x_53, 1, x_79);
lean_ctor_set(x_53, 0, x_78);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_82);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_69);
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_53, 1);
x_85 = lean_ctor_get(x_53, 2);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_ctor_get(x_55, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_55, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_55, 3);
lean_inc(x_89);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_90 = x_55;
} else {
 lean_dec_ref(x_55);
 x_90 = lean_box(0);
}
x_91 = 1;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(1, 4, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_39);
lean_ctor_set(x_92, 1, x_40);
lean_ctor_set(x_92, 2, x_41);
lean_ctor_set(x_92, 3, x_54);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_91);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_91);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_85);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_92);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_53, 3);
lean_dec(x_95);
x_96 = lean_ctor_get(x_53, 0);
lean_dec(x_96);
x_97 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_97);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_53, 1);
x_99 = lean_ctor_get(x_53, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_53);
x_100 = 0;
x_101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_101, 0, x_54);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_55);
lean_ctor_set_uint8(x_101, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_101);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_66);
return x_1;
}
}
}
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_54, sizeof(void*)*4);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_53);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_53, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_54);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_54, 0);
x_107 = lean_ctor_get(x_54, 1);
x_108 = lean_ctor_get(x_54, 2);
x_109 = lean_ctor_get(x_54, 3);
x_110 = 1;
lean_ctor_set(x_54, 3, x_106);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_110);
lean_ctor_set(x_53, 0, x_109);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_110);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_108);
lean_ctor_set(x_1, 1, x_107);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_54, 0);
x_112 = lean_ctor_get(x_54, 1);
x_113 = lean_ctor_get(x_54, 2);
x_114 = lean_ctor_get(x_54, 3);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_54);
x_115 = 1;
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_39);
lean_ctor_set(x_116, 1, x_40);
lean_ctor_set(x_116, 2, x_41);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
lean_ctor_set(x_53, 0, x_114);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set(x_1, 2, x_113);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_53, 1);
x_118 = lean_ctor_get(x_53, 2);
x_119 = lean_ctor_get(x_53, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_53);
x_120 = lean_ctor_get(x_54, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_54, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_54, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_54, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_124 = x_54;
} else {
 lean_dec_ref(x_54);
 x_124 = lean_box(0);
}
x_125 = 1;
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 4, 1);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_40);
lean_ctor_set(x_126, 2, x_41);
lean_ctor_set(x_126, 3, x_120);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_117);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_127);
lean_ctor_set(x_1, 2, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_53, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_53);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_53, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_53, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_132);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_53, 1);
x_134 = lean_ctor_get(x_53, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_53);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_54);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_128);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_102);
return x_1;
}
}
else
{
uint8_t x_137; 
x_137 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_137 == 0)
{
uint8_t x_138; 
lean_free_object(x_1);
x_138 = !lean_is_exclusive(x_53);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_53, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_53, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_128);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_ctor_get(x_128, 0);
x_143 = lean_ctor_get(x_128, 1);
x_144 = lean_ctor_get(x_128, 2);
x_145 = lean_ctor_get(x_128, 3);
lean_inc(x_54);
lean_ctor_set(x_128, 3, x_54);
lean_ctor_set(x_128, 2, x_41);
lean_ctor_set(x_128, 1, x_40);
lean_ctor_set(x_128, 0, x_39);
x_146 = !lean_is_exclusive(x_54);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_54, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_54, 2);
lean_dec(x_148);
x_149 = lean_ctor_get(x_54, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_54, 0);
lean_dec(x_150);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
lean_ctor_set(x_54, 3, x_145);
lean_ctor_set(x_54, 2, x_144);
lean_ctor_set(x_54, 1, x_143);
lean_ctor_set(x_54, 0, x_142);
lean_ctor_set(x_53, 3, x_54);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
else
{
lean_object* x_151; 
lean_dec(x_54);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_102);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_145);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_151);
lean_ctor_set(x_53, 0, x_128);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_128, 0);
x_153 = lean_ctor_get(x_128, 1);
x_154 = lean_ctor_get(x_128, 2);
x_155 = lean_ctor_get(x_128, 3);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_128);
lean_inc(x_54);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_39);
lean_ctor_set(x_156, 1, x_40);
lean_ctor_set(x_156, 2, x_41);
lean_ctor_set(x_156, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_157 = x_54;
} else {
 lean_dec_ref(x_54);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set(x_158, 2, x_154);
lean_ctor_set(x_158, 3, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_102);
lean_ctor_set(x_53, 3, x_158);
lean_ctor_set(x_53, 0, x_156);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_137);
return x_53;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_159 = lean_ctor_get(x_53, 1);
x_160 = lean_ctor_get(x_53, 2);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_53);
x_161 = lean_ctor_get(x_128, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_128, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_128, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_128, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_165 = x_128;
} else {
 lean_dec_ref(x_128);
 x_165 = lean_box(0);
}
lean_inc(x_54);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_39);
lean_ctor_set(x_166, 1, x_40);
lean_ctor_set(x_166, 2, x_41);
lean_ctor_set(x_166, 3, x_54);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_167 = x_54;
} else {
 lean_dec_ref(x_54);
 x_167 = lean_box(0);
}
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_102);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_102);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set(x_169, 2, x_160);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_137);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_53);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_53, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_53, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_54);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_137);
x_174 = 0;
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_174);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_54, 0);
x_176 = lean_ctor_get(x_54, 1);
x_177 = lean_ctor_get(x_54, 2);
x_178 = lean_ctor_get(x_54, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_54);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_137);
x_180 = 0;
lean_ctor_set(x_53, 0, x_179);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_180);
lean_ctor_set(x_1, 3, x_53);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_181 = lean_ctor_get(x_53, 1);
x_182 = lean_ctor_get(x_53, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_53);
x_183 = lean_ctor_get(x_54, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_54, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_54, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_54, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_187 = x_54;
} else {
 lean_dec_ref(x_54);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_137);
x_189 = 0;
x_190 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_128);
lean_ctor_set_uint8(x_190, sizeof(void*)*4, x_189);
lean_ctor_set(x_1, 3, x_190);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
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
uint8_t x_191; uint8_t x_192; 
x_191 = l_RBNode_isRed___rarg(x_39);
x_192 = l_coeDecidableEq(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_39, x_2, x_3);
lean_ctor_set(x_1, 0, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_39, x_2, x_3);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_194, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_198 = lean_ctor_get(x_194, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_194, 0);
lean_dec(x_199);
x_200 = 0;
lean_ctor_set(x_194, 0, x_196);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_200);
x_201 = 1;
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_194, 1);
x_203 = lean_ctor_get(x_194, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_194);
x_204 = 0;
x_205 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_205, 0, x_196);
lean_ctor_set(x_205, 1, x_202);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_196);
lean_ctor_set_uint8(x_205, sizeof(void*)*4, x_204);
x_206 = 1;
lean_ctor_set(x_1, 0, x_205);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_206);
return x_1;
}
}
else
{
uint8_t x_207; 
x_207 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_194, 1);
x_210 = lean_ctor_get(x_194, 2);
x_211 = lean_ctor_get(x_194, 3);
lean_dec(x_211);
x_212 = lean_ctor_get(x_194, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_196);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_196, 0);
x_215 = lean_ctor_get(x_196, 1);
x_216 = lean_ctor_get(x_196, 2);
x_217 = lean_ctor_get(x_196, 3);
x_218 = 1;
lean_ctor_set(x_196, 3, x_214);
lean_ctor_set(x_196, 2, x_210);
lean_ctor_set(x_196, 1, x_209);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_218);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_217);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_218);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_216);
lean_ctor_set(x_1, 1, x_215);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_196, 0);
x_220 = lean_ctor_get(x_196, 1);
x_221 = lean_ctor_get(x_196, 2);
x_222 = lean_ctor_get(x_196, 3);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_196);
x_223 = 1;
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_195);
lean_ctor_set(x_224, 1, x_209);
lean_ctor_set(x_224, 2, x_210);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_223);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_222);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_223);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_224);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; 
x_225 = lean_ctor_get(x_194, 1);
x_226 = lean_ctor_get(x_194, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_194);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_40);
lean_ctor_set(x_234, 2, x_41);
lean_ctor_set(x_234, 3, x_42);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_194);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_194, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 0);
lean_dec(x_237);
x_238 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_238);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_194, 1);
x_240 = lean_ctor_get(x_194, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_194);
x_241 = 0;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_195);
lean_ctor_set(x_242, 1, x_239);
lean_ctor_set(x_242, 2, x_240);
lean_ctor_set(x_242, 3, x_196);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_242);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_207);
return x_1;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_194);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_194, 1);
x_246 = lean_ctor_get(x_194, 2);
x_247 = lean_ctor_get(x_194, 3);
x_248 = lean_ctor_get(x_194, 0);
lean_dec(x_248);
x_249 = !lean_is_exclusive(x_195);
if (x_249 == 0)
{
uint8_t x_250; 
x_250 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_250);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_250);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_195, 0);
x_252 = lean_ctor_get(x_195, 1);
x_253 = lean_ctor_get(x_195, 2);
x_254 = lean_ctor_get(x_195, 3);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_195);
x_255 = 1;
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
lean_ctor_set(x_194, 3, x_42);
lean_ctor_set(x_194, 2, x_41);
lean_ctor_set(x_194, 1, x_40);
lean_ctor_set(x_194, 0, x_247);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_194);
lean_ctor_set(x_1, 2, x_246);
lean_ctor_set(x_1, 1, x_245);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; 
x_257 = lean_ctor_get(x_194, 1);
x_258 = lean_ctor_get(x_194, 2);
x_259 = lean_ctor_get(x_194, 3);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_194);
x_260 = lean_ctor_get(x_195, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_195, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_195, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_195, 3);
lean_inc(x_263);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_264 = x_195;
} else {
 lean_dec_ref(x_195);
 x_264 = lean_box(0);
}
x_265 = 1;
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(1, 4, 1);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_260);
lean_ctor_set(x_266, 1, x_261);
lean_ctor_set(x_266, 2, x_262);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
x_267 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_40);
lean_ctor_set(x_267, 2, x_41);
lean_ctor_set(x_267, 3, x_42);
lean_ctor_set_uint8(x_267, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 3, x_267);
lean_ctor_set(x_1, 2, x_258);
lean_ctor_set(x_1, 1, x_257);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_194, 3);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_194);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_194, 3);
lean_dec(x_270);
x_271 = lean_ctor_get(x_194, 0);
lean_dec(x_271);
x_272 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_272);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_194, 1);
x_274 = lean_ctor_get(x_194, 2);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_194);
x_275 = 0;
x_276 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_276, 0, x_195);
lean_ctor_set(x_276, 1, x_273);
lean_ctor_set(x_276, 2, x_274);
lean_ctor_set(x_276, 3, x_268);
lean_ctor_set_uint8(x_276, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_276);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_243);
return x_1;
}
}
else
{
uint8_t x_277; 
x_277 = lean_ctor_get_uint8(x_268, sizeof(void*)*4);
if (x_277 == 0)
{
uint8_t x_278; 
lean_free_object(x_1);
x_278 = !lean_is_exclusive(x_194);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_279 = lean_ctor_get(x_194, 1);
x_280 = lean_ctor_get(x_194, 2);
x_281 = lean_ctor_get(x_194, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_194, 0);
lean_dec(x_282);
x_283 = !lean_is_exclusive(x_268);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_268, 0);
x_285 = lean_ctor_get(x_268, 1);
x_286 = lean_ctor_get(x_268, 2);
x_287 = lean_ctor_get(x_268, 3);
lean_inc(x_195);
lean_ctor_set(x_268, 3, x_284);
lean_ctor_set(x_268, 2, x_280);
lean_ctor_set(x_268, 1, x_279);
lean_ctor_set(x_268, 0, x_195);
x_288 = !lean_is_exclusive(x_195);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_195, 3);
lean_dec(x_289);
x_290 = lean_ctor_get(x_195, 2);
lean_dec(x_290);
x_291 = lean_ctor_get(x_195, 1);
lean_dec(x_291);
x_292 = lean_ctor_get(x_195, 0);
lean_dec(x_292);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
lean_ctor_set(x_195, 3, x_42);
lean_ctor_set(x_195, 2, x_41);
lean_ctor_set(x_195, 1, x_40);
lean_ctor_set(x_195, 0, x_287);
lean_ctor_set(x_194, 3, x_195);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
else
{
lean_object* x_293; 
lean_dec(x_195);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_243);
x_293 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_40);
lean_ctor_set(x_293, 2, x_41);
lean_ctor_set(x_293, 3, x_42);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_293);
lean_ctor_set(x_194, 2, x_286);
lean_ctor_set(x_194, 1, x_285);
lean_ctor_set(x_194, 0, x_268);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_294 = lean_ctor_get(x_268, 0);
x_295 = lean_ctor_get(x_268, 1);
x_296 = lean_ctor_get(x_268, 2);
x_297 = lean_ctor_get(x_268, 3);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_268);
lean_inc(x_195);
x_298 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_298, 0, x_195);
lean_ctor_set(x_298, 1, x_279);
lean_ctor_set(x_298, 2, x_280);
lean_ctor_set(x_298, 3, x_294);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_299 = x_195;
} else {
 lean_dec_ref(x_195);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_40);
lean_ctor_set(x_300, 2, x_41);
lean_ctor_set(x_300, 3, x_42);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_243);
lean_ctor_set(x_194, 3, x_300);
lean_ctor_set(x_194, 2, x_296);
lean_ctor_set(x_194, 1, x_295);
lean_ctor_set(x_194, 0, x_298);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_277);
return x_194;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_301 = lean_ctor_get(x_194, 1);
x_302 = lean_ctor_get(x_194, 2);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_194);
x_303 = lean_ctor_get(x_268, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_268, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_268, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_268, 3);
lean_inc(x_306);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_307 = x_268;
} else {
 lean_dec_ref(x_268);
 x_307 = lean_box(0);
}
lean_inc(x_195);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_195);
lean_ctor_set(x_308, 1, x_301);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_303);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_309 = x_195;
} else {
 lean_dec_ref(x_195);
 x_309 = lean_box(0);
}
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_243);
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 4, 1);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_40);
lean_ctor_set(x_310, 2, x_41);
lean_ctor_set(x_310, 3, x_42);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_243);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_277);
return x_311;
}
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_194);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_ctor_get(x_194, 3);
lean_dec(x_313);
x_314 = lean_ctor_get(x_194, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_195);
if (x_315 == 0)
{
uint8_t x_316; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_277);
x_316 = 0;
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_316);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_317 = lean_ctor_get(x_195, 0);
x_318 = lean_ctor_get(x_195, 1);
x_319 = lean_ctor_get(x_195, 2);
x_320 = lean_ctor_get(x_195, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_195);
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_317);
lean_ctor_set(x_321, 1, x_318);
lean_ctor_set(x_321, 2, x_319);
lean_ctor_set(x_321, 3, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_277);
x_322 = 0;
lean_ctor_set(x_194, 0, x_321);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_322);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
return x_1;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; 
x_323 = lean_ctor_get(x_194, 1);
x_324 = lean_ctor_get(x_194, 2);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_194);
x_325 = lean_ctor_get(x_195, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_195, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_195, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_195, 3);
lean_inc(x_328);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_329 = x_195;
} else {
 lean_dec_ref(x_195);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 4, 1);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_325);
lean_ctor_set(x_330, 1, x_326);
lean_ctor_set(x_330, 2, x_327);
lean_ctor_set(x_330, 3, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_277);
x_331 = 0;
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_323);
lean_ctor_set(x_332, 2, x_324);
lean_ctor_set(x_332, 3, x_268);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_331);
lean_ctor_set(x_1, 0, x_332);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_277);
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
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint32_t x_337; uint8_t x_338; uint8_t x_339; 
x_333 = lean_ctor_get(x_1, 0);
x_334 = lean_ctor_get(x_1, 1);
x_335 = lean_ctor_get(x_1, 2);
x_336 = lean_ctor_get(x_1, 3);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_1);
x_337 = lean_unbox_uint32(x_334);
x_338 = x_2 < x_337;
x_339 = l_coeDecidableEq(x_338);
if (x_339 == 0)
{
uint32_t x_340; uint8_t x_341; uint8_t x_342; 
x_340 = lean_unbox_uint32(x_334);
x_341 = x_340 < x_2;
x_342 = l_coeDecidableEq(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_335);
lean_dec(x_334);
x_343 = lean_box_uint32(x_2);
x_344 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_344, 0, x_333);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_3);
lean_ctor_set(x_344, 3, x_336);
lean_ctor_set_uint8(x_344, sizeof(void*)*4, x_7);
return x_344;
}
else
{
uint8_t x_345; uint8_t x_346; 
x_345 = l_RBNode_isRed___rarg(x_336);
x_346 = l_coeDecidableEq(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_336, x_2, x_3);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_333);
lean_ctor_set(x_348, 1, x_334);
lean_ctor_set(x_348, 2, x_335);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_336, x_2, x_3);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_349, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; 
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_354 = x_349;
} else {
 lean_dec_ref(x_349);
 x_354 = lean_box(0);
}
x_355 = 0;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_351);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
x_357 = 1;
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_333);
lean_ctor_set(x_358, 1, x_334);
lean_ctor_set(x_358, 2, x_335);
lean_ctor_set(x_358, 3, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
return x_358;
}
else
{
uint8_t x_359; 
x_359 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 2);
lean_inc(x_361);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_362 = x_349;
} else {
 lean_dec_ref(x_349);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_351, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_351, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_367 = x_351;
} else {
 lean_dec_ref(x_351);
 x_367 = lean_box(0);
}
x_368 = 1;
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_333);
lean_ctor_set(x_369, 1, x_334);
lean_ctor_set(x_369, 2, x_335);
lean_ctor_set(x_369, 3, x_350);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_368);
if (lean_is_scalar(x_362)) {
 x_370 = lean_alloc_ctor(1, 4, 1);
} else {
 x_370 = x_362;
}
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_364);
lean_ctor_set(x_370, 2, x_365);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_368);
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_360);
lean_ctor_set(x_371, 2, x_361);
lean_ctor_set(x_371, 3, x_370);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_359);
return x_371;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_349, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_349, 2);
lean_inc(x_373);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_374 = x_349;
} else {
 lean_dec_ref(x_349);
 x_374 = lean_box(0);
}
x_375 = 0;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_350);
lean_ctor_set(x_376, 1, x_372);
lean_ctor_set(x_376, 2, x_373);
lean_ctor_set(x_376, 3, x_351);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
x_377 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_377, 0, x_333);
lean_ctor_set(x_377, 1, x_334);
lean_ctor_set(x_377, 2, x_335);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_359);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_379 = lean_ctor_get(x_349, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_382 = x_349;
} else {
 lean_dec_ref(x_349);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_350, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_350, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_350, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_387 = x_350;
} else {
 lean_dec_ref(x_350);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_333);
lean_ctor_set(x_389, 1, x_334);
lean_ctor_set(x_389, 2, x_335);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_384);
lean_ctor_set(x_391, 2, x_385);
lean_ctor_set(x_391, 3, x_390);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_378);
return x_391;
}
else
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_349, 3);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_349, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_349, 2);
lean_inc(x_394);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_395 = x_349;
} else {
 lean_dec_ref(x_349);
 x_395 = lean_box(0);
}
x_396 = 0;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_350);
lean_ctor_set(x_397, 1, x_393);
lean_ctor_set(x_397, 2, x_394);
lean_ctor_set(x_397, 3, x_392);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_333);
lean_ctor_set(x_398, 1, x_334);
lean_ctor_set(x_398, 2, x_335);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_378);
return x_398;
}
else
{
uint8_t x_399; 
x_399 = lean_ctor_get_uint8(x_392, sizeof(void*)*4);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_400 = lean_ctor_get(x_349, 1);
lean_inc(x_400);
x_401 = lean_ctor_get(x_349, 2);
lean_inc(x_401);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_402 = x_349;
} else {
 lean_dec_ref(x_349);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_392, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_392, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_392, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_392, 3);
lean_inc(x_406);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 x_407 = x_392;
} else {
 lean_dec_ref(x_392);
 x_407 = lean_box(0);
}
lean_inc(x_350);
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_333);
lean_ctor_set(x_408, 1, x_334);
lean_ctor_set(x_408, 2, x_335);
lean_ctor_set(x_408, 3, x_350);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_409 = x_350;
} else {
 lean_dec_ref(x_350);
 x_409 = lean_box(0);
}
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 4, 1);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_403);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set(x_410, 2, x_405);
lean_ctor_set(x_410, 3, x_406);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_378);
if (lean_is_scalar(x_402)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_402;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_400);
lean_ctor_set(x_411, 2, x_401);
lean_ctor_set(x_411, 3, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_399);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_414 = x_349;
} else {
 lean_dec_ref(x_349);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_350, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_350, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_350, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_350, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_419 = x_350;
} else {
 lean_dec_ref(x_350);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_399);
x_421 = 0;
if (lean_is_scalar(x_414)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_414;
}
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_412);
lean_ctor_set(x_422, 2, x_413);
lean_ctor_set(x_422, 3, x_392);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_333);
lean_ctor_set(x_423, 1, x_334);
lean_ctor_set(x_423, 2, x_335);
lean_ctor_set(x_423, 3, x_422);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_399);
return x_423;
}
}
}
}
}
}
}
else
{
uint8_t x_424; uint8_t x_425; 
x_424 = l_RBNode_isRed___rarg(x_333);
x_425 = l_coeDecidableEq(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; 
x_426 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_333, x_2, x_3);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_334);
lean_ctor_set(x_427, 2, x_335);
lean_ctor_set(x_427, 3, x_336);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_7);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_333, x_2, x_3);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 3);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_428, 2);
lean_inc(x_432);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_433 = x_428;
} else {
 lean_dec_ref(x_428);
 x_433 = lean_box(0);
}
x_434 = 0;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_430);
lean_ctor_set(x_435, 1, x_431);
lean_ctor_set(x_435, 2, x_432);
lean_ctor_set(x_435, 3, x_430);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_334);
lean_ctor_set(x_437, 2, x_335);
lean_ctor_set(x_437, 3, x_336);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_430, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_430, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_430, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_430, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_446 = x_430;
} else {
 lean_dec_ref(x_430);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_429);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_334);
lean_ctor_set(x_449, 2, x_335);
lean_ctor_set(x_449, 3, x_336);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_443);
lean_ctor_set(x_450, 2, x_444);
lean_ctor_set(x_450, 3, x_449);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_438);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; 
x_451 = lean_ctor_get(x_428, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_428, 2);
lean_inc(x_452);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_453 = x_428;
} else {
 lean_dec_ref(x_428);
 x_453 = lean_box(0);
}
x_454 = 0;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_429);
lean_ctor_set(x_455, 1, x_451);
lean_ctor_set(x_455, 2, x_452);
lean_ctor_set(x_455, 3, x_430);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_334);
lean_ctor_set(x_456, 2, x_335);
lean_ctor_set(x_456, 3, x_336);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_438);
return x_456;
}
}
}
else
{
uint8_t x_457; 
x_457 = lean_ctor_get_uint8(x_429, sizeof(void*)*4);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_458 = lean_ctor_get(x_428, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_428, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_428, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_461 = x_428;
} else {
 lean_dec_ref(x_428);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_429, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_429, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_429, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_429, 3);
lean_inc(x_465);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_466 = x_429;
} else {
 lean_dec_ref(x_429);
 x_466 = lean_box(0);
}
x_467 = 1;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_462);
lean_ctor_set(x_468, 1, x_463);
lean_ctor_set(x_468, 2, x_464);
lean_ctor_set(x_468, 3, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_467);
if (lean_is_scalar(x_461)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_461;
}
lean_ctor_set(x_469, 0, x_460);
lean_ctor_set(x_469, 1, x_334);
lean_ctor_set(x_469, 2, x_335);
lean_ctor_set(x_469, 3, x_336);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_467);
x_470 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_458);
lean_ctor_set(x_470, 2, x_459);
lean_ctor_set(x_470, 3, x_469);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_457);
return x_470;
}
else
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_428, 3);
lean_inc(x_471);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; lean_object* x_476; lean_object* x_477; 
x_472 = lean_ctor_get(x_428, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_428, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_474 = x_428;
} else {
 lean_dec_ref(x_428);
 x_474 = lean_box(0);
}
x_475 = 0;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_474;
}
lean_ctor_set(x_476, 0, x_429);
lean_ctor_set(x_476, 1, x_472);
lean_ctor_set(x_476, 2, x_473);
lean_ctor_set(x_476, 3, x_471);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_475);
x_477 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_334);
lean_ctor_set(x_477, 2, x_335);
lean_ctor_set(x_477, 3, x_336);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_457);
return x_477;
}
else
{
uint8_t x_478; 
x_478 = lean_ctor_get_uint8(x_471, sizeof(void*)*4);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_428, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_428, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_481 = x_428;
} else {
 lean_dec_ref(x_428);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_471, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_471, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_471, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_471, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 lean_ctor_release(x_471, 2);
 lean_ctor_release(x_471, 3);
 x_486 = x_471;
} else {
 lean_dec_ref(x_471);
 x_486 = lean_box(0);
}
lean_inc(x_429);
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_429);
lean_ctor_set(x_487, 1, x_479);
lean_ctor_set(x_487, 2, x_480);
lean_ctor_set(x_487, 3, x_482);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_488 = x_429;
} else {
 lean_dec_ref(x_429);
 x_488 = lean_box(0);
}
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_485);
lean_ctor_set(x_489, 1, x_334);
lean_ctor_set(x_489, 2, x_335);
lean_ctor_set(x_489, 3, x_336);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_457);
if (lean_is_scalar(x_481)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_481;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_483);
lean_ctor_set(x_490, 2, x_484);
lean_ctor_set(x_490, 3, x_489);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_478);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; lean_object* x_502; 
x_491 = lean_ctor_get(x_428, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_428, 2);
lean_inc(x_492);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_493 = x_428;
} else {
 lean_dec_ref(x_428);
 x_493 = lean_box(0);
}
x_494 = lean_ctor_get(x_429, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_429, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_429, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_429, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_498 = x_429;
} else {
 lean_dec_ref(x_429);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(1, 4, 1);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_495);
lean_ctor_set(x_499, 2, x_496);
lean_ctor_set(x_499, 3, x_497);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_478);
x_500 = 0;
if (lean_is_scalar(x_493)) {
 x_501 = lean_alloc_ctor(1, 4, 1);
} else {
 x_501 = x_493;
}
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_491);
lean_ctor_set(x_501, 2, x_492);
lean_ctor_set(x_501, 3, x_471);
lean_ctor_set_uint8(x_501, sizeof(void*)*4, x_500);
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_334);
lean_ctor_set(x_502, 2, x_335);
lean_ctor_set(x_502, 3, x_336);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_478);
return x_502;
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
uint8_t x_4; uint8_t x_5; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__6___rarg(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___at___private_Init_Lean_Data_Trie_2__insertAux___main___spec__7___rarg(x_1, x_2, x_3);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; 
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
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_4);
x_11 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_12 = x_11 < x_2;
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; 
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
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_4);
x_11 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_12 = x_11 < x_2;
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
return x_14;
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 0;
lean_inc(x_2);
lean_inc(x_6);
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
x_9 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Data_Trie_6__toStringAux___main___spec__1(x_4, x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
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
