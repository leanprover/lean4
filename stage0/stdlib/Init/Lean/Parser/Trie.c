// Lean compiler output
// Module: Init.Lean.Parser.Trie
// Imports: Init.Data.RBMap Init.Lean.Format
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
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1(lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_HasEmptyc(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_HasToString___rarg(lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___main(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main(lean_object*);
lean_object* l_Lean_Parser_Trie_empty(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg(lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(lean_object*, uint32_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1(lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_find___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_HasEmptyc___closed__1;
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg(lean_object*, uint32_t, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7(lean_object*);
lean_object* l_Lean_Parser_Trie_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1(lean_object*);
lean_object* l_Lean_Parser_Trie_matchPrefix(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5(lean_object*);
lean_object* l_Lean_Parser_Trie_find___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_find(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux(lean_object*);
lean_object* l_Lean_Parser_Trie_HasToString(lean_object*);
lean_object* l_Lean_Parser_Trie_Inhabited(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc(lean_object*);
lean_object* l_Lean_Parser_Trie_insert___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg(lean_object*, uint32_t);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_empty___closed__1;
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux(lean_object*);
lean_object* l_Char_quoteCore(uint32_t);
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Trie_insert(lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___rarg(lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_singleton___rarg(lean_object*, lean_object*);
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
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_string_utf8_at_end(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_6);
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
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
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
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_4);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_13 = x_12 < x_2;
x_14 = l_Bool_DecidableEq(x_13, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
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
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_unbox_uint32(x_10);
x_18 = x_17 < x_2;
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_21);
return x_1;
}
}
else
{
lean_object* x_22; 
x_22 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_27 = lean_unbox_uint32(x_24);
x_28 = x_2 < x_27;
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_unbox_uint32(x_24);
x_32 = x_31 < x_2;
x_33 = l_Bool_DecidableEq(x_32, x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_24);
x_34 = lean_box_uint32(x_2);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_26, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_23, x_2, x_3);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_7);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_unbox_uint32(x_42);
x_46 = x_2 < x_45;
x_47 = 1;
x_48 = l_Bool_DecidableEq(x_46, x_47);
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_unbox_uint32(x_42);
x_50 = x_49 < x_2;
x_51 = l_Bool_DecidableEq(x_50, x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_42);
x_52 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_52);
return x_1;
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = l_RBNode_isRed___rarg(x_44);
x_54 = l_Bool_DecidableEq(x_53, x_47);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_44, x_2, x_3);
lean_ctor_set(x_1, 3, x_55);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_44, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = 0;
lean_ctor_set(x_56, 0, x_58);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_62);
x_63 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_63);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_56, 1);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = 0;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = 1;
lean_ctor_set(x_1, 3, x_67);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_68);
return x_1;
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_56, 1);
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_56, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
x_78 = lean_ctor_get(x_58, 2);
x_79 = lean_ctor_get(x_58, 3);
x_80 = 1;
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_80);
lean_ctor_set(x_56, 3, x_79);
lean_ctor_set(x_56, 2, x_78);
lean_ctor_set(x_56, 1, x_77);
lean_ctor_set(x_56, 0, x_76);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_58);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
x_83 = lean_ctor_get(x_58, 2);
x_84 = lean_ctor_get(x_58, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_85 = 1;
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_41);
lean_ctor_set(x_86, 1, x_42);
lean_ctor_set(x_86, 2, x_43);
lean_ctor_set(x_86, 3, x_57);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
lean_ctor_set(x_56, 3, x_84);
lean_ctor_set(x_56, 2, x_83);
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_81);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_85);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_56, 1);
x_88 = lean_ctor_get(x_56, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_56);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_58, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_58, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_93 = x_58;
} else {
 lean_dec_ref(x_58);
 x_93 = lean_box(0);
}
x_94 = 1;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(1, 4, 1);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_41);
lean_ctor_set(x_95, 1, x_42);
lean_ctor_set(x_95, 2, x_43);
lean_ctor_set(x_95, 3, x_57);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_94);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_94);
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set(x_1, 2, x_88);
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_56);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_56, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_56, 0);
lean_dec(x_99);
x_100 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_56, 1);
x_102 = lean_ctor_get(x_56, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = 0;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_57);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_102);
lean_ctor_set(x_104, 3, x_58);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_104);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
}
}
else
{
uint8_t x_105; 
x_105 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_56);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_56, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_57);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_57, 0);
x_110 = lean_ctor_get(x_57, 1);
x_111 = lean_ctor_get(x_57, 2);
x_112 = lean_ctor_get(x_57, 3);
x_113 = 1;
lean_ctor_set(x_57, 3, x_109);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 1, x_42);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_113);
lean_ctor_set(x_56, 0, x_112);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_113);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_57, 0);
x_115 = lean_ctor_get(x_57, 1);
x_116 = lean_ctor_get(x_57, 2);
x_117 = lean_ctor_get(x_57, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_57);
x_118 = 1;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_41);
lean_ctor_set(x_119, 1, x_42);
lean_ctor_set(x_119, 2, x_43);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_56, 0, x_117);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_116);
lean_ctor_set(x_1, 1, x_115);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_56, 1);
x_121 = lean_ctor_get(x_56, 2);
x_122 = lean_ctor_get(x_56, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_56);
x_123 = lean_ctor_get(x_57, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_57, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_57, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_57, 3);
lean_inc(x_126);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_127 = x_57;
} else {
 lean_dec_ref(x_57);
 x_127 = lean_box(0);
}
x_128 = 1;
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_41);
lean_ctor_set(x_129, 1, x_42);
lean_ctor_set(x_129, 2, x_43);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_130);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_56, 3);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_56);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_56, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_56, 0);
lean_dec(x_134);
x_135 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_56, 1);
x_137 = lean_ctor_get(x_56, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_56);
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_57);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_131);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_131, sizeof(void*)*4);
if (x_140 == 0)
{
uint8_t x_141; 
lean_free_object(x_1);
x_141 = !lean_is_exclusive(x_56);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_56, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_56, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
x_147 = lean_ctor_get(x_131, 2);
x_148 = lean_ctor_get(x_131, 3);
lean_inc(x_57);
lean_ctor_set(x_131, 3, x_57);
lean_ctor_set(x_131, 2, x_43);
lean_ctor_set(x_131, 1, x_42);
lean_ctor_set(x_131, 0, x_41);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_57, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_57, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_57, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_57, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
lean_ctor_set(x_57, 3, x_148);
lean_ctor_set(x_57, 2, x_147);
lean_ctor_set(x_57, 1, x_146);
lean_ctor_set(x_57, 0, x_145);
lean_ctor_set(x_56, 3, x_57);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
else
{
lean_object* x_154; 
lean_dec(x_57);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_154);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_131, 0);
x_156 = lean_ctor_get(x_131, 1);
x_157 = lean_ctor_get(x_131, 2);
x_158 = lean_ctor_get(x_131, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_131);
lean_inc(x_57);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_41);
lean_ctor_set(x_159, 1, x_42);
lean_ctor_set(x_159, 2, x_43);
lean_ctor_set(x_159, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_160 = x_57;
} else {
 lean_dec_ref(x_57);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_157);
lean_ctor_set(x_161, 3, x_158);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_161);
lean_ctor_set(x_56, 0, x_159);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_56, 1);
x_163 = lean_ctor_get(x_56, 2);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_56);
x_164 = lean_ctor_get(x_131, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_131, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_131, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_131, 3);
lean_inc(x_167);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_168 = x_131;
} else {
 lean_dec_ref(x_131);
 x_168 = lean_box(0);
}
lean_inc(x_57);
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 4, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_41);
lean_ctor_set(x_169, 1, x_42);
lean_ctor_set(x_169, 2, x_43);
lean_ctor_set(x_169, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_170 = x_57;
} else {
 lean_dec_ref(x_57);
 x_170 = lean_box(0);
}
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_165);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_105);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_162);
lean_ctor_set(x_172, 2, x_163);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_140);
return x_172;
}
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_56);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_56, 3);
lean_dec(x_174);
x_175 = lean_ctor_get(x_56, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_57);
if (x_176 == 0)
{
uint8_t x_177; 
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_140);
x_177 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_177);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_57, 0);
x_179 = lean_ctor_get(x_57, 1);
x_180 = lean_ctor_get(x_57, 2);
x_181 = lean_ctor_get(x_57, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_57);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_140);
x_183 = 0;
lean_ctor_set(x_56, 0, x_182);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_183);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_56, 1);
x_185 = lean_ctor_get(x_56, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_56);
x_186 = lean_ctor_get(x_57, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_57, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_57, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_57, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_190 = x_57;
} else {
 lean_dec_ref(x_57);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 4, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_140);
x_192 = 0;
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_185);
lean_ctor_set(x_193, 3, x_131);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_192);
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
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
uint8_t x_194; uint8_t x_195; 
x_194 = l_RBNode_isRed___rarg(x_41);
x_195 = l_Bool_DecidableEq(x_194, x_47);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_41, x_2, x_3);
lean_ctor_set(x_1, 0, x_196);
return x_1;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_41, x_2, x_3);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 3);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_197, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_197, 0);
lean_dec(x_202);
x_203 = 0;
lean_ctor_set(x_197, 0, x_199);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_203);
x_204 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_197, 1);
x_206 = lean_ctor_get(x_197, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_197);
x_207 = 0;
x_208 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_206);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_207);
x_209 = 1;
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_209);
return x_1;
}
}
else
{
uint8_t x_210; 
x_210 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_197, 1);
x_213 = lean_ctor_get(x_197, 2);
x_214 = lean_ctor_get(x_197, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_197, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_199);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_199, 0);
x_218 = lean_ctor_get(x_199, 1);
x_219 = lean_ctor_get(x_199, 2);
x_220 = lean_ctor_get(x_199, 3);
x_221 = 1;
lean_ctor_set(x_199, 3, x_217);
lean_ctor_set(x_199, 2, x_213);
lean_ctor_set(x_199, 1, x_212);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_221);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_220);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_221);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
x_224 = lean_ctor_get(x_199, 2);
x_225 = lean_ctor_get(x_199, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_226 = 1;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_198);
lean_ctor_set(x_227, 1, x_212);
lean_ctor_set(x_227, 2, x_213);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_225);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_226);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_197, 1);
x_229 = lean_ctor_get(x_197, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_197);
x_230 = lean_ctor_get(x_199, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_199, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_199, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_199, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_234 = x_199;
} else {
 lean_dec_ref(x_199);
 x_234 = lean_box(0);
}
x_235 = 1;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 4, 1);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_198);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set(x_236, 2, x_229);
lean_ctor_set(x_236, 3, x_230);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_42);
lean_ctor_set(x_237, 2, x_43);
lean_ctor_set(x_237, 3, x_44);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_235);
lean_ctor_set(x_1, 3, x_237);
lean_ctor_set(x_1, 2, x_232);
lean_ctor_set(x_1, 1, x_231);
lean_ctor_set(x_1, 0, x_236);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_197);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_197, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_197, 0);
lean_dec(x_240);
x_241 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_197, 1);
x_243 = lean_ctor_get(x_197, 2);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_197);
x_244 = 0;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_198);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_199);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_198, sizeof(void*)*4);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_197);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_197, 1);
x_249 = lean_ctor_get(x_197, 2);
x_250 = lean_ctor_get(x_197, 3);
x_251 = lean_ctor_get(x_197, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_198);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = 1;
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_253);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_253);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_198, 0);
x_255 = lean_ctor_get(x_198, 1);
x_256 = lean_ctor_get(x_198, 2);
x_257 = lean_ctor_get(x_198, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_198);
x_258 = 1;
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_255);
lean_ctor_set(x_259, 2, x_256);
lean_ctor_set(x_259, 3, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; 
x_260 = lean_ctor_get(x_197, 1);
x_261 = lean_ctor_get(x_197, 2);
x_262 = lean_ctor_get(x_197, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_197);
x_263 = lean_ctor_get(x_198, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_198, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_198, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_198, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_267 = x_198;
} else {
 lean_dec_ref(x_198);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_42);
lean_ctor_set(x_270, 2, x_43);
lean_ctor_set(x_270, 3, x_44);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_197, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_197);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_197, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_197, 0);
lean_dec(x_274);
x_275 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_197, 1);
x_277 = lean_ctor_get(x_197, 2);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_197);
x_278 = 0;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_198);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_279, 2, x_277);
lean_ctor_set(x_279, 3, x_271);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
lean_ctor_set(x_1, 0, x_279);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_197);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_197, 1);
x_283 = lean_ctor_get(x_197, 2);
x_284 = lean_ctor_get(x_197, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_197, 0);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_271);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_271, 0);
x_288 = lean_ctor_get(x_271, 1);
x_289 = lean_ctor_get(x_271, 2);
x_290 = lean_ctor_get(x_271, 3);
lean_inc(x_198);
lean_ctor_set(x_271, 3, x_287);
lean_ctor_set(x_271, 2, x_283);
lean_ctor_set(x_271, 1, x_282);
lean_ctor_set(x_271, 0, x_198);
x_291 = !lean_is_exclusive(x_198);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_198, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_198, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_198, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_198, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
lean_ctor_set(x_198, 3, x_44);
lean_ctor_set(x_198, 2, x_43);
lean_ctor_set(x_198, 1, x_42);
lean_ctor_set(x_198, 0, x_290);
lean_ctor_set(x_197, 3, x_198);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
else
{
lean_object* x_296; 
lean_dec(x_198);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_42);
lean_ctor_set(x_296, 2, x_43);
lean_ctor_set(x_296, 3, x_44);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_296);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_297 = lean_ctor_get(x_271, 0);
x_298 = lean_ctor_get(x_271, 1);
x_299 = lean_ctor_get(x_271, 2);
x_300 = lean_ctor_get(x_271, 3);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_271);
lean_inc(x_198);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_198);
lean_ctor_set(x_301, 1, x_282);
lean_ctor_set(x_301, 2, x_283);
lean_ctor_set(x_301, 3, x_297);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_302 = x_198;
} else {
 lean_dec_ref(x_198);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_42);
lean_ctor_set(x_303, 2, x_43);
lean_ctor_set(x_303, 3, x_44);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_303);
lean_ctor_set(x_197, 2, x_299);
lean_ctor_set(x_197, 1, x_298);
lean_ctor_set(x_197, 0, x_301);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_197, 1);
x_305 = lean_ctor_get(x_197, 2);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_197);
x_306 = lean_ctor_get(x_271, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_271, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_271, 3);
lean_inc(x_309);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_310 = x_271;
} else {
 lean_dec_ref(x_271);
 x_310 = lean_box(0);
}
lean_inc(x_198);
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 4, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_198);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_306);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_312 = x_198;
} else {
 lean_dec_ref(x_198);
 x_312 = lean_box(0);
}
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 4, 1);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_42);
lean_ctor_set(x_313, 2, x_43);
lean_ctor_set(x_313, 3, x_44);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_246);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_307);
lean_ctor_set(x_314, 2, x_308);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_280);
return x_314;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_197);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_197, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_197, 0);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
uint8_t x_319; 
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_280);
x_319 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_319);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_198, 0);
x_321 = lean_ctor_get(x_198, 1);
x_322 = lean_ctor_get(x_198, 2);
x_323 = lean_ctor_get(x_198, 3);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_198);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_322);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_280);
x_325 = 0;
lean_ctor_set(x_197, 0, x_324);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_325);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_197, 1);
x_327 = lean_ctor_get(x_197, 2);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_197);
x_328 = lean_ctor_get(x_198, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_198, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_198, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_198, 3);
lean_inc(x_331);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_332 = x_198;
} else {
 lean_dec_ref(x_198);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_329);
lean_ctor_set(x_333, 2, x_330);
lean_ctor_set(x_333, 3, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_280);
x_334 = 0;
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_326);
lean_ctor_set(x_335, 2, x_327);
lean_ctor_set(x_335, 3, x_271);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_334);
lean_ctor_set(x_1, 0, x_335);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
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
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint32_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_1, 0);
x_337 = lean_ctor_get(x_1, 1);
x_338 = lean_ctor_get(x_1, 2);
x_339 = lean_ctor_get(x_1, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_1);
x_340 = lean_unbox_uint32(x_337);
x_341 = x_2 < x_340;
x_342 = 1;
x_343 = l_Bool_DecidableEq(x_341, x_342);
if (x_343 == 0)
{
uint32_t x_344; uint8_t x_345; uint8_t x_346; 
x_344 = lean_unbox_uint32(x_337);
x_345 = x_344 < x_2;
x_346 = l_Bool_DecidableEq(x_345, x_342);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_338);
lean_dec(x_337);
x_347 = lean_box_uint32(x_2);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_348, 2, x_3);
lean_ctor_set(x_348, 3, x_339);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
uint8_t x_349; uint8_t x_350; 
x_349 = l_RBNode_isRed___rarg(x_339);
x_350 = l_Bool_DecidableEq(x_349, x_342);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_339, x_2, x_3);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_337);
lean_ctor_set(x_352, 2, x_338);
lean_ctor_set(x_352, 3, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_7);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_339, x_2, x_3);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 3);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = 0;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_356);
lean_ctor_set(x_360, 2, x_357);
lean_ctor_set(x_360, 3, x_355);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_336);
lean_ctor_set(x_362, 1, x_337);
lean_ctor_set(x_362, 2, x_338);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_361);
return x_362;
}
else
{
uint8_t x_363; 
x_363 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = lean_ctor_get(x_353, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_353, 2);
lean_inc(x_365);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_366 = x_353;
} else {
 lean_dec_ref(x_353);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_355, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_355, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_371 = x_355;
} else {
 lean_dec_ref(x_355);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_336);
lean_ctor_set(x_373, 1, x_337);
lean_ctor_set(x_373, 2, x_338);
lean_ctor_set(x_373, 3, x_354);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
if (lean_is_scalar(x_366)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_366;
}
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_368);
lean_ctor_set(x_374, 2, x_369);
lean_ctor_set(x_374, 3, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_372);
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_365);
lean_ctor_set(x_375, 3, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_363);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_353, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_378 = x_353;
} else {
 lean_dec_ref(x_353);
 x_378 = lean_box(0);
}
x_379 = 0;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_354);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_377);
lean_ctor_set(x_380, 3, x_355);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
x_381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_381, 0, x_336);
lean_ctor_set(x_381, 1, x_337);
lean_ctor_set(x_381, 2, x_338);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_363);
return x_381;
}
}
}
else
{
uint8_t x_382; 
x_382 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_383 = lean_ctor_get(x_353, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 3);
lean_inc(x_385);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_386 = x_353;
} else {
 lean_dec_ref(x_353);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_354, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_354, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_354, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_354, 3);
lean_inc(x_390);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_391 = x_354;
} else {
 lean_dec_ref(x_354);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_336);
lean_ctor_set(x_393, 1, x_337);
lean_ctor_set(x_393, 2, x_338);
lean_ctor_set(x_393, 3, x_387);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
if (lean_is_scalar(x_386)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_386;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_385);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_388);
lean_ctor_set(x_395, 2, x_389);
lean_ctor_set(x_395, 3, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_382);
return x_395;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_353, 3);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_353, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_353, 2);
lean_inc(x_398);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_399 = x_353;
} else {
 lean_dec_ref(x_353);
 x_399 = lean_box(0);
}
x_400 = 0;
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_354);
lean_ctor_set(x_401, 1, x_397);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_396);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_336);
lean_ctor_set(x_402, 1, x_337);
lean_ctor_set(x_402, 2, x_338);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_382);
return x_402;
}
else
{
uint8_t x_403; 
x_403 = lean_ctor_get_uint8(x_396, sizeof(void*)*4);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_404 = lean_ctor_get(x_353, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_353, 2);
lean_inc(x_405);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_406 = x_353;
} else {
 lean_dec_ref(x_353);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_396, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_396, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_396, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_396, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 x_411 = x_396;
} else {
 lean_dec_ref(x_396);
 x_411 = lean_box(0);
}
lean_inc(x_354);
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 4, 1);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_336);
lean_ctor_set(x_412, 1, x_337);
lean_ctor_set(x_412, 2, x_338);
lean_ctor_set(x_412, 3, x_354);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_413 = x_354;
} else {
 lean_dec_ref(x_354);
 x_413 = lean_box(0);
}
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_408);
lean_ctor_set(x_414, 2, x_409);
lean_ctor_set(x_414, 3, x_410);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_406)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_406;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_404);
lean_ctor_set(x_415, 2, x_405);
lean_ctor_set(x_415, 3, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_403);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_418 = x_353;
} else {
 lean_dec_ref(x_353);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_354, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_354, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_354, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_354, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_423 = x_354;
} else {
 lean_dec_ref(x_354);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_421);
lean_ctor_set(x_424, 3, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_403);
x_425 = 0;
if (lean_is_scalar(x_418)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_418;
}
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_416);
lean_ctor_set(x_426, 2, x_417);
lean_ctor_set(x_426, 3, x_396);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_336);
lean_ctor_set(x_427, 1, x_337);
lean_ctor_set(x_427, 2, x_338);
lean_ctor_set(x_427, 3, x_426);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_403);
return x_427;
}
}
}
}
}
}
}
else
{
uint8_t x_428; uint8_t x_429; 
x_428 = l_RBNode_isRed___rarg(x_336);
x_429 = l_Bool_DecidableEq(x_428, x_342);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_336, x_2, x_3);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_337);
lean_ctor_set(x_431, 2, x_338);
lean_ctor_set(x_431, 3, x_339);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_7);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_336, x_2, x_3);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_432, 3);
lean_inc(x_434);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; 
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = 0;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_434);
lean_ctor_set(x_439, 1, x_435);
lean_ctor_set(x_439, 2, x_436);
lean_ctor_set(x_439, 3, x_434);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = 1;
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_337);
lean_ctor_set(x_441, 2, x_338);
lean_ctor_set(x_441, 3, x_339);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
return x_441;
}
else
{
uint8_t x_442; 
x_442 = lean_ctor_get_uint8(x_434, sizeof(void*)*4);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_443 = lean_ctor_get(x_432, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 2);
lean_inc(x_444);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_445 = x_432;
} else {
 lean_dec_ref(x_432);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_434, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_434, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_434, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_434, 3);
lean_inc(x_449);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 lean_ctor_release(x_434, 2);
 lean_ctor_release(x_434, 3);
 x_450 = x_434;
} else {
 lean_dec_ref(x_434);
 x_450 = lean_box(0);
}
x_451 = 1;
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_433);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_446);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_449);
lean_ctor_set(x_453, 1, x_337);
lean_ctor_set(x_453, 2, x_338);
lean_ctor_set(x_453, 3, x_339);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_447);
lean_ctor_set(x_454, 2, x_448);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_442);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_432, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_432, 2);
lean_inc(x_456);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_457 = x_432;
} else {
 lean_dec_ref(x_432);
 x_457 = lean_box(0);
}
x_458 = 0;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_433);
lean_ctor_set(x_459, 1, x_455);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_434);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
x_460 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_337);
lean_ctor_set(x_460, 2, x_338);
lean_ctor_set(x_460, 3, x_339);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_442);
return x_460;
}
}
}
else
{
uint8_t x_461; 
x_461 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_462 = lean_ctor_get(x_432, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_432, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_432, 3);
lean_inc(x_464);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_465 = x_432;
} else {
 lean_dec_ref(x_432);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_433, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_433, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_433, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_433, 3);
lean_inc(x_469);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_470 = x_433;
} else {
 lean_dec_ref(x_433);
 x_470 = lean_box(0);
}
x_471 = 1;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(1, 4, 1);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_466);
lean_ctor_set(x_472, 1, x_467);
lean_ctor_set(x_472, 2, x_468);
lean_ctor_set(x_472, 3, x_469);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_465)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_465;
}
lean_ctor_set(x_473, 0, x_464);
lean_ctor_set(x_473, 1, x_337);
lean_ctor_set(x_473, 2, x_338);
lean_ctor_set(x_473, 3, x_339);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_471);
x_474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_462);
lean_ctor_set(x_474, 2, x_463);
lean_ctor_set(x_474, 3, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_461);
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_432, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; 
x_476 = lean_ctor_get(x_432, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_432, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_478 = x_432;
} else {
 lean_dec_ref(x_432);
 x_478 = lean_box(0);
}
x_479 = 0;
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_433);
lean_ctor_set(x_480, 1, x_476);
lean_ctor_set(x_480, 2, x_477);
lean_ctor_set(x_480, 3, x_475);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
x_481 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_337);
lean_ctor_set(x_481, 2, x_338);
lean_ctor_set(x_481, 3, x_339);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_461);
return x_481;
}
else
{
uint8_t x_482; 
x_482 = lean_ctor_get_uint8(x_475, sizeof(void*)*4);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_483 = lean_ctor_get(x_432, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_432, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_485 = x_432;
} else {
 lean_dec_ref(x_432);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_475, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_475, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_475, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_475, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_490 = x_475;
} else {
 lean_dec_ref(x_475);
 x_490 = lean_box(0);
}
lean_inc(x_433);
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_433);
lean_ctor_set(x_491, 1, x_483);
lean_ctor_set(x_491, 2, x_484);
lean_ctor_set(x_491, 3, x_486);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_492 = x_433;
} else {
 lean_dec_ref(x_433);
 x_492 = lean_box(0);
}
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_337);
lean_ctor_set(x_493, 2, x_338);
lean_ctor_set(x_493, 3, x_339);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_485)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_485;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_487);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set(x_494, 3, x_493);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_482);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
x_495 = lean_ctor_get(x_432, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_432, 2);
lean_inc(x_496);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_497 = x_432;
} else {
 lean_dec_ref(x_432);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_433, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_433, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_433, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_433, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_502 = x_433;
} else {
 lean_dec_ref(x_433);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 4, 1);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_482);
x_504 = 0;
if (lean_is_scalar(x_497)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_497;
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_495);
lean_ctor_set(x_505, 2, x_496);
lean_ctor_set(x_505, 3, x_475);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_337);
lean_ctor_set(x_506, 2, x_338);
lean_ctor_set(x_506, 3, x_339);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_482);
return x_506;
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
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_unbox_uint32(x_10);
x_18 = x_17 < x_2;
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_21);
return x_1;
}
}
else
{
lean_object* x_22; 
x_22 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_27 = lean_unbox_uint32(x_24);
x_28 = x_2 < x_27;
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_unbox_uint32(x_24);
x_32 = x_31 < x_2;
x_33 = l_Bool_DecidableEq(x_32, x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_24);
x_34 = lean_box_uint32(x_2);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_26, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_23, x_2, x_3);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_7);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_unbox_uint32(x_42);
x_46 = x_2 < x_45;
x_47 = 1;
x_48 = l_Bool_DecidableEq(x_46, x_47);
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_unbox_uint32(x_42);
x_50 = x_49 < x_2;
x_51 = l_Bool_DecidableEq(x_50, x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_42);
x_52 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_52);
return x_1;
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = l_RBNode_isRed___rarg(x_44);
x_54 = l_Bool_DecidableEq(x_53, x_47);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_44, x_2, x_3);
lean_ctor_set(x_1, 3, x_55);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_44, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = 0;
lean_ctor_set(x_56, 0, x_58);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_62);
x_63 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_63);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_56, 1);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = 0;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = 1;
lean_ctor_set(x_1, 3, x_67);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_68);
return x_1;
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_56, 1);
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_56, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
x_78 = lean_ctor_get(x_58, 2);
x_79 = lean_ctor_get(x_58, 3);
x_80 = 1;
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_80);
lean_ctor_set(x_56, 3, x_79);
lean_ctor_set(x_56, 2, x_78);
lean_ctor_set(x_56, 1, x_77);
lean_ctor_set(x_56, 0, x_76);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_58);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
x_83 = lean_ctor_get(x_58, 2);
x_84 = lean_ctor_get(x_58, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_85 = 1;
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_41);
lean_ctor_set(x_86, 1, x_42);
lean_ctor_set(x_86, 2, x_43);
lean_ctor_set(x_86, 3, x_57);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
lean_ctor_set(x_56, 3, x_84);
lean_ctor_set(x_56, 2, x_83);
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_81);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_85);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_56, 1);
x_88 = lean_ctor_get(x_56, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_56);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_58, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_58, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_93 = x_58;
} else {
 lean_dec_ref(x_58);
 x_93 = lean_box(0);
}
x_94 = 1;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(1, 4, 1);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_41);
lean_ctor_set(x_95, 1, x_42);
lean_ctor_set(x_95, 2, x_43);
lean_ctor_set(x_95, 3, x_57);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_94);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_94);
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set(x_1, 2, x_88);
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_56);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_56, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_56, 0);
lean_dec(x_99);
x_100 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_56, 1);
x_102 = lean_ctor_get(x_56, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = 0;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_57);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_102);
lean_ctor_set(x_104, 3, x_58);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_104);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
}
}
else
{
uint8_t x_105; 
x_105 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_56);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_56, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_57);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_57, 0);
x_110 = lean_ctor_get(x_57, 1);
x_111 = lean_ctor_get(x_57, 2);
x_112 = lean_ctor_get(x_57, 3);
x_113 = 1;
lean_ctor_set(x_57, 3, x_109);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 1, x_42);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_113);
lean_ctor_set(x_56, 0, x_112);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_113);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_57, 0);
x_115 = lean_ctor_get(x_57, 1);
x_116 = lean_ctor_get(x_57, 2);
x_117 = lean_ctor_get(x_57, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_57);
x_118 = 1;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_41);
lean_ctor_set(x_119, 1, x_42);
lean_ctor_set(x_119, 2, x_43);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_56, 0, x_117);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_116);
lean_ctor_set(x_1, 1, x_115);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_56, 1);
x_121 = lean_ctor_get(x_56, 2);
x_122 = lean_ctor_get(x_56, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_56);
x_123 = lean_ctor_get(x_57, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_57, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_57, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_57, 3);
lean_inc(x_126);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_127 = x_57;
} else {
 lean_dec_ref(x_57);
 x_127 = lean_box(0);
}
x_128 = 1;
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_41);
lean_ctor_set(x_129, 1, x_42);
lean_ctor_set(x_129, 2, x_43);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_130);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_56, 3);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_56);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_56, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_56, 0);
lean_dec(x_134);
x_135 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_56, 1);
x_137 = lean_ctor_get(x_56, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_56);
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_57);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_131);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_131, sizeof(void*)*4);
if (x_140 == 0)
{
uint8_t x_141; 
lean_free_object(x_1);
x_141 = !lean_is_exclusive(x_56);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_56, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_56, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
x_147 = lean_ctor_get(x_131, 2);
x_148 = lean_ctor_get(x_131, 3);
lean_inc(x_57);
lean_ctor_set(x_131, 3, x_57);
lean_ctor_set(x_131, 2, x_43);
lean_ctor_set(x_131, 1, x_42);
lean_ctor_set(x_131, 0, x_41);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_57, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_57, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_57, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_57, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
lean_ctor_set(x_57, 3, x_148);
lean_ctor_set(x_57, 2, x_147);
lean_ctor_set(x_57, 1, x_146);
lean_ctor_set(x_57, 0, x_145);
lean_ctor_set(x_56, 3, x_57);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
else
{
lean_object* x_154; 
lean_dec(x_57);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_154);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_131, 0);
x_156 = lean_ctor_get(x_131, 1);
x_157 = lean_ctor_get(x_131, 2);
x_158 = lean_ctor_get(x_131, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_131);
lean_inc(x_57);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_41);
lean_ctor_set(x_159, 1, x_42);
lean_ctor_set(x_159, 2, x_43);
lean_ctor_set(x_159, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_160 = x_57;
} else {
 lean_dec_ref(x_57);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_157);
lean_ctor_set(x_161, 3, x_158);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_161);
lean_ctor_set(x_56, 0, x_159);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_56, 1);
x_163 = lean_ctor_get(x_56, 2);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_56);
x_164 = lean_ctor_get(x_131, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_131, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_131, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_131, 3);
lean_inc(x_167);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_168 = x_131;
} else {
 lean_dec_ref(x_131);
 x_168 = lean_box(0);
}
lean_inc(x_57);
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 4, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_41);
lean_ctor_set(x_169, 1, x_42);
lean_ctor_set(x_169, 2, x_43);
lean_ctor_set(x_169, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_170 = x_57;
} else {
 lean_dec_ref(x_57);
 x_170 = lean_box(0);
}
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_165);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_105);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_162);
lean_ctor_set(x_172, 2, x_163);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_140);
return x_172;
}
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_56);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_56, 3);
lean_dec(x_174);
x_175 = lean_ctor_get(x_56, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_57);
if (x_176 == 0)
{
uint8_t x_177; 
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_140);
x_177 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_177);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_57, 0);
x_179 = lean_ctor_get(x_57, 1);
x_180 = lean_ctor_get(x_57, 2);
x_181 = lean_ctor_get(x_57, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_57);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_140);
x_183 = 0;
lean_ctor_set(x_56, 0, x_182);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_183);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_56, 1);
x_185 = lean_ctor_get(x_56, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_56);
x_186 = lean_ctor_get(x_57, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_57, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_57, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_57, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_190 = x_57;
} else {
 lean_dec_ref(x_57);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 4, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_140);
x_192 = 0;
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_185);
lean_ctor_set(x_193, 3, x_131);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_192);
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
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
uint8_t x_194; uint8_t x_195; 
x_194 = l_RBNode_isRed___rarg(x_41);
x_195 = l_Bool_DecidableEq(x_194, x_47);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_41, x_2, x_3);
lean_ctor_set(x_1, 0, x_196);
return x_1;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_41, x_2, x_3);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 3);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_197, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_197, 0);
lean_dec(x_202);
x_203 = 0;
lean_ctor_set(x_197, 0, x_199);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_203);
x_204 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_197, 1);
x_206 = lean_ctor_get(x_197, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_197);
x_207 = 0;
x_208 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_206);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_207);
x_209 = 1;
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_209);
return x_1;
}
}
else
{
uint8_t x_210; 
x_210 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_197, 1);
x_213 = lean_ctor_get(x_197, 2);
x_214 = lean_ctor_get(x_197, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_197, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_199);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_199, 0);
x_218 = lean_ctor_get(x_199, 1);
x_219 = lean_ctor_get(x_199, 2);
x_220 = lean_ctor_get(x_199, 3);
x_221 = 1;
lean_ctor_set(x_199, 3, x_217);
lean_ctor_set(x_199, 2, x_213);
lean_ctor_set(x_199, 1, x_212);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_221);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_220);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_221);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
x_224 = lean_ctor_get(x_199, 2);
x_225 = lean_ctor_get(x_199, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_226 = 1;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_198);
lean_ctor_set(x_227, 1, x_212);
lean_ctor_set(x_227, 2, x_213);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_225);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_226);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_197, 1);
x_229 = lean_ctor_get(x_197, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_197);
x_230 = lean_ctor_get(x_199, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_199, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_199, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_199, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_234 = x_199;
} else {
 lean_dec_ref(x_199);
 x_234 = lean_box(0);
}
x_235 = 1;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 4, 1);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_198);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set(x_236, 2, x_229);
lean_ctor_set(x_236, 3, x_230);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_42);
lean_ctor_set(x_237, 2, x_43);
lean_ctor_set(x_237, 3, x_44);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_235);
lean_ctor_set(x_1, 3, x_237);
lean_ctor_set(x_1, 2, x_232);
lean_ctor_set(x_1, 1, x_231);
lean_ctor_set(x_1, 0, x_236);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_197);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_197, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_197, 0);
lean_dec(x_240);
x_241 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_197, 1);
x_243 = lean_ctor_get(x_197, 2);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_197);
x_244 = 0;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_198);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_199);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_198, sizeof(void*)*4);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_197);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_197, 1);
x_249 = lean_ctor_get(x_197, 2);
x_250 = lean_ctor_get(x_197, 3);
x_251 = lean_ctor_get(x_197, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_198);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = 1;
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_253);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_253);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_198, 0);
x_255 = lean_ctor_get(x_198, 1);
x_256 = lean_ctor_get(x_198, 2);
x_257 = lean_ctor_get(x_198, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_198);
x_258 = 1;
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_255);
lean_ctor_set(x_259, 2, x_256);
lean_ctor_set(x_259, 3, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; 
x_260 = lean_ctor_get(x_197, 1);
x_261 = lean_ctor_get(x_197, 2);
x_262 = lean_ctor_get(x_197, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_197);
x_263 = lean_ctor_get(x_198, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_198, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_198, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_198, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_267 = x_198;
} else {
 lean_dec_ref(x_198);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_42);
lean_ctor_set(x_270, 2, x_43);
lean_ctor_set(x_270, 3, x_44);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_197, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_197);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_197, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_197, 0);
lean_dec(x_274);
x_275 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_197, 1);
x_277 = lean_ctor_get(x_197, 2);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_197);
x_278 = 0;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_198);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_279, 2, x_277);
lean_ctor_set(x_279, 3, x_271);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
lean_ctor_set(x_1, 0, x_279);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_197);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_197, 1);
x_283 = lean_ctor_get(x_197, 2);
x_284 = lean_ctor_get(x_197, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_197, 0);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_271);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_271, 0);
x_288 = lean_ctor_get(x_271, 1);
x_289 = lean_ctor_get(x_271, 2);
x_290 = lean_ctor_get(x_271, 3);
lean_inc(x_198);
lean_ctor_set(x_271, 3, x_287);
lean_ctor_set(x_271, 2, x_283);
lean_ctor_set(x_271, 1, x_282);
lean_ctor_set(x_271, 0, x_198);
x_291 = !lean_is_exclusive(x_198);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_198, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_198, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_198, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_198, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
lean_ctor_set(x_198, 3, x_44);
lean_ctor_set(x_198, 2, x_43);
lean_ctor_set(x_198, 1, x_42);
lean_ctor_set(x_198, 0, x_290);
lean_ctor_set(x_197, 3, x_198);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
else
{
lean_object* x_296; 
lean_dec(x_198);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_42);
lean_ctor_set(x_296, 2, x_43);
lean_ctor_set(x_296, 3, x_44);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_296);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_297 = lean_ctor_get(x_271, 0);
x_298 = lean_ctor_get(x_271, 1);
x_299 = lean_ctor_get(x_271, 2);
x_300 = lean_ctor_get(x_271, 3);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_271);
lean_inc(x_198);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_198);
lean_ctor_set(x_301, 1, x_282);
lean_ctor_set(x_301, 2, x_283);
lean_ctor_set(x_301, 3, x_297);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_302 = x_198;
} else {
 lean_dec_ref(x_198);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_42);
lean_ctor_set(x_303, 2, x_43);
lean_ctor_set(x_303, 3, x_44);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_303);
lean_ctor_set(x_197, 2, x_299);
lean_ctor_set(x_197, 1, x_298);
lean_ctor_set(x_197, 0, x_301);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_197, 1);
x_305 = lean_ctor_get(x_197, 2);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_197);
x_306 = lean_ctor_get(x_271, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_271, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_271, 3);
lean_inc(x_309);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_310 = x_271;
} else {
 lean_dec_ref(x_271);
 x_310 = lean_box(0);
}
lean_inc(x_198);
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 4, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_198);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_306);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_312 = x_198;
} else {
 lean_dec_ref(x_198);
 x_312 = lean_box(0);
}
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 4, 1);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_42);
lean_ctor_set(x_313, 2, x_43);
lean_ctor_set(x_313, 3, x_44);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_246);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_307);
lean_ctor_set(x_314, 2, x_308);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_280);
return x_314;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_197);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_197, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_197, 0);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
uint8_t x_319; 
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_280);
x_319 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_319);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_198, 0);
x_321 = lean_ctor_get(x_198, 1);
x_322 = lean_ctor_get(x_198, 2);
x_323 = lean_ctor_get(x_198, 3);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_198);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_322);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_280);
x_325 = 0;
lean_ctor_set(x_197, 0, x_324);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_325);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_197, 1);
x_327 = lean_ctor_get(x_197, 2);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_197);
x_328 = lean_ctor_get(x_198, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_198, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_198, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_198, 3);
lean_inc(x_331);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_332 = x_198;
} else {
 lean_dec_ref(x_198);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_329);
lean_ctor_set(x_333, 2, x_330);
lean_ctor_set(x_333, 3, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_280);
x_334 = 0;
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_326);
lean_ctor_set(x_335, 2, x_327);
lean_ctor_set(x_335, 3, x_271);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_334);
lean_ctor_set(x_1, 0, x_335);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
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
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint32_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_1, 0);
x_337 = lean_ctor_get(x_1, 1);
x_338 = lean_ctor_get(x_1, 2);
x_339 = lean_ctor_get(x_1, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_1);
x_340 = lean_unbox_uint32(x_337);
x_341 = x_2 < x_340;
x_342 = 1;
x_343 = l_Bool_DecidableEq(x_341, x_342);
if (x_343 == 0)
{
uint32_t x_344; uint8_t x_345; uint8_t x_346; 
x_344 = lean_unbox_uint32(x_337);
x_345 = x_344 < x_2;
x_346 = l_Bool_DecidableEq(x_345, x_342);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_338);
lean_dec(x_337);
x_347 = lean_box_uint32(x_2);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_348, 2, x_3);
lean_ctor_set(x_348, 3, x_339);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
uint8_t x_349; uint8_t x_350; 
x_349 = l_RBNode_isRed___rarg(x_339);
x_350 = l_Bool_DecidableEq(x_349, x_342);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_339, x_2, x_3);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_337);
lean_ctor_set(x_352, 2, x_338);
lean_ctor_set(x_352, 3, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_7);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_339, x_2, x_3);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 3);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = 0;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_356);
lean_ctor_set(x_360, 2, x_357);
lean_ctor_set(x_360, 3, x_355);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_336);
lean_ctor_set(x_362, 1, x_337);
lean_ctor_set(x_362, 2, x_338);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_361);
return x_362;
}
else
{
uint8_t x_363; 
x_363 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = lean_ctor_get(x_353, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_353, 2);
lean_inc(x_365);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_366 = x_353;
} else {
 lean_dec_ref(x_353);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_355, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_355, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_371 = x_355;
} else {
 lean_dec_ref(x_355);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_336);
lean_ctor_set(x_373, 1, x_337);
lean_ctor_set(x_373, 2, x_338);
lean_ctor_set(x_373, 3, x_354);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
if (lean_is_scalar(x_366)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_366;
}
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_368);
lean_ctor_set(x_374, 2, x_369);
lean_ctor_set(x_374, 3, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_372);
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_365);
lean_ctor_set(x_375, 3, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_363);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_353, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_378 = x_353;
} else {
 lean_dec_ref(x_353);
 x_378 = lean_box(0);
}
x_379 = 0;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_354);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_377);
lean_ctor_set(x_380, 3, x_355);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
x_381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_381, 0, x_336);
lean_ctor_set(x_381, 1, x_337);
lean_ctor_set(x_381, 2, x_338);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_363);
return x_381;
}
}
}
else
{
uint8_t x_382; 
x_382 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_383 = lean_ctor_get(x_353, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 3);
lean_inc(x_385);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_386 = x_353;
} else {
 lean_dec_ref(x_353);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_354, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_354, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_354, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_354, 3);
lean_inc(x_390);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_391 = x_354;
} else {
 lean_dec_ref(x_354);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_336);
lean_ctor_set(x_393, 1, x_337);
lean_ctor_set(x_393, 2, x_338);
lean_ctor_set(x_393, 3, x_387);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
if (lean_is_scalar(x_386)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_386;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_385);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_388);
lean_ctor_set(x_395, 2, x_389);
lean_ctor_set(x_395, 3, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_382);
return x_395;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_353, 3);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_353, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_353, 2);
lean_inc(x_398);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_399 = x_353;
} else {
 lean_dec_ref(x_353);
 x_399 = lean_box(0);
}
x_400 = 0;
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_354);
lean_ctor_set(x_401, 1, x_397);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_396);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_336);
lean_ctor_set(x_402, 1, x_337);
lean_ctor_set(x_402, 2, x_338);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_382);
return x_402;
}
else
{
uint8_t x_403; 
x_403 = lean_ctor_get_uint8(x_396, sizeof(void*)*4);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_404 = lean_ctor_get(x_353, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_353, 2);
lean_inc(x_405);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_406 = x_353;
} else {
 lean_dec_ref(x_353);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_396, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_396, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_396, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_396, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 x_411 = x_396;
} else {
 lean_dec_ref(x_396);
 x_411 = lean_box(0);
}
lean_inc(x_354);
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 4, 1);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_336);
lean_ctor_set(x_412, 1, x_337);
lean_ctor_set(x_412, 2, x_338);
lean_ctor_set(x_412, 3, x_354);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_413 = x_354;
} else {
 lean_dec_ref(x_354);
 x_413 = lean_box(0);
}
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_408);
lean_ctor_set(x_414, 2, x_409);
lean_ctor_set(x_414, 3, x_410);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_406)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_406;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_404);
lean_ctor_set(x_415, 2, x_405);
lean_ctor_set(x_415, 3, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_403);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_418 = x_353;
} else {
 lean_dec_ref(x_353);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_354, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_354, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_354, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_354, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_423 = x_354;
} else {
 lean_dec_ref(x_354);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_421);
lean_ctor_set(x_424, 3, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_403);
x_425 = 0;
if (lean_is_scalar(x_418)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_418;
}
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_416);
lean_ctor_set(x_426, 2, x_417);
lean_ctor_set(x_426, 3, x_396);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_336);
lean_ctor_set(x_427, 1, x_337);
lean_ctor_set(x_427, 2, x_338);
lean_ctor_set(x_427, 3, x_426);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_403);
return x_427;
}
}
}
}
}
}
}
else
{
uint8_t x_428; uint8_t x_429; 
x_428 = l_RBNode_isRed___rarg(x_336);
x_429 = l_Bool_DecidableEq(x_428, x_342);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_336, x_2, x_3);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_337);
lean_ctor_set(x_431, 2, x_338);
lean_ctor_set(x_431, 3, x_339);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_7);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_336, x_2, x_3);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_432, 3);
lean_inc(x_434);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; 
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = 0;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_434);
lean_ctor_set(x_439, 1, x_435);
lean_ctor_set(x_439, 2, x_436);
lean_ctor_set(x_439, 3, x_434);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = 1;
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_337);
lean_ctor_set(x_441, 2, x_338);
lean_ctor_set(x_441, 3, x_339);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
return x_441;
}
else
{
uint8_t x_442; 
x_442 = lean_ctor_get_uint8(x_434, sizeof(void*)*4);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_443 = lean_ctor_get(x_432, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 2);
lean_inc(x_444);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_445 = x_432;
} else {
 lean_dec_ref(x_432);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_434, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_434, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_434, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_434, 3);
lean_inc(x_449);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 lean_ctor_release(x_434, 2);
 lean_ctor_release(x_434, 3);
 x_450 = x_434;
} else {
 lean_dec_ref(x_434);
 x_450 = lean_box(0);
}
x_451 = 1;
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_433);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_446);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_449);
lean_ctor_set(x_453, 1, x_337);
lean_ctor_set(x_453, 2, x_338);
lean_ctor_set(x_453, 3, x_339);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_447);
lean_ctor_set(x_454, 2, x_448);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_442);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_432, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_432, 2);
lean_inc(x_456);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_457 = x_432;
} else {
 lean_dec_ref(x_432);
 x_457 = lean_box(0);
}
x_458 = 0;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_433);
lean_ctor_set(x_459, 1, x_455);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_434);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
x_460 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_337);
lean_ctor_set(x_460, 2, x_338);
lean_ctor_set(x_460, 3, x_339);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_442);
return x_460;
}
}
}
else
{
uint8_t x_461; 
x_461 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_462 = lean_ctor_get(x_432, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_432, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_432, 3);
lean_inc(x_464);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_465 = x_432;
} else {
 lean_dec_ref(x_432);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_433, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_433, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_433, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_433, 3);
lean_inc(x_469);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_470 = x_433;
} else {
 lean_dec_ref(x_433);
 x_470 = lean_box(0);
}
x_471 = 1;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(1, 4, 1);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_466);
lean_ctor_set(x_472, 1, x_467);
lean_ctor_set(x_472, 2, x_468);
lean_ctor_set(x_472, 3, x_469);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_465)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_465;
}
lean_ctor_set(x_473, 0, x_464);
lean_ctor_set(x_473, 1, x_337);
lean_ctor_set(x_473, 2, x_338);
lean_ctor_set(x_473, 3, x_339);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_471);
x_474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_462);
lean_ctor_set(x_474, 2, x_463);
lean_ctor_set(x_474, 3, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_461);
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_432, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; 
x_476 = lean_ctor_get(x_432, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_432, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_478 = x_432;
} else {
 lean_dec_ref(x_432);
 x_478 = lean_box(0);
}
x_479 = 0;
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_433);
lean_ctor_set(x_480, 1, x_476);
lean_ctor_set(x_480, 2, x_477);
lean_ctor_set(x_480, 3, x_475);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
x_481 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_337);
lean_ctor_set(x_481, 2, x_338);
lean_ctor_set(x_481, 3, x_339);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_461);
return x_481;
}
else
{
uint8_t x_482; 
x_482 = lean_ctor_get_uint8(x_475, sizeof(void*)*4);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_483 = lean_ctor_get(x_432, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_432, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_485 = x_432;
} else {
 lean_dec_ref(x_432);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_475, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_475, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_475, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_475, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_490 = x_475;
} else {
 lean_dec_ref(x_475);
 x_490 = lean_box(0);
}
lean_inc(x_433);
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_433);
lean_ctor_set(x_491, 1, x_483);
lean_ctor_set(x_491, 2, x_484);
lean_ctor_set(x_491, 3, x_486);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_492 = x_433;
} else {
 lean_dec_ref(x_433);
 x_492 = lean_box(0);
}
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_337);
lean_ctor_set(x_493, 2, x_338);
lean_ctor_set(x_493, 3, x_339);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_485)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_485;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_487);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set(x_494, 3, x_493);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_482);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
x_495 = lean_ctor_get(x_432, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_432, 2);
lean_inc(x_496);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_497 = x_432;
} else {
 lean_dec_ref(x_432);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_433, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_433, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_433, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_433, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_502 = x_433;
} else {
 lean_dec_ref(x_433);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 4, 1);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_482);
x_504 = 0;
if (lean_is_scalar(x_497)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_497;
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_495);
lean_ctor_set(x_505, 2, x_496);
lean_ctor_set(x_505, 3, x_475);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_337);
lean_ctor_set(x_506, 2, x_338);
lean_ctor_set(x_506, 3, x_339);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_482);
return x_506;
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
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
}
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_unbox_uint32(x_10);
x_18 = x_17 < x_2;
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_21);
return x_1;
}
}
else
{
lean_object* x_22; 
x_22 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_27 = lean_unbox_uint32(x_24);
x_28 = x_2 < x_27;
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_unbox_uint32(x_24);
x_32 = x_31 < x_2;
x_33 = l_Bool_DecidableEq(x_32, x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_24);
x_34 = lean_box_uint32(x_2);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_26, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_23, x_2, x_3);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_7);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_unbox_uint32(x_42);
x_46 = x_2 < x_45;
x_47 = 1;
x_48 = l_Bool_DecidableEq(x_46, x_47);
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_unbox_uint32(x_42);
x_50 = x_49 < x_2;
x_51 = l_Bool_DecidableEq(x_50, x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_42);
x_52 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_52);
return x_1;
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = l_RBNode_isRed___rarg(x_44);
x_54 = l_Bool_DecidableEq(x_53, x_47);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_44, x_2, x_3);
lean_ctor_set(x_1, 3, x_55);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_44, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = 0;
lean_ctor_set(x_56, 0, x_58);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_62);
x_63 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_63);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_56, 1);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = 0;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = 1;
lean_ctor_set(x_1, 3, x_67);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_68);
return x_1;
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_56, 1);
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_56, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
x_78 = lean_ctor_get(x_58, 2);
x_79 = lean_ctor_get(x_58, 3);
x_80 = 1;
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_80);
lean_ctor_set(x_56, 3, x_79);
lean_ctor_set(x_56, 2, x_78);
lean_ctor_set(x_56, 1, x_77);
lean_ctor_set(x_56, 0, x_76);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_58);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
x_83 = lean_ctor_get(x_58, 2);
x_84 = lean_ctor_get(x_58, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_85 = 1;
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_41);
lean_ctor_set(x_86, 1, x_42);
lean_ctor_set(x_86, 2, x_43);
lean_ctor_set(x_86, 3, x_57);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
lean_ctor_set(x_56, 3, x_84);
lean_ctor_set(x_56, 2, x_83);
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_81);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_85);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_56, 1);
x_88 = lean_ctor_get(x_56, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_56);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_58, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_58, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_93 = x_58;
} else {
 lean_dec_ref(x_58);
 x_93 = lean_box(0);
}
x_94 = 1;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(1, 4, 1);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_41);
lean_ctor_set(x_95, 1, x_42);
lean_ctor_set(x_95, 2, x_43);
lean_ctor_set(x_95, 3, x_57);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_94);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_94);
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set(x_1, 2, x_88);
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_56);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_56, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_56, 0);
lean_dec(x_99);
x_100 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_56, 1);
x_102 = lean_ctor_get(x_56, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = 0;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_57);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_102);
lean_ctor_set(x_104, 3, x_58);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_104);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
}
}
else
{
uint8_t x_105; 
x_105 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_56);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_56, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_57);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_57, 0);
x_110 = lean_ctor_get(x_57, 1);
x_111 = lean_ctor_get(x_57, 2);
x_112 = lean_ctor_get(x_57, 3);
x_113 = 1;
lean_ctor_set(x_57, 3, x_109);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 1, x_42);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_113);
lean_ctor_set(x_56, 0, x_112);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_113);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_57, 0);
x_115 = lean_ctor_get(x_57, 1);
x_116 = lean_ctor_get(x_57, 2);
x_117 = lean_ctor_get(x_57, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_57);
x_118 = 1;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_41);
lean_ctor_set(x_119, 1, x_42);
lean_ctor_set(x_119, 2, x_43);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_56, 0, x_117);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_116);
lean_ctor_set(x_1, 1, x_115);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_56, 1);
x_121 = lean_ctor_get(x_56, 2);
x_122 = lean_ctor_get(x_56, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_56);
x_123 = lean_ctor_get(x_57, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_57, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_57, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_57, 3);
lean_inc(x_126);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_127 = x_57;
} else {
 lean_dec_ref(x_57);
 x_127 = lean_box(0);
}
x_128 = 1;
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_41);
lean_ctor_set(x_129, 1, x_42);
lean_ctor_set(x_129, 2, x_43);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_130);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_56, 3);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_56);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_56, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_56, 0);
lean_dec(x_134);
x_135 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_56, 1);
x_137 = lean_ctor_get(x_56, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_56);
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_57);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_131);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_131, sizeof(void*)*4);
if (x_140 == 0)
{
uint8_t x_141; 
lean_free_object(x_1);
x_141 = !lean_is_exclusive(x_56);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_56, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_56, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
x_147 = lean_ctor_get(x_131, 2);
x_148 = lean_ctor_get(x_131, 3);
lean_inc(x_57);
lean_ctor_set(x_131, 3, x_57);
lean_ctor_set(x_131, 2, x_43);
lean_ctor_set(x_131, 1, x_42);
lean_ctor_set(x_131, 0, x_41);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_57, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_57, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_57, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_57, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
lean_ctor_set(x_57, 3, x_148);
lean_ctor_set(x_57, 2, x_147);
lean_ctor_set(x_57, 1, x_146);
lean_ctor_set(x_57, 0, x_145);
lean_ctor_set(x_56, 3, x_57);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
else
{
lean_object* x_154; 
lean_dec(x_57);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_154);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_131, 0);
x_156 = lean_ctor_get(x_131, 1);
x_157 = lean_ctor_get(x_131, 2);
x_158 = lean_ctor_get(x_131, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_131);
lean_inc(x_57);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_41);
lean_ctor_set(x_159, 1, x_42);
lean_ctor_set(x_159, 2, x_43);
lean_ctor_set(x_159, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_160 = x_57;
} else {
 lean_dec_ref(x_57);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_157);
lean_ctor_set(x_161, 3, x_158);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_161);
lean_ctor_set(x_56, 0, x_159);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_56, 1);
x_163 = lean_ctor_get(x_56, 2);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_56);
x_164 = lean_ctor_get(x_131, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_131, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_131, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_131, 3);
lean_inc(x_167);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_168 = x_131;
} else {
 lean_dec_ref(x_131);
 x_168 = lean_box(0);
}
lean_inc(x_57);
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 4, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_41);
lean_ctor_set(x_169, 1, x_42);
lean_ctor_set(x_169, 2, x_43);
lean_ctor_set(x_169, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_170 = x_57;
} else {
 lean_dec_ref(x_57);
 x_170 = lean_box(0);
}
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_165);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_105);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_162);
lean_ctor_set(x_172, 2, x_163);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_140);
return x_172;
}
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_56);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_56, 3);
lean_dec(x_174);
x_175 = lean_ctor_get(x_56, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_57);
if (x_176 == 0)
{
uint8_t x_177; 
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_140);
x_177 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_177);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_57, 0);
x_179 = lean_ctor_get(x_57, 1);
x_180 = lean_ctor_get(x_57, 2);
x_181 = lean_ctor_get(x_57, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_57);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_140);
x_183 = 0;
lean_ctor_set(x_56, 0, x_182);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_183);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_56, 1);
x_185 = lean_ctor_get(x_56, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_56);
x_186 = lean_ctor_get(x_57, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_57, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_57, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_57, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_190 = x_57;
} else {
 lean_dec_ref(x_57);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 4, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_140);
x_192 = 0;
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_185);
lean_ctor_set(x_193, 3, x_131);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_192);
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
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
uint8_t x_194; uint8_t x_195; 
x_194 = l_RBNode_isRed___rarg(x_41);
x_195 = l_Bool_DecidableEq(x_194, x_47);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_41, x_2, x_3);
lean_ctor_set(x_1, 0, x_196);
return x_1;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_41, x_2, x_3);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 3);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_197, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_197, 0);
lean_dec(x_202);
x_203 = 0;
lean_ctor_set(x_197, 0, x_199);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_203);
x_204 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_197, 1);
x_206 = lean_ctor_get(x_197, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_197);
x_207 = 0;
x_208 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_206);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_207);
x_209 = 1;
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_209);
return x_1;
}
}
else
{
uint8_t x_210; 
x_210 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_197, 1);
x_213 = lean_ctor_get(x_197, 2);
x_214 = lean_ctor_get(x_197, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_197, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_199);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_199, 0);
x_218 = lean_ctor_get(x_199, 1);
x_219 = lean_ctor_get(x_199, 2);
x_220 = lean_ctor_get(x_199, 3);
x_221 = 1;
lean_ctor_set(x_199, 3, x_217);
lean_ctor_set(x_199, 2, x_213);
lean_ctor_set(x_199, 1, x_212);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_221);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_220);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_221);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
x_224 = lean_ctor_get(x_199, 2);
x_225 = lean_ctor_get(x_199, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_226 = 1;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_198);
lean_ctor_set(x_227, 1, x_212);
lean_ctor_set(x_227, 2, x_213);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_225);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_226);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_197, 1);
x_229 = lean_ctor_get(x_197, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_197);
x_230 = lean_ctor_get(x_199, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_199, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_199, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_199, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_234 = x_199;
} else {
 lean_dec_ref(x_199);
 x_234 = lean_box(0);
}
x_235 = 1;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 4, 1);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_198);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set(x_236, 2, x_229);
lean_ctor_set(x_236, 3, x_230);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_42);
lean_ctor_set(x_237, 2, x_43);
lean_ctor_set(x_237, 3, x_44);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_235);
lean_ctor_set(x_1, 3, x_237);
lean_ctor_set(x_1, 2, x_232);
lean_ctor_set(x_1, 1, x_231);
lean_ctor_set(x_1, 0, x_236);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_197);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_197, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_197, 0);
lean_dec(x_240);
x_241 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_197, 1);
x_243 = lean_ctor_get(x_197, 2);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_197);
x_244 = 0;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_198);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_199);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_198, sizeof(void*)*4);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_197);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_197, 1);
x_249 = lean_ctor_get(x_197, 2);
x_250 = lean_ctor_get(x_197, 3);
x_251 = lean_ctor_get(x_197, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_198);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = 1;
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_253);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_253);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_198, 0);
x_255 = lean_ctor_get(x_198, 1);
x_256 = lean_ctor_get(x_198, 2);
x_257 = lean_ctor_get(x_198, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_198);
x_258 = 1;
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_255);
lean_ctor_set(x_259, 2, x_256);
lean_ctor_set(x_259, 3, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; 
x_260 = lean_ctor_get(x_197, 1);
x_261 = lean_ctor_get(x_197, 2);
x_262 = lean_ctor_get(x_197, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_197);
x_263 = lean_ctor_get(x_198, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_198, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_198, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_198, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_267 = x_198;
} else {
 lean_dec_ref(x_198);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_42);
lean_ctor_set(x_270, 2, x_43);
lean_ctor_set(x_270, 3, x_44);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_197, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_197);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_197, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_197, 0);
lean_dec(x_274);
x_275 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_197, 1);
x_277 = lean_ctor_get(x_197, 2);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_197);
x_278 = 0;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_198);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_279, 2, x_277);
lean_ctor_set(x_279, 3, x_271);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
lean_ctor_set(x_1, 0, x_279);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_197);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_197, 1);
x_283 = lean_ctor_get(x_197, 2);
x_284 = lean_ctor_get(x_197, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_197, 0);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_271);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_271, 0);
x_288 = lean_ctor_get(x_271, 1);
x_289 = lean_ctor_get(x_271, 2);
x_290 = lean_ctor_get(x_271, 3);
lean_inc(x_198);
lean_ctor_set(x_271, 3, x_287);
lean_ctor_set(x_271, 2, x_283);
lean_ctor_set(x_271, 1, x_282);
lean_ctor_set(x_271, 0, x_198);
x_291 = !lean_is_exclusive(x_198);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_198, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_198, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_198, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_198, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
lean_ctor_set(x_198, 3, x_44);
lean_ctor_set(x_198, 2, x_43);
lean_ctor_set(x_198, 1, x_42);
lean_ctor_set(x_198, 0, x_290);
lean_ctor_set(x_197, 3, x_198);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
else
{
lean_object* x_296; 
lean_dec(x_198);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_42);
lean_ctor_set(x_296, 2, x_43);
lean_ctor_set(x_296, 3, x_44);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_296);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_297 = lean_ctor_get(x_271, 0);
x_298 = lean_ctor_get(x_271, 1);
x_299 = lean_ctor_get(x_271, 2);
x_300 = lean_ctor_get(x_271, 3);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_271);
lean_inc(x_198);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_198);
lean_ctor_set(x_301, 1, x_282);
lean_ctor_set(x_301, 2, x_283);
lean_ctor_set(x_301, 3, x_297);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_302 = x_198;
} else {
 lean_dec_ref(x_198);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_42);
lean_ctor_set(x_303, 2, x_43);
lean_ctor_set(x_303, 3, x_44);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_303);
lean_ctor_set(x_197, 2, x_299);
lean_ctor_set(x_197, 1, x_298);
lean_ctor_set(x_197, 0, x_301);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_197, 1);
x_305 = lean_ctor_get(x_197, 2);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_197);
x_306 = lean_ctor_get(x_271, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_271, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_271, 3);
lean_inc(x_309);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_310 = x_271;
} else {
 lean_dec_ref(x_271);
 x_310 = lean_box(0);
}
lean_inc(x_198);
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 4, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_198);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_306);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_312 = x_198;
} else {
 lean_dec_ref(x_198);
 x_312 = lean_box(0);
}
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 4, 1);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_42);
lean_ctor_set(x_313, 2, x_43);
lean_ctor_set(x_313, 3, x_44);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_246);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_307);
lean_ctor_set(x_314, 2, x_308);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_280);
return x_314;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_197);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_197, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_197, 0);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
uint8_t x_319; 
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_280);
x_319 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_319);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_198, 0);
x_321 = lean_ctor_get(x_198, 1);
x_322 = lean_ctor_get(x_198, 2);
x_323 = lean_ctor_get(x_198, 3);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_198);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_322);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_280);
x_325 = 0;
lean_ctor_set(x_197, 0, x_324);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_325);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_197, 1);
x_327 = lean_ctor_get(x_197, 2);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_197);
x_328 = lean_ctor_get(x_198, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_198, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_198, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_198, 3);
lean_inc(x_331);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_332 = x_198;
} else {
 lean_dec_ref(x_198);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_329);
lean_ctor_set(x_333, 2, x_330);
lean_ctor_set(x_333, 3, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_280);
x_334 = 0;
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_326);
lean_ctor_set(x_335, 2, x_327);
lean_ctor_set(x_335, 3, x_271);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_334);
lean_ctor_set(x_1, 0, x_335);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
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
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint32_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_1, 0);
x_337 = lean_ctor_get(x_1, 1);
x_338 = lean_ctor_get(x_1, 2);
x_339 = lean_ctor_get(x_1, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_1);
x_340 = lean_unbox_uint32(x_337);
x_341 = x_2 < x_340;
x_342 = 1;
x_343 = l_Bool_DecidableEq(x_341, x_342);
if (x_343 == 0)
{
uint32_t x_344; uint8_t x_345; uint8_t x_346; 
x_344 = lean_unbox_uint32(x_337);
x_345 = x_344 < x_2;
x_346 = l_Bool_DecidableEq(x_345, x_342);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_338);
lean_dec(x_337);
x_347 = lean_box_uint32(x_2);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_348, 2, x_3);
lean_ctor_set(x_348, 3, x_339);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
uint8_t x_349; uint8_t x_350; 
x_349 = l_RBNode_isRed___rarg(x_339);
x_350 = l_Bool_DecidableEq(x_349, x_342);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_339, x_2, x_3);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_337);
lean_ctor_set(x_352, 2, x_338);
lean_ctor_set(x_352, 3, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_7);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_339, x_2, x_3);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 3);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = 0;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_356);
lean_ctor_set(x_360, 2, x_357);
lean_ctor_set(x_360, 3, x_355);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_336);
lean_ctor_set(x_362, 1, x_337);
lean_ctor_set(x_362, 2, x_338);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_361);
return x_362;
}
else
{
uint8_t x_363; 
x_363 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = lean_ctor_get(x_353, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_353, 2);
lean_inc(x_365);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_366 = x_353;
} else {
 lean_dec_ref(x_353);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_355, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_355, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_371 = x_355;
} else {
 lean_dec_ref(x_355);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_336);
lean_ctor_set(x_373, 1, x_337);
lean_ctor_set(x_373, 2, x_338);
lean_ctor_set(x_373, 3, x_354);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
if (lean_is_scalar(x_366)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_366;
}
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_368);
lean_ctor_set(x_374, 2, x_369);
lean_ctor_set(x_374, 3, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_372);
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_365);
lean_ctor_set(x_375, 3, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_363);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_353, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_378 = x_353;
} else {
 lean_dec_ref(x_353);
 x_378 = lean_box(0);
}
x_379 = 0;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_354);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_377);
lean_ctor_set(x_380, 3, x_355);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
x_381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_381, 0, x_336);
lean_ctor_set(x_381, 1, x_337);
lean_ctor_set(x_381, 2, x_338);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_363);
return x_381;
}
}
}
else
{
uint8_t x_382; 
x_382 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_383 = lean_ctor_get(x_353, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 3);
lean_inc(x_385);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_386 = x_353;
} else {
 lean_dec_ref(x_353);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_354, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_354, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_354, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_354, 3);
lean_inc(x_390);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_391 = x_354;
} else {
 lean_dec_ref(x_354);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_336);
lean_ctor_set(x_393, 1, x_337);
lean_ctor_set(x_393, 2, x_338);
lean_ctor_set(x_393, 3, x_387);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
if (lean_is_scalar(x_386)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_386;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_385);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_388);
lean_ctor_set(x_395, 2, x_389);
lean_ctor_set(x_395, 3, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_382);
return x_395;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_353, 3);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_353, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_353, 2);
lean_inc(x_398);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_399 = x_353;
} else {
 lean_dec_ref(x_353);
 x_399 = lean_box(0);
}
x_400 = 0;
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_354);
lean_ctor_set(x_401, 1, x_397);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_396);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_336);
lean_ctor_set(x_402, 1, x_337);
lean_ctor_set(x_402, 2, x_338);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_382);
return x_402;
}
else
{
uint8_t x_403; 
x_403 = lean_ctor_get_uint8(x_396, sizeof(void*)*4);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_404 = lean_ctor_get(x_353, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_353, 2);
lean_inc(x_405);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_406 = x_353;
} else {
 lean_dec_ref(x_353);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_396, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_396, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_396, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_396, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 x_411 = x_396;
} else {
 lean_dec_ref(x_396);
 x_411 = lean_box(0);
}
lean_inc(x_354);
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 4, 1);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_336);
lean_ctor_set(x_412, 1, x_337);
lean_ctor_set(x_412, 2, x_338);
lean_ctor_set(x_412, 3, x_354);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_413 = x_354;
} else {
 lean_dec_ref(x_354);
 x_413 = lean_box(0);
}
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_408);
lean_ctor_set(x_414, 2, x_409);
lean_ctor_set(x_414, 3, x_410);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_406)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_406;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_404);
lean_ctor_set(x_415, 2, x_405);
lean_ctor_set(x_415, 3, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_403);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_418 = x_353;
} else {
 lean_dec_ref(x_353);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_354, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_354, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_354, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_354, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_423 = x_354;
} else {
 lean_dec_ref(x_354);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_421);
lean_ctor_set(x_424, 3, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_403);
x_425 = 0;
if (lean_is_scalar(x_418)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_418;
}
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_416);
lean_ctor_set(x_426, 2, x_417);
lean_ctor_set(x_426, 3, x_396);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_336);
lean_ctor_set(x_427, 1, x_337);
lean_ctor_set(x_427, 2, x_338);
lean_ctor_set(x_427, 3, x_426);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_403);
return x_427;
}
}
}
}
}
}
}
else
{
uint8_t x_428; uint8_t x_429; 
x_428 = l_RBNode_isRed___rarg(x_336);
x_429 = l_Bool_DecidableEq(x_428, x_342);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_336, x_2, x_3);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_337);
lean_ctor_set(x_431, 2, x_338);
lean_ctor_set(x_431, 3, x_339);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_7);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_336, x_2, x_3);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_432, 3);
lean_inc(x_434);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; 
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = 0;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_434);
lean_ctor_set(x_439, 1, x_435);
lean_ctor_set(x_439, 2, x_436);
lean_ctor_set(x_439, 3, x_434);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = 1;
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_337);
lean_ctor_set(x_441, 2, x_338);
lean_ctor_set(x_441, 3, x_339);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
return x_441;
}
else
{
uint8_t x_442; 
x_442 = lean_ctor_get_uint8(x_434, sizeof(void*)*4);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_443 = lean_ctor_get(x_432, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 2);
lean_inc(x_444);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_445 = x_432;
} else {
 lean_dec_ref(x_432);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_434, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_434, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_434, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_434, 3);
lean_inc(x_449);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 lean_ctor_release(x_434, 2);
 lean_ctor_release(x_434, 3);
 x_450 = x_434;
} else {
 lean_dec_ref(x_434);
 x_450 = lean_box(0);
}
x_451 = 1;
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_433);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_446);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_449);
lean_ctor_set(x_453, 1, x_337);
lean_ctor_set(x_453, 2, x_338);
lean_ctor_set(x_453, 3, x_339);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_447);
lean_ctor_set(x_454, 2, x_448);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_442);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_432, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_432, 2);
lean_inc(x_456);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_457 = x_432;
} else {
 lean_dec_ref(x_432);
 x_457 = lean_box(0);
}
x_458 = 0;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_433);
lean_ctor_set(x_459, 1, x_455);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_434);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
x_460 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_337);
lean_ctor_set(x_460, 2, x_338);
lean_ctor_set(x_460, 3, x_339);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_442);
return x_460;
}
}
}
else
{
uint8_t x_461; 
x_461 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_462 = lean_ctor_get(x_432, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_432, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_432, 3);
lean_inc(x_464);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_465 = x_432;
} else {
 lean_dec_ref(x_432);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_433, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_433, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_433, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_433, 3);
lean_inc(x_469);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_470 = x_433;
} else {
 lean_dec_ref(x_433);
 x_470 = lean_box(0);
}
x_471 = 1;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(1, 4, 1);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_466);
lean_ctor_set(x_472, 1, x_467);
lean_ctor_set(x_472, 2, x_468);
lean_ctor_set(x_472, 3, x_469);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_465)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_465;
}
lean_ctor_set(x_473, 0, x_464);
lean_ctor_set(x_473, 1, x_337);
lean_ctor_set(x_473, 2, x_338);
lean_ctor_set(x_473, 3, x_339);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_471);
x_474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_462);
lean_ctor_set(x_474, 2, x_463);
lean_ctor_set(x_474, 3, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_461);
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_432, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; 
x_476 = lean_ctor_get(x_432, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_432, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_478 = x_432;
} else {
 lean_dec_ref(x_432);
 x_478 = lean_box(0);
}
x_479 = 0;
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_433);
lean_ctor_set(x_480, 1, x_476);
lean_ctor_set(x_480, 2, x_477);
lean_ctor_set(x_480, 3, x_475);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
x_481 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_337);
lean_ctor_set(x_481, 2, x_338);
lean_ctor_set(x_481, 3, x_339);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_461);
return x_481;
}
else
{
uint8_t x_482; 
x_482 = lean_ctor_get_uint8(x_475, sizeof(void*)*4);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_483 = lean_ctor_get(x_432, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_432, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_485 = x_432;
} else {
 lean_dec_ref(x_432);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_475, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_475, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_475, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_475, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_490 = x_475;
} else {
 lean_dec_ref(x_475);
 x_490 = lean_box(0);
}
lean_inc(x_433);
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_433);
lean_ctor_set(x_491, 1, x_483);
lean_ctor_set(x_491, 2, x_484);
lean_ctor_set(x_491, 3, x_486);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_492 = x_433;
} else {
 lean_dec_ref(x_433);
 x_492 = lean_box(0);
}
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_337);
lean_ctor_set(x_493, 2, x_338);
lean_ctor_set(x_493, 3, x_339);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_485)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_485;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_487);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set(x_494, 3, x_493);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_482);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
x_495 = lean_ctor_get(x_432, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_432, 2);
lean_inc(x_496);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_497 = x_432;
} else {
 lean_dec_ref(x_432);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_433, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_433, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_433, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_433, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_502 = x_433;
} else {
 lean_dec_ref(x_433);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 4, 1);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_482);
x_504 = 0;
if (lean_is_scalar(x_497)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_497;
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_495);
lean_ctor_set(x_505, 2, x_496);
lean_ctor_set(x_505, 3, x_475);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_337);
lean_ctor_set(x_506, 2, x_338);
lean_ctor_set(x_506, 3, x_339);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_482);
return x_506;
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
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_unbox_uint32(x_10);
x_18 = x_17 < x_2;
x_19 = l_Bool_DecidableEq(x_18, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
else
{
lean_object* x_21; 
x_21 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_21);
return x_1;
}
}
else
{
lean_object* x_22; 
x_22 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_27 = lean_unbox_uint32(x_24);
x_28 = x_2 < x_27;
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; uint8_t x_33; 
x_31 = lean_unbox_uint32(x_24);
x_32 = x_31 < x_2;
x_33 = l_Bool_DecidableEq(x_32, x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_24);
x_34 = lean_box_uint32(x_2);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_7);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_26, x_2, x_3);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_25);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_23, x_2, x_3);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set(x_39, 3, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_7);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_unbox_uint32(x_42);
x_46 = x_2 < x_45;
x_47 = 1;
x_48 = l_Bool_DecidableEq(x_46, x_47);
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_unbox_uint32(x_42);
x_50 = x_49 < x_2;
x_51 = l_Bool_DecidableEq(x_50, x_47);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_42);
x_52 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_52);
return x_1;
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = l_RBNode_isRed___rarg(x_44);
x_54 = l_Bool_DecidableEq(x_53, x_47);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_44, x_2, x_3);
lean_ctor_set(x_1, 3, x_55);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_44, x_2, x_3);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = 0;
lean_ctor_set(x_56, 0, x_58);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_62);
x_63 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_63);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_56, 1);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = 0;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = 1;
lean_ctor_set(x_1, 3, x_67);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_68);
return x_1;
}
}
else
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_56, 1);
x_72 = lean_ctor_get(x_56, 2);
x_73 = lean_ctor_get(x_56, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_56, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
x_78 = lean_ctor_get(x_58, 2);
x_79 = lean_ctor_get(x_58, 3);
x_80 = 1;
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_80);
lean_ctor_set(x_56, 3, x_79);
lean_ctor_set(x_56, 2, x_78);
lean_ctor_set(x_56, 1, x_77);
lean_ctor_set(x_56, 0, x_76);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_80);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_58);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
x_83 = lean_ctor_get(x_58, 2);
x_84 = lean_ctor_get(x_58, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_85 = 1;
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_41);
lean_ctor_set(x_86, 1, x_42);
lean_ctor_set(x_86, 2, x_43);
lean_ctor_set(x_86, 3, x_57);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
lean_ctor_set(x_56, 3, x_84);
lean_ctor_set(x_56, 2, x_83);
lean_ctor_set(x_56, 1, x_82);
lean_ctor_set(x_56, 0, x_81);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_85);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_72);
lean_ctor_set(x_1, 1, x_71);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_56, 1);
x_88 = lean_ctor_get(x_56, 2);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_56);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_58, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_58, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_93 = x_58;
} else {
 lean_dec_ref(x_58);
 x_93 = lean_box(0);
}
x_94 = 1;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(1, 4, 1);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_41);
lean_ctor_set(x_95, 1, x_42);
lean_ctor_set(x_95, 2, x_43);
lean_ctor_set(x_95, 3, x_57);
lean_ctor_set_uint8(x_95, sizeof(void*)*4, x_94);
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_89);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_94);
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set(x_1, 2, x_88);
lean_ctor_set(x_1, 1, x_87);
lean_ctor_set(x_1, 0, x_95);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_56);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_56, 3);
lean_dec(x_98);
x_99 = lean_ctor_get(x_56, 0);
lean_dec(x_99);
x_100 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_56, 1);
x_102 = lean_ctor_get(x_56, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = 0;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_57);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_102);
lean_ctor_set(x_104, 3, x_58);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_104);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
}
}
else
{
uint8_t x_105; 
x_105 = lean_ctor_get_uint8(x_57, sizeof(void*)*4);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_56);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_56, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_57);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_109 = lean_ctor_get(x_57, 0);
x_110 = lean_ctor_get(x_57, 1);
x_111 = lean_ctor_get(x_57, 2);
x_112 = lean_ctor_get(x_57, 3);
x_113 = 1;
lean_ctor_set(x_57, 3, x_109);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 1, x_42);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_113);
lean_ctor_set(x_56, 0, x_112);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_113);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_57, 0);
x_115 = lean_ctor_get(x_57, 1);
x_116 = lean_ctor_get(x_57, 2);
x_117 = lean_ctor_get(x_57, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_57);
x_118 = 1;
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_41);
lean_ctor_set(x_119, 1, x_42);
lean_ctor_set(x_119, 2, x_43);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
lean_ctor_set(x_56, 0, x_117);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set(x_1, 2, x_116);
lean_ctor_set(x_1, 1, x_115);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_56, 1);
x_121 = lean_ctor_get(x_56, 2);
x_122 = lean_ctor_get(x_56, 3);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_56);
x_123 = lean_ctor_get(x_57, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_57, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_57, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_57, 3);
lean_inc(x_126);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_127 = x_57;
} else {
 lean_dec_ref(x_57);
 x_127 = lean_box(0);
}
x_128 = 1;
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_41);
lean_ctor_set(x_129, 1, x_42);
lean_ctor_set(x_129, 2, x_43);
lean_ctor_set(x_129, 3, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
x_130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_120);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_130);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_56, 3);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_56);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_56, 3);
lean_dec(x_133);
x_134 = lean_ctor_get(x_56, 0);
lean_dec(x_134);
x_135 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_135);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_56, 1);
x_137 = lean_ctor_get(x_56, 2);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_56);
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_57);
lean_ctor_set(x_139, 1, x_136);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_139, 3, x_131);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_138);
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_105);
return x_1;
}
}
else
{
uint8_t x_140; 
x_140 = lean_ctor_get_uint8(x_131, sizeof(void*)*4);
if (x_140 == 0)
{
uint8_t x_141; 
lean_free_object(x_1);
x_141 = !lean_is_exclusive(x_56);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_56, 3);
lean_dec(x_142);
x_143 = lean_ctor_get(x_56, 0);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = lean_ctor_get(x_131, 0);
x_146 = lean_ctor_get(x_131, 1);
x_147 = lean_ctor_get(x_131, 2);
x_148 = lean_ctor_get(x_131, 3);
lean_inc(x_57);
lean_ctor_set(x_131, 3, x_57);
lean_ctor_set(x_131, 2, x_43);
lean_ctor_set(x_131, 1, x_42);
lean_ctor_set(x_131, 0, x_41);
x_149 = !lean_is_exclusive(x_57);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_57, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_57, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_57, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_57, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
lean_ctor_set(x_57, 3, x_148);
lean_ctor_set(x_57, 2, x_147);
lean_ctor_set(x_57, 1, x_146);
lean_ctor_set(x_57, 0, x_145);
lean_ctor_set(x_56, 3, x_57);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
else
{
lean_object* x_154; 
lean_dec(x_57);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_105);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_147);
lean_ctor_set(x_154, 3, x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_154);
lean_ctor_set(x_56, 0, x_131);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_131, 0);
x_156 = lean_ctor_get(x_131, 1);
x_157 = lean_ctor_get(x_131, 2);
x_158 = lean_ctor_get(x_131, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_131);
lean_inc(x_57);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_41);
lean_ctor_set(x_159, 1, x_42);
lean_ctor_set(x_159, 2, x_43);
lean_ctor_set(x_159, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_160 = x_57;
} else {
 lean_dec_ref(x_57);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_155);
lean_ctor_set(x_161, 1, x_156);
lean_ctor_set(x_161, 2, x_157);
lean_ctor_set(x_161, 3, x_158);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_105);
lean_ctor_set(x_56, 3, x_161);
lean_ctor_set(x_56, 0, x_159);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_140);
return x_56;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_162 = lean_ctor_get(x_56, 1);
x_163 = lean_ctor_get(x_56, 2);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_56);
x_164 = lean_ctor_get(x_131, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_131, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_131, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_131, 3);
lean_inc(x_167);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_168 = x_131;
} else {
 lean_dec_ref(x_131);
 x_168 = lean_box(0);
}
lean_inc(x_57);
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 4, 1);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_41);
lean_ctor_set(x_169, 1, x_42);
lean_ctor_set(x_169, 2, x_43);
lean_ctor_set(x_169, 3, x_57);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_170 = x_57;
} else {
 lean_dec_ref(x_57);
 x_170 = lean_box(0);
}
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_105);
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 4, 1);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_165);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_105);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_162);
lean_ctor_set(x_172, 2, x_163);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_140);
return x_172;
}
}
else
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_56);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_56, 3);
lean_dec(x_174);
x_175 = lean_ctor_get(x_56, 0);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_57);
if (x_176 == 0)
{
uint8_t x_177; 
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_140);
x_177 = 0;
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_177);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_178 = lean_ctor_get(x_57, 0);
x_179 = lean_ctor_get(x_57, 1);
x_180 = lean_ctor_get(x_57, 2);
x_181 = lean_ctor_get(x_57, 3);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_57);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_179);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_140);
x_183 = 0;
lean_ctor_set(x_56, 0, x_182);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_183);
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
return x_1;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
x_184 = lean_ctor_get(x_56, 1);
x_185 = lean_ctor_get(x_56, 2);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_56);
x_186 = lean_ctor_get(x_57, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_57, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_57, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_57, 3);
lean_inc(x_189);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 x_190 = x_57;
} else {
 lean_dec_ref(x_57);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 4, 1);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_186);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
lean_ctor_set(x_191, 3, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_140);
x_192 = 0;
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_184);
lean_ctor_set(x_193, 2, x_185);
lean_ctor_set(x_193, 3, x_131);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_192);
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_140);
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
uint8_t x_194; uint8_t x_195; 
x_194 = l_RBNode_isRed___rarg(x_41);
x_195 = l_Bool_DecidableEq(x_194, x_47);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_41, x_2, x_3);
lean_ctor_set(x_1, 0, x_196);
return x_1;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_41, x_2, x_3);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 3);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_197);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_197, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_197, 0);
lean_dec(x_202);
x_203 = 0;
lean_ctor_set(x_197, 0, x_199);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_203);
x_204 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_197, 1);
x_206 = lean_ctor_get(x_197, 2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_197);
x_207 = 0;
x_208 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_208, 0, x_199);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_206);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_207);
x_209 = 1;
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_209);
return x_1;
}
}
else
{
uint8_t x_210; 
x_210 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
if (x_210 == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_197);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_212 = lean_ctor_get(x_197, 1);
x_213 = lean_ctor_get(x_197, 2);
x_214 = lean_ctor_get(x_197, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_197, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_199);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_199, 0);
x_218 = lean_ctor_get(x_199, 1);
x_219 = lean_ctor_get(x_199, 2);
x_220 = lean_ctor_get(x_199, 3);
x_221 = 1;
lean_ctor_set(x_199, 3, x_217);
lean_ctor_set(x_199, 2, x_213);
lean_ctor_set(x_199, 1, x_212);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_221);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_220);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_221);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_199, 0);
x_223 = lean_ctor_get(x_199, 1);
x_224 = lean_ctor_get(x_199, 2);
x_225 = lean_ctor_get(x_199, 3);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_199);
x_226 = 1;
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_198);
lean_ctor_set(x_227, 1, x_212);
lean_ctor_set(x_227, 2, x_213);
lean_ctor_set(x_227, 3, x_222);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_226);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_225);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_226);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_227);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_197, 1);
x_229 = lean_ctor_get(x_197, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_197);
x_230 = lean_ctor_get(x_199, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_199, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_199, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_199, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_234 = x_199;
} else {
 lean_dec_ref(x_199);
 x_234 = lean_box(0);
}
x_235 = 1;
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(1, 4, 1);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_198);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set(x_236, 2, x_229);
lean_ctor_set(x_236, 3, x_230);
lean_ctor_set_uint8(x_236, sizeof(void*)*4, x_235);
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_42);
lean_ctor_set(x_237, 2, x_43);
lean_ctor_set(x_237, 3, x_44);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_235);
lean_ctor_set(x_1, 3, x_237);
lean_ctor_set(x_1, 2, x_232);
lean_ctor_set(x_1, 1, x_231);
lean_ctor_set(x_1, 0, x_236);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
else
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_197);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_197, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_197, 0);
lean_dec(x_240);
x_241 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_241);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_197, 1);
x_243 = lean_ctor_get(x_197, 2);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_197);
x_244 = 0;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_198);
lean_ctor_set(x_245, 1, x_242);
lean_ctor_set(x_245, 2, x_243);
lean_ctor_set(x_245, 3, x_199);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_210);
return x_1;
}
}
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_198, sizeof(void*)*4);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_197);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_197, 1);
x_249 = lean_ctor_get(x_197, 2);
x_250 = lean_ctor_get(x_197, 3);
x_251 = lean_ctor_get(x_197, 0);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_198);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = 1;
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_253);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_253);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_198, 0);
x_255 = lean_ctor_get(x_198, 1);
x_256 = lean_ctor_get(x_198, 2);
x_257 = lean_ctor_get(x_198, 3);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_198);
x_258 = 1;
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_254);
lean_ctor_set(x_259, 1, x_255);
lean_ctor_set(x_259, 2, x_256);
lean_ctor_set(x_259, 3, x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
lean_ctor_set(x_197, 3, x_44);
lean_ctor_set(x_197, 2, x_43);
lean_ctor_set(x_197, 1, x_42);
lean_ctor_set(x_197, 0, x_250);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_197);
lean_ctor_set(x_1, 2, x_249);
lean_ctor_set(x_1, 1, x_248);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; 
x_260 = lean_ctor_get(x_197, 1);
x_261 = lean_ctor_get(x_197, 2);
x_262 = lean_ctor_get(x_197, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_197);
x_263 = lean_ctor_get(x_198, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_198, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_198, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_198, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_267 = x_198;
} else {
 lean_dec_ref(x_198);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_42);
lean_ctor_set(x_270, 2, x_43);
lean_ctor_set(x_270, 3, x_44);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_197, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_197);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_197, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_197, 0);
lean_dec(x_274);
x_275 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_275);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_197, 1);
x_277 = lean_ctor_get(x_197, 2);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_197);
x_278 = 0;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_198);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_279, 2, x_277);
lean_ctor_set(x_279, 3, x_271);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
lean_ctor_set(x_1, 0, x_279);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
return x_1;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_197);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_197, 1);
x_283 = lean_ctor_get(x_197, 2);
x_284 = lean_ctor_get(x_197, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_197, 0);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_271);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_271, 0);
x_288 = lean_ctor_get(x_271, 1);
x_289 = lean_ctor_get(x_271, 2);
x_290 = lean_ctor_get(x_271, 3);
lean_inc(x_198);
lean_ctor_set(x_271, 3, x_287);
lean_ctor_set(x_271, 2, x_283);
lean_ctor_set(x_271, 1, x_282);
lean_ctor_set(x_271, 0, x_198);
x_291 = !lean_is_exclusive(x_198);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_198, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_198, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_198, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_198, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
lean_ctor_set(x_198, 3, x_44);
lean_ctor_set(x_198, 2, x_43);
lean_ctor_set(x_198, 1, x_42);
lean_ctor_set(x_198, 0, x_290);
lean_ctor_set(x_197, 3, x_198);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
else
{
lean_object* x_296; 
lean_dec(x_198);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_290);
lean_ctor_set(x_296, 1, x_42);
lean_ctor_set(x_296, 2, x_43);
lean_ctor_set(x_296, 3, x_44);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_296);
lean_ctor_set(x_197, 2, x_289);
lean_ctor_set(x_197, 1, x_288);
lean_ctor_set(x_197, 0, x_271);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_297 = lean_ctor_get(x_271, 0);
x_298 = lean_ctor_get(x_271, 1);
x_299 = lean_ctor_get(x_271, 2);
x_300 = lean_ctor_get(x_271, 3);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_271);
lean_inc(x_198);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_198);
lean_ctor_set(x_301, 1, x_282);
lean_ctor_set(x_301, 2, x_283);
lean_ctor_set(x_301, 3, x_297);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_302 = x_198;
} else {
 lean_dec_ref(x_198);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_42);
lean_ctor_set(x_303, 2, x_43);
lean_ctor_set(x_303, 3, x_44);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_246);
lean_ctor_set(x_197, 3, x_303);
lean_ctor_set(x_197, 2, x_299);
lean_ctor_set(x_197, 1, x_298);
lean_ctor_set(x_197, 0, x_301);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_280);
return x_197;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_304 = lean_ctor_get(x_197, 1);
x_305 = lean_ctor_get(x_197, 2);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_197);
x_306 = lean_ctor_get(x_271, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_271, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_271, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_271, 3);
lean_inc(x_309);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_310 = x_271;
} else {
 lean_dec_ref(x_271);
 x_310 = lean_box(0);
}
lean_inc(x_198);
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 4, 1);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_198);
lean_ctor_set(x_311, 1, x_304);
lean_ctor_set(x_311, 2, x_305);
lean_ctor_set(x_311, 3, x_306);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_312 = x_198;
} else {
 lean_dec_ref(x_198);
 x_312 = lean_box(0);
}
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 4, 1);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_42);
lean_ctor_set(x_313, 2, x_43);
lean_ctor_set(x_313, 3, x_44);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_246);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_307);
lean_ctor_set(x_314, 2, x_308);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_280);
return x_314;
}
}
else
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_197);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_197, 3);
lean_dec(x_316);
x_317 = lean_ctor_get(x_197, 0);
lean_dec(x_317);
x_318 = !lean_is_exclusive(x_198);
if (x_318 == 0)
{
uint8_t x_319; 
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_280);
x_319 = 0;
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_319);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_198, 0);
x_321 = lean_ctor_get(x_198, 1);
x_322 = lean_ctor_get(x_198, 2);
x_323 = lean_ctor_get(x_198, 3);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_198);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_320);
lean_ctor_set(x_324, 1, x_321);
lean_ctor_set(x_324, 2, x_322);
lean_ctor_set(x_324, 3, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_280);
x_325 = 0;
lean_ctor_set(x_197, 0, x_324);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_325);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
return x_1;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; 
x_326 = lean_ctor_get(x_197, 1);
x_327 = lean_ctor_get(x_197, 2);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_197);
x_328 = lean_ctor_get(x_198, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_198, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_198, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_198, 3);
lean_inc(x_331);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 x_332 = x_198;
} else {
 lean_dec_ref(x_198);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 4, 1);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_328);
lean_ctor_set(x_333, 1, x_329);
lean_ctor_set(x_333, 2, x_330);
lean_ctor_set(x_333, 3, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_280);
x_334 = 0;
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_326);
lean_ctor_set(x_335, 2, x_327);
lean_ctor_set(x_335, 3, x_271);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_334);
lean_ctor_set(x_1, 0, x_335);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_280);
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
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint32_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_1, 0);
x_337 = lean_ctor_get(x_1, 1);
x_338 = lean_ctor_get(x_1, 2);
x_339 = lean_ctor_get(x_1, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_1);
x_340 = lean_unbox_uint32(x_337);
x_341 = x_2 < x_340;
x_342 = 1;
x_343 = l_Bool_DecidableEq(x_341, x_342);
if (x_343 == 0)
{
uint32_t x_344; uint8_t x_345; uint8_t x_346; 
x_344 = lean_unbox_uint32(x_337);
x_345 = x_344 < x_2;
x_346 = l_Bool_DecidableEq(x_345, x_342);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_338);
lean_dec(x_337);
x_347 = lean_box_uint32(x_2);
x_348 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_347);
lean_ctor_set(x_348, 2, x_3);
lean_ctor_set(x_348, 3, x_339);
lean_ctor_set_uint8(x_348, sizeof(void*)*4, x_7);
return x_348;
}
else
{
uint8_t x_349; uint8_t x_350; 
x_349 = l_RBNode_isRed___rarg(x_339);
x_350 = l_Bool_DecidableEq(x_349, x_342);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_339, x_2, x_3);
x_352 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_337);
lean_ctor_set(x_352, 2, x_338);
lean_ctor_set(x_352, 3, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*4, x_7);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_339, x_2, x_3);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 3);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = 0;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_355);
lean_ctor_set(x_360, 1, x_356);
lean_ctor_set(x_360, 2, x_357);
lean_ctor_set(x_360, 3, x_355);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
x_361 = 1;
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_336);
lean_ctor_set(x_362, 1, x_337);
lean_ctor_set(x_362, 2, x_338);
lean_ctor_set(x_362, 3, x_360);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_361);
return x_362;
}
else
{
uint8_t x_363; 
x_363 = lean_ctor_get_uint8(x_355, sizeof(void*)*4);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_364 = lean_ctor_get(x_353, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_353, 2);
lean_inc(x_365);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_366 = x_353;
} else {
 lean_dec_ref(x_353);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_355, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_355, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_355, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 x_371 = x_355;
} else {
 lean_dec_ref(x_355);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_336);
lean_ctor_set(x_373, 1, x_337);
lean_ctor_set(x_373, 2, x_338);
lean_ctor_set(x_373, 3, x_354);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
if (lean_is_scalar(x_366)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_366;
}
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_368);
lean_ctor_set(x_374, 2, x_369);
lean_ctor_set(x_374, 3, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_372);
x_375 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_365);
lean_ctor_set(x_375, 3, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_363);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; 
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_353, 2);
lean_inc(x_377);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_378 = x_353;
} else {
 lean_dec_ref(x_353);
 x_378 = lean_box(0);
}
x_379 = 0;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_354);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_377);
lean_ctor_set(x_380, 3, x_355);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
x_381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_381, 0, x_336);
lean_ctor_set(x_381, 1, x_337);
lean_ctor_set(x_381, 2, x_338);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_363);
return x_381;
}
}
}
else
{
uint8_t x_382; 
x_382 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_383 = lean_ctor_get(x_353, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 3);
lean_inc(x_385);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_386 = x_353;
} else {
 lean_dec_ref(x_353);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_354, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_354, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_354, 2);
lean_inc(x_389);
x_390 = lean_ctor_get(x_354, 3);
lean_inc(x_390);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_391 = x_354;
} else {
 lean_dec_ref(x_354);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_336);
lean_ctor_set(x_393, 1, x_337);
lean_ctor_set(x_393, 2, x_338);
lean_ctor_set(x_393, 3, x_387);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
if (lean_is_scalar(x_386)) {
 x_394 = lean_alloc_ctor(1, 4, 1);
} else {
 x_394 = x_386;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_385);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_388);
lean_ctor_set(x_395, 2, x_389);
lean_ctor_set(x_395, 3, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_382);
return x_395;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_353, 3);
lean_inc(x_396);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_353, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_353, 2);
lean_inc(x_398);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_399 = x_353;
} else {
 lean_dec_ref(x_353);
 x_399 = lean_box(0);
}
x_400 = 0;
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_354);
lean_ctor_set(x_401, 1, x_397);
lean_ctor_set(x_401, 2, x_398);
lean_ctor_set(x_401, 3, x_396);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_400);
x_402 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_402, 0, x_336);
lean_ctor_set(x_402, 1, x_337);
lean_ctor_set(x_402, 2, x_338);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_382);
return x_402;
}
else
{
uint8_t x_403; 
x_403 = lean_ctor_get_uint8(x_396, sizeof(void*)*4);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_404 = lean_ctor_get(x_353, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_353, 2);
lean_inc(x_405);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_406 = x_353;
} else {
 lean_dec_ref(x_353);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_396, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_396, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_396, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_396, 3);
lean_inc(x_410);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 lean_ctor_release(x_396, 2);
 lean_ctor_release(x_396, 3);
 x_411 = x_396;
} else {
 lean_dec_ref(x_396);
 x_411 = lean_box(0);
}
lean_inc(x_354);
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 4, 1);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_336);
lean_ctor_set(x_412, 1, x_337);
lean_ctor_set(x_412, 2, x_338);
lean_ctor_set(x_412, 3, x_354);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_413 = x_354;
} else {
 lean_dec_ref(x_354);
 x_413 = lean_box(0);
}
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 4, 1);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_408);
lean_ctor_set(x_414, 2, x_409);
lean_ctor_set(x_414, 3, x_410);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_382);
if (lean_is_scalar(x_406)) {
 x_415 = lean_alloc_ctor(1, 4, 1);
} else {
 x_415 = x_406;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_404);
lean_ctor_set(x_415, 2, x_405);
lean_ctor_set(x_415, 3, x_414);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_403);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; 
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_418 = x_353;
} else {
 lean_dec_ref(x_353);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_354, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_354, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_354, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_354, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_423 = x_354;
} else {
 lean_dec_ref(x_354);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_421);
lean_ctor_set(x_424, 3, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_403);
x_425 = 0;
if (lean_is_scalar(x_418)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_418;
}
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_416);
lean_ctor_set(x_426, 2, x_417);
lean_ctor_set(x_426, 3, x_396);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_336);
lean_ctor_set(x_427, 1, x_337);
lean_ctor_set(x_427, 2, x_338);
lean_ctor_set(x_427, 3, x_426);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_403);
return x_427;
}
}
}
}
}
}
}
else
{
uint8_t x_428; uint8_t x_429; 
x_428 = l_RBNode_isRed___rarg(x_336);
x_429 = l_Bool_DecidableEq(x_428, x_342);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
x_430 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_336, x_2, x_3);
x_431 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_337);
lean_ctor_set(x_431, 2, x_338);
lean_ctor_set(x_431, 3, x_339);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_7);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_336, x_2, x_3);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_432, 3);
lean_inc(x_434);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; 
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_432, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_437 = x_432;
} else {
 lean_dec_ref(x_432);
 x_437 = lean_box(0);
}
x_438 = 0;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_434);
lean_ctor_set(x_439, 1, x_435);
lean_ctor_set(x_439, 2, x_436);
lean_ctor_set(x_439, 3, x_434);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = 1;
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_337);
lean_ctor_set(x_441, 2, x_338);
lean_ctor_set(x_441, 3, x_339);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
return x_441;
}
else
{
uint8_t x_442; 
x_442 = lean_ctor_get_uint8(x_434, sizeof(void*)*4);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_443 = lean_ctor_get(x_432, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_432, 2);
lean_inc(x_444);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_445 = x_432;
} else {
 lean_dec_ref(x_432);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_434, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_434, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_434, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_434, 3);
lean_inc(x_449);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 lean_ctor_release(x_434, 2);
 lean_ctor_release(x_434, 3);
 x_450 = x_434;
} else {
 lean_dec_ref(x_434);
 x_450 = lean_box(0);
}
x_451 = 1;
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_433);
lean_ctor_set(x_452, 1, x_443);
lean_ctor_set(x_452, 2, x_444);
lean_ctor_set(x_452, 3, x_446);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_449);
lean_ctor_set(x_453, 1, x_337);
lean_ctor_set(x_453, 2, x_338);
lean_ctor_set(x_453, 3, x_339);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_447);
lean_ctor_set(x_454, 2, x_448);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_442);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_ctor_get(x_432, 1);
lean_inc(x_455);
x_456 = lean_ctor_get(x_432, 2);
lean_inc(x_456);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_457 = x_432;
} else {
 lean_dec_ref(x_432);
 x_457 = lean_box(0);
}
x_458 = 0;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_433);
lean_ctor_set(x_459, 1, x_455);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_434);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
x_460 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_337);
lean_ctor_set(x_460, 2, x_338);
lean_ctor_set(x_460, 3, x_339);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_442);
return x_460;
}
}
}
else
{
uint8_t x_461; 
x_461 = lean_ctor_get_uint8(x_433, sizeof(void*)*4);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_462 = lean_ctor_get(x_432, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_432, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_432, 3);
lean_inc(x_464);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_465 = x_432;
} else {
 lean_dec_ref(x_432);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_433, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_433, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_433, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_433, 3);
lean_inc(x_469);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_470 = x_433;
} else {
 lean_dec_ref(x_433);
 x_470 = lean_box(0);
}
x_471 = 1;
if (lean_is_scalar(x_470)) {
 x_472 = lean_alloc_ctor(1, 4, 1);
} else {
 x_472 = x_470;
}
lean_ctor_set(x_472, 0, x_466);
lean_ctor_set(x_472, 1, x_467);
lean_ctor_set(x_472, 2, x_468);
lean_ctor_set(x_472, 3, x_469);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_465)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_465;
}
lean_ctor_set(x_473, 0, x_464);
lean_ctor_set(x_473, 1, x_337);
lean_ctor_set(x_473, 2, x_338);
lean_ctor_set(x_473, 3, x_339);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_471);
x_474 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_462);
lean_ctor_set(x_474, 2, x_463);
lean_ctor_set(x_474, 3, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_461);
return x_474;
}
else
{
lean_object* x_475; 
x_475 = lean_ctor_get(x_432, 3);
lean_inc(x_475);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; 
x_476 = lean_ctor_get(x_432, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_432, 2);
lean_inc(x_477);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_478 = x_432;
} else {
 lean_dec_ref(x_432);
 x_478 = lean_box(0);
}
x_479 = 0;
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_433);
lean_ctor_set(x_480, 1, x_476);
lean_ctor_set(x_480, 2, x_477);
lean_ctor_set(x_480, 3, x_475);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
x_481 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_337);
lean_ctor_set(x_481, 2, x_338);
lean_ctor_set(x_481, 3, x_339);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_461);
return x_481;
}
else
{
uint8_t x_482; 
x_482 = lean_ctor_get_uint8(x_475, sizeof(void*)*4);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_483 = lean_ctor_get(x_432, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_432, 2);
lean_inc(x_484);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_485 = x_432;
} else {
 lean_dec_ref(x_432);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_475, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_475, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_475, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_475, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_490 = x_475;
} else {
 lean_dec_ref(x_475);
 x_490 = lean_box(0);
}
lean_inc(x_433);
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_433);
lean_ctor_set(x_491, 1, x_483);
lean_ctor_set(x_491, 2, x_484);
lean_ctor_set(x_491, 3, x_486);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_492 = x_433;
} else {
 lean_dec_ref(x_433);
 x_492 = lean_box(0);
}
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_489);
lean_ctor_set(x_493, 1, x_337);
lean_ctor_set(x_493, 2, x_338);
lean_ctor_set(x_493, 3, x_339);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_485)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_485;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_487);
lean_ctor_set(x_494, 2, x_488);
lean_ctor_set(x_494, 3, x_493);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_482);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; 
x_495 = lean_ctor_get(x_432, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_432, 2);
lean_inc(x_496);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_497 = x_432;
} else {
 lean_dec_ref(x_432);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_433, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_433, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_433, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_433, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 lean_ctor_release(x_433, 2);
 lean_ctor_release(x_433, 3);
 x_502 = x_433;
} else {
 lean_dec_ref(x_433);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 4, 1);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_498);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_482);
x_504 = 0;
if (lean_is_scalar(x_497)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_497;
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_495);
lean_ctor_set(x_505, 2, x_496);
lean_ctor_set(x_505, 3, x_475);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
x_506 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_337);
lean_ctor_set(x_506, 2, x_338);
lean_ctor_set(x_506, 3, x_339);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_482);
return x_506;
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
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
}
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_11 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg(x_7, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_10);
lean_dec(x_10);
x_13 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg(x_7, x_9, x_12);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_2, x_14, x_10);
lean_dec(x_10);
x_16 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg(x_7, x_9, x_15);
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
x_23 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg(x_19, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l___private_Init_Lean_Parser_Trie_1__insertEmptyAux___main___rarg(x_1, x_2, x_22);
lean_dec(x_22);
x_25 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg(x_19, x_21, x_24);
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
x_28 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_2, x_27, x_22);
lean_dec(x_22);
x_29 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg(x_19, x_21, x_28);
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
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_RBNode_insert___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__5___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_2__insertAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_2__insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_2__insertAux___rarg(x_1, x_2, x_3, x_4);
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
x_5 = l___private_Init_Lean_Parser_Trie_2__insertAux___main___rarg(x_2, x_3, x_1, x_4);
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
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
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
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_4);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_13 = x_12 < x_2;
x_14 = l_Bool_DecidableEq(x_13, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
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
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg(x_5, x_7);
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
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_3__findAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_3__findAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_3__findAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_3__findAux___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Parser_Trie_find___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Lean_Parser_Trie_3__findAux___main___rarg(x_2, x_1, x_3);
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
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg(lean_object* x_1, uint32_t x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
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
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_4);
x_12 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_13 = x_12 < x_2;
x_14 = l_Bool_DecidableEq(x_13, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
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
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean_dec(x_4);
x_9 = lean_string_utf8_get(x_1, x_3);
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_11 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg(x_6, x_9);
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
x_14 = l___private_Init_Lean_Parser_Trie_4__updtAcc___rarg(x_5, x_3, x_4);
lean_dec(x_4);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___spec__1___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___rarg(x_1, x_2, x_3, x_4);
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
x_6 = l___private_Init_Lean_Parser_Trie_5__matchPrefixAux___main___rarg(x_1, x_2, x_3, x_5);
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
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(x_4, x_2);
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2___rarg(x_1, x_3);
x_8 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_9 = l_Char_quoteCore(x_8);
x_10 = l_Char_HasRepr___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_string_append(x_11, x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg(x_5);
x_15 = lean_box(1);
x_16 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(x_14, x_15);
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
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = l_RBNode_fold___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__2___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Parser_Trie_6__toStringAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Parser_Trie_6__toStringAux___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Parser_Trie_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Init_Lean_Parser_Trie_6__toStringAux___main___rarg(x_1);
x_3 = lean_box(1);
x_4 = l_Lean_Format_joinSep___main___at___private_Init_Lean_Parser_Trie_6__toStringAux___main___spec__1(x_2, x_3);
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
lean_object* initialize_Init_Lean_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Trie(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Format(lean_io_mk_world());
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
