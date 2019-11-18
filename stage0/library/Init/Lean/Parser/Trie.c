// Lean compiler output
// Module: Init.Lean.Parser.Trie
// Imports: Init.Data.RBMap.Default Init.Lean.Format
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = lean_unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
}
else
{
lean_object* x_19; 
x_19 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = lean_unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = lean_box_uint32(x_2);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_23, x_2, x_3);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_20, x_2, x_3);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = lean_unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_36);
x_43 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_38, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_38, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_35);
lean_ctor_set(x_109, 1, x_36);
lean_ctor_set(x_109, 2, x_37);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_36);
lean_ctor_set(x_119, 2, x_37);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_35);
lean_ctor_set(x_149, 1, x_36);
lean_ctor_set(x_149, 2, x_37);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_159, 2, x_37);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_35, x_2, x_3);
lean_ctor_set(x_1, 0, x_185);
return x_1;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_35, x_2, x_3);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 3);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_186, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_186, 0);
lean_dec(x_191);
x_192 = 0;
lean_ctor_set(x_186, 0, x_188);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_186, 1);
x_195 = lean_ctor_get(x_186, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_186);
x_196 = 0;
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8_t x_199; 
x_199 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_186);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_186, 1);
x_202 = lean_ctor_get(x_186, 2);
x_203 = lean_ctor_get(x_186, 3);
lean_dec(x_203);
x_204 = lean_ctor_get(x_186, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
x_208 = lean_ctor_get(x_188, 2);
x_209 = lean_ctor_get(x_188, 3);
x_210 = 1;
lean_ctor_set(x_188, 3, x_206);
lean_ctor_set(x_188, 2, x_202);
lean_ctor_set(x_188, 1, x_201);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_210);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_209);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_210);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_208);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_188, 0);
x_212 = lean_ctor_get(x_188, 1);
x_213 = lean_ctor_get(x_188, 2);
x_214 = lean_ctor_get(x_188, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_188);
x_215 = 1;
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_187);
lean_ctor_set(x_216, 1, x_201);
lean_ctor_set(x_216, 2, x_202);
lean_ctor_set(x_216, 3, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_215);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_214);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_213);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_186, 1);
x_218 = lean_ctor_get(x_186, 2);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_186);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_188, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_223 = x_188;
} else {
 lean_dec_ref(x_188);
 x_223 = lean_box(0);
}
x_224 = 1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_187);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_218);
lean_ctor_set(x_225, 3, x_219);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
x_226 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_36);
lean_ctor_set(x_226, 2, x_37);
lean_ctor_set(x_226, 3, x_38);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_224);
lean_ctor_set(x_1, 3, x_226);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_186);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_186, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_186, 0);
lean_dec(x_229);
x_230 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_230);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_186, 1);
x_232 = lean_ctor_get(x_186, 2);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_186);
x_233 = 0;
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_187);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
lean_ctor_set(x_234, 3, x_188);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 0, x_234);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8_t x_235; 
x_235 = lean_ctor_get_uint8(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_186);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_186, 1);
x_238 = lean_ctor_get(x_186, 2);
x_239 = lean_ctor_get(x_186, 3);
x_240 = lean_ctor_get(x_186, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_187);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = 1;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_242);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_242);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_187, 0);
x_244 = lean_ctor_get(x_187, 1);
x_245 = lean_ctor_get(x_187, 2);
x_246 = lean_ctor_get(x_187, 3);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_187);
x_247 = 1;
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_245);
lean_ctor_set(x_248, 3, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_249 = lean_ctor_get(x_186, 1);
x_250 = lean_ctor_get(x_186, 2);
x_251 = lean_ctor_get(x_186, 3);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_186);
x_252 = lean_ctor_get(x_187, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_187, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_187, 3);
lean_inc(x_255);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_256 = x_187;
} else {
 lean_dec_ref(x_187);
 x_256 = lean_box(0);
}
x_257 = 1;
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_253);
lean_ctor_set(x_258, 2, x_254);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_36);
lean_ctor_set(x_259, 2, x_37);
lean_ctor_set(x_259, 3, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 3, x_259);
lean_ctor_set(x_1, 2, x_250);
lean_ctor_set(x_1, 1, x_249);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_186, 3);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_186);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_186, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_186, 0);
lean_dec(x_263);
x_264 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_264);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_186, 1);
x_266 = lean_ctor_get(x_186, 2);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_186);
x_267 = 0;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_187);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_260);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_269; 
x_269 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8_t x_270; 
lean_free_object(x_1);
x_270 = !lean_is_exclusive(x_186);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_271 = lean_ctor_get(x_186, 1);
x_272 = lean_ctor_get(x_186, 2);
x_273 = lean_ctor_get(x_186, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_186, 0);
lean_dec(x_274);
x_275 = !lean_is_exclusive(x_260);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_260, 0);
x_277 = lean_ctor_get(x_260, 1);
x_278 = lean_ctor_get(x_260, 2);
x_279 = lean_ctor_get(x_260, 3);
lean_inc(x_187);
lean_ctor_set(x_260, 3, x_276);
lean_ctor_set(x_260, 2, x_272);
lean_ctor_set(x_260, 1, x_271);
lean_ctor_set(x_260, 0, x_187);
x_280 = !lean_is_exclusive(x_187);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_187, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_187, 2);
lean_dec(x_282);
x_283 = lean_ctor_get(x_187, 1);
lean_dec(x_283);
x_284 = lean_ctor_get(x_187, 0);
lean_dec(x_284);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
lean_ctor_set(x_187, 3, x_38);
lean_ctor_set(x_187, 2, x_37);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_279);
lean_ctor_set(x_186, 3, x_187);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
lean_object* x_285; 
lean_dec(x_187);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_36);
lean_ctor_set(x_285, 2, x_37);
lean_ctor_set(x_285, 3, x_38);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_285);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_260, 0);
x_287 = lean_ctor_get(x_260, 1);
x_288 = lean_ctor_get(x_260, 2);
x_289 = lean_ctor_get(x_260, 3);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_260);
lean_inc(x_187);
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_187);
lean_ctor_set(x_290, 1, x_271);
lean_ctor_set(x_290, 2, x_272);
lean_ctor_set(x_290, 3, x_286);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_291 = x_187;
} else {
 lean_dec_ref(x_187);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_36);
lean_ctor_set(x_292, 2, x_37);
lean_ctor_set(x_292, 3, x_38);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_292);
lean_ctor_set(x_186, 2, x_288);
lean_ctor_set(x_186, 1, x_287);
lean_ctor_set(x_186, 0, x_290);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_186, 1);
x_294 = lean_ctor_get(x_186, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_186);
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_260, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_260, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_260, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 x_299 = x_260;
} else {
 lean_dec_ref(x_260);
 x_299 = lean_box(0);
}
lean_inc(x_187);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_187);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_295);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_301 = x_187;
} else {
 lean_dec_ref(x_187);
 x_301 = lean_box(0);
}
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 4, 1);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_36);
lean_ctor_set(x_302, 2, x_37);
lean_ctor_set(x_302, 3, x_38);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_235);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_296);
lean_ctor_set(x_303, 2, x_297);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_186);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_186, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_186, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_187);
if (x_307 == 0)
{
uint8_t x_308; 
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_308);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_187, 0);
x_310 = lean_ctor_get(x_187, 1);
x_311 = lean_ctor_get(x_187, 2);
x_312 = lean_ctor_get(x_187, 3);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_187);
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_311);
lean_ctor_set(x_313, 3, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean_ctor_set(x_186, 0, x_313);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_314);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_186, 1);
x_316 = lean_ctor_get(x_186, 2);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_186);
x_317 = lean_ctor_get(x_187, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_187, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_187, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_187, 3);
lean_inc(x_320);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_321 = x_187;
} else {
 lean_dec_ref(x_187);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_322, 2, x_319);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_260);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
lean_ctor_set(x_1, 0, x_324);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
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
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint32_t x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_1, 0);
x_326 = lean_ctor_get(x_1, 1);
x_327 = lean_ctor_get(x_1, 2);
x_328 = lean_ctor_get(x_1, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_1);
x_329 = lean_unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32_t x_331; uint8_t x_332; 
x_331 = lean_unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_327);
lean_dec(x_326);
x_333 = lean_box_uint32(x_2);
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_325);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_334, 2, x_3);
lean_ctor_set(x_334, 3, x_328);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_328, x_2, x_3);
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_326);
lean_ctor_set(x_337, 2, x_327);
lean_ctor_set(x_337, 3, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_328, x_2, x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 3);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 2);
lean_inc(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
x_344 = 0;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_341);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_340);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_325);
lean_ctor_set(x_347, 1, x_326);
lean_ctor_set(x_347, 2, x_327);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = lean_ctor_get(x_338, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_338, 2);
lean_inc(x_350);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_351 = x_338;
} else {
 lean_dec_ref(x_338);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_340, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_340, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 3);
lean_inc(x_355);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_356 = x_340;
} else {
 lean_dec_ref(x_340);
 x_356 = lean_box(0);
}
x_357 = 1;
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_325);
lean_ctor_set(x_358, 1, x_326);
lean_ctor_set(x_358, 2, x_327);
lean_ctor_set(x_358, 3, x_339);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
if (lean_is_scalar(x_351)) {
 x_359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_359 = x_351;
}
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_354);
lean_ctor_set(x_359, 3, x_355);
lean_ctor_set_uint8(x_359, sizeof(void*)*4, x_357);
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_350);
lean_ctor_set(x_360, 3, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_338, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_338, 2);
lean_inc(x_362);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_363 = x_338;
} else {
 lean_dec_ref(x_338);
 x_363 = lean_box(0);
}
x_364 = 0;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_339);
lean_ctor_set(x_365, 1, x_361);
lean_ctor_set(x_365, 2, x_362);
lean_ctor_set(x_365, 3, x_340);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
x_366 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_366, 0, x_325);
lean_ctor_set(x_366, 1, x_326);
lean_ctor_set(x_366, 2, x_327);
lean_ctor_set(x_366, 3, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8_t x_367; 
x_367 = lean_ctor_get_uint8(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_368 = lean_ctor_get(x_338, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_338, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_338, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_371 = x_338;
} else {
 lean_dec_ref(x_338);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_339, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_339, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_339, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_339, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_376 = x_339;
} else {
 lean_dec_ref(x_339);
 x_376 = lean_box(0);
}
x_377 = 1;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_325);
lean_ctor_set(x_378, 1, x_326);
lean_ctor_set(x_378, 2, x_327);
lean_ctor_set(x_378, 3, x_372);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
if (lean_is_scalar(x_371)) {
 x_379 = lean_alloc_ctor(1, 4, 1);
} else {
 x_379 = x_371;
}
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_368);
lean_ctor_set(x_379, 2, x_369);
lean_ctor_set(x_379, 3, x_370);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_377);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_374);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_338, 3);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; 
x_382 = lean_ctor_get(x_338, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_338, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_384 = x_338;
} else {
 lean_dec_ref(x_338);
 x_384 = lean_box(0);
}
x_385 = 0;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_339);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_381);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
x_387 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_387, 0, x_325);
lean_ctor_set(x_387, 1, x_326);
lean_ctor_set(x_387, 2, x_327);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8_t x_388; 
x_388 = lean_ctor_get_uint8(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_389 = lean_ctor_get(x_338, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_338, 2);
lean_inc(x_390);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_391 = x_338;
} else {
 lean_dec_ref(x_338);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_381, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_381, 3);
lean_inc(x_395);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_396 = x_381;
} else {
 lean_dec_ref(x_381);
 x_396 = lean_box(0);
}
lean_inc(x_339);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_325);
lean_ctor_set(x_397, 1, x_326);
lean_ctor_set(x_397, 2, x_327);
lean_ctor_set(x_397, 3, x_339);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_398 = x_339;
} else {
 lean_dec_ref(x_339);
 x_398 = lean_box(0);
}
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_393);
lean_ctor_set(x_399, 2, x_394);
lean_ctor_set(x_399, 3, x_395);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_391)) {
 x_400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_400 = x_391;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_389);
lean_ctor_set(x_400, 2, x_390);
lean_ctor_set(x_400, 3, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; 
x_401 = lean_ctor_get(x_338, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_338, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_403 = x_338;
} else {
 lean_dec_ref(x_338);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_339, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_339, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_339, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_339, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_408 = x_339;
} else {
 lean_dec_ref(x_339);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_404);
lean_ctor_set(x_409, 1, x_405);
lean_ctor_set(x_409, 2, x_406);
lean_ctor_set(x_409, 3, x_407);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean_is_scalar(x_403)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_403;
}
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_401);
lean_ctor_set(x_411, 2, x_402);
lean_ctor_set(x_411, 3, x_381);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_325);
lean_ctor_set(x_412, 1, x_326);
lean_ctor_set(x_412, 2, x_327);
lean_ctor_set(x_412, 3, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_388);
return x_412;
}
}
}
}
}
}
}
else
{
uint8_t x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_325, x_2, x_3);
x_415 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_326);
lean_ctor_set(x_415, 2, x_327);
lean_ctor_set(x_415, 3, x_328);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_325, x_2, x_3);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 3);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 2);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
x_422 = 0;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set(x_423, 2, x_420);
lean_ctor_set(x_423, 3, x_418);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_326);
lean_ctor_set(x_425, 2, x_327);
lean_ctor_set(x_425, 3, x_328);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8_t x_426; 
x_426 = lean_ctor_get_uint8(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_429 = x_416;
} else {
 lean_dec_ref(x_416);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_418, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_418, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_418, 2);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 3);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
 x_434 = lean_box(0);
}
x_435 = 1;
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_417);
lean_ctor_set(x_436, 1, x_427);
lean_ctor_set(x_436, 2, x_428);
lean_ctor_set(x_436, 3, x_430);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_435);
if (lean_is_scalar(x_429)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_429;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_326);
lean_ctor_set(x_437, 2, x_327);
lean_ctor_set(x_437, 3, x_328);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_435);
x_438 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_431);
lean_ctor_set(x_438, 2, x_432);
lean_ctor_set(x_438, 3, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_416, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_416, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_441 = x_416;
} else {
 lean_dec_ref(x_416);
 x_441 = lean_box(0);
}
x_442 = 0;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_417);
lean_ctor_set(x_443, 1, x_439);
lean_ctor_set(x_443, 2, x_440);
lean_ctor_set(x_443, 3, x_418);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
x_444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_326);
lean_ctor_set(x_444, 2, x_327);
lean_ctor_set(x_444, 3, x_328);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8_t x_445; 
x_445 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_416, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_416, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_416, 3);
lean_inc(x_448);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_449 = x_416;
} else {
 lean_dec_ref(x_416);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_417, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_417, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_417, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_417, 3);
lean_inc(x_453);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_454 = x_417;
} else {
 lean_dec_ref(x_417);
 x_454 = lean_box(0);
}
x_455 = 1;
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_451);
lean_ctor_set(x_456, 2, x_452);
lean_ctor_set(x_456, 3, x_453);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
if (lean_is_scalar(x_449)) {
 x_457 = lean_alloc_ctor(1, 4, 1);
} else {
 x_457 = x_449;
}
lean_ctor_set(x_457, 0, x_448);
lean_ctor_set(x_457, 1, x_326);
lean_ctor_set(x_457, 2, x_327);
lean_ctor_set(x_457, 3, x_328);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_455);
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_446);
lean_ctor_set(x_458, 2, x_447);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_416, 3);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_416, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_416, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_462 = x_416;
} else {
 lean_dec_ref(x_416);
 x_462 = lean_box(0);
}
x_463 = 0;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_460);
lean_ctor_set(x_464, 2, x_461);
lean_ctor_set(x_464, 3, x_459);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_463);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_326);
lean_ctor_set(x_465, 2, x_327);
lean_ctor_set(x_465, 3, x_328);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_467 = lean_ctor_get(x_416, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_416, 2);
lean_inc(x_468);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_469 = x_416;
} else {
 lean_dec_ref(x_416);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_459, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_459, 3);
lean_inc(x_473);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_474 = x_459;
} else {
 lean_dec_ref(x_459);
 x_474 = lean_box(0);
}
lean_inc(x_417);
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 4, 1);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_417);
lean_ctor_set(x_475, 1, x_467);
lean_ctor_set(x_475, 2, x_468);
lean_ctor_set(x_475, 3, x_470);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_476 = x_417;
} else {
 lean_dec_ref(x_417);
 x_476 = lean_box(0);
}
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_326);
lean_ctor_set(x_477, 2, x_327);
lean_ctor_set(x_477, 3, x_328);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_469)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_469;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_416, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_416, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_481 = x_416;
} else {
 lean_dec_ref(x_416);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_417, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_417, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_417, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_417, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_486 = x_417;
} else {
 lean_dec_ref(x_417);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_482);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean_is_scalar(x_481)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_481;
}
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_479);
lean_ctor_set(x_489, 2, x_480);
lean_ctor_set(x_489, 3, x_459);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
x_490 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_326);
lean_ctor_set(x_490, 2, x_327);
lean_ctor_set(x_490, 3, x_328);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_466);
return x_490;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = lean_unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
}
else
{
lean_object* x_19; 
x_19 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = lean_unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = lean_box_uint32(x_2);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_23, x_2, x_3);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_20, x_2, x_3);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = lean_unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_36);
x_43 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_38, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_38, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_35);
lean_ctor_set(x_109, 1, x_36);
lean_ctor_set(x_109, 2, x_37);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_36);
lean_ctor_set(x_119, 2, x_37);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_35);
lean_ctor_set(x_149, 1, x_36);
lean_ctor_set(x_149, 2, x_37);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_159, 2, x_37);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_35, x_2, x_3);
lean_ctor_set(x_1, 0, x_185);
return x_1;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_35, x_2, x_3);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 3);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_186, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_186, 0);
lean_dec(x_191);
x_192 = 0;
lean_ctor_set(x_186, 0, x_188);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_186, 1);
x_195 = lean_ctor_get(x_186, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_186);
x_196 = 0;
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8_t x_199; 
x_199 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_186);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_186, 1);
x_202 = lean_ctor_get(x_186, 2);
x_203 = lean_ctor_get(x_186, 3);
lean_dec(x_203);
x_204 = lean_ctor_get(x_186, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
x_208 = lean_ctor_get(x_188, 2);
x_209 = lean_ctor_get(x_188, 3);
x_210 = 1;
lean_ctor_set(x_188, 3, x_206);
lean_ctor_set(x_188, 2, x_202);
lean_ctor_set(x_188, 1, x_201);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_210);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_209);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_210);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_208);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_188, 0);
x_212 = lean_ctor_get(x_188, 1);
x_213 = lean_ctor_get(x_188, 2);
x_214 = lean_ctor_get(x_188, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_188);
x_215 = 1;
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_187);
lean_ctor_set(x_216, 1, x_201);
lean_ctor_set(x_216, 2, x_202);
lean_ctor_set(x_216, 3, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_215);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_214);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_213);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_186, 1);
x_218 = lean_ctor_get(x_186, 2);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_186);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_188, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_223 = x_188;
} else {
 lean_dec_ref(x_188);
 x_223 = lean_box(0);
}
x_224 = 1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_187);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_218);
lean_ctor_set(x_225, 3, x_219);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
x_226 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_36);
lean_ctor_set(x_226, 2, x_37);
lean_ctor_set(x_226, 3, x_38);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_224);
lean_ctor_set(x_1, 3, x_226);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_186);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_186, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_186, 0);
lean_dec(x_229);
x_230 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_230);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_186, 1);
x_232 = lean_ctor_get(x_186, 2);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_186);
x_233 = 0;
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_187);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
lean_ctor_set(x_234, 3, x_188);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 0, x_234);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8_t x_235; 
x_235 = lean_ctor_get_uint8(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_186);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_186, 1);
x_238 = lean_ctor_get(x_186, 2);
x_239 = lean_ctor_get(x_186, 3);
x_240 = lean_ctor_get(x_186, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_187);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = 1;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_242);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_242);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_187, 0);
x_244 = lean_ctor_get(x_187, 1);
x_245 = lean_ctor_get(x_187, 2);
x_246 = lean_ctor_get(x_187, 3);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_187);
x_247 = 1;
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_245);
lean_ctor_set(x_248, 3, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_249 = lean_ctor_get(x_186, 1);
x_250 = lean_ctor_get(x_186, 2);
x_251 = lean_ctor_get(x_186, 3);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_186);
x_252 = lean_ctor_get(x_187, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_187, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_187, 3);
lean_inc(x_255);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_256 = x_187;
} else {
 lean_dec_ref(x_187);
 x_256 = lean_box(0);
}
x_257 = 1;
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_253);
lean_ctor_set(x_258, 2, x_254);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_36);
lean_ctor_set(x_259, 2, x_37);
lean_ctor_set(x_259, 3, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 3, x_259);
lean_ctor_set(x_1, 2, x_250);
lean_ctor_set(x_1, 1, x_249);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_186, 3);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_186);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_186, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_186, 0);
lean_dec(x_263);
x_264 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_264);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_186, 1);
x_266 = lean_ctor_get(x_186, 2);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_186);
x_267 = 0;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_187);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_260);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_269; 
x_269 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8_t x_270; 
lean_free_object(x_1);
x_270 = !lean_is_exclusive(x_186);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_271 = lean_ctor_get(x_186, 1);
x_272 = lean_ctor_get(x_186, 2);
x_273 = lean_ctor_get(x_186, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_186, 0);
lean_dec(x_274);
x_275 = !lean_is_exclusive(x_260);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_260, 0);
x_277 = lean_ctor_get(x_260, 1);
x_278 = lean_ctor_get(x_260, 2);
x_279 = lean_ctor_get(x_260, 3);
lean_inc(x_187);
lean_ctor_set(x_260, 3, x_276);
lean_ctor_set(x_260, 2, x_272);
lean_ctor_set(x_260, 1, x_271);
lean_ctor_set(x_260, 0, x_187);
x_280 = !lean_is_exclusive(x_187);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_187, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_187, 2);
lean_dec(x_282);
x_283 = lean_ctor_get(x_187, 1);
lean_dec(x_283);
x_284 = lean_ctor_get(x_187, 0);
lean_dec(x_284);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
lean_ctor_set(x_187, 3, x_38);
lean_ctor_set(x_187, 2, x_37);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_279);
lean_ctor_set(x_186, 3, x_187);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
lean_object* x_285; 
lean_dec(x_187);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_36);
lean_ctor_set(x_285, 2, x_37);
lean_ctor_set(x_285, 3, x_38);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_285);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_260, 0);
x_287 = lean_ctor_get(x_260, 1);
x_288 = lean_ctor_get(x_260, 2);
x_289 = lean_ctor_get(x_260, 3);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_260);
lean_inc(x_187);
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_187);
lean_ctor_set(x_290, 1, x_271);
lean_ctor_set(x_290, 2, x_272);
lean_ctor_set(x_290, 3, x_286);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_291 = x_187;
} else {
 lean_dec_ref(x_187);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_36);
lean_ctor_set(x_292, 2, x_37);
lean_ctor_set(x_292, 3, x_38);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_292);
lean_ctor_set(x_186, 2, x_288);
lean_ctor_set(x_186, 1, x_287);
lean_ctor_set(x_186, 0, x_290);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_186, 1);
x_294 = lean_ctor_get(x_186, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_186);
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_260, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_260, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_260, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 x_299 = x_260;
} else {
 lean_dec_ref(x_260);
 x_299 = lean_box(0);
}
lean_inc(x_187);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_187);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_295);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_301 = x_187;
} else {
 lean_dec_ref(x_187);
 x_301 = lean_box(0);
}
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 4, 1);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_36);
lean_ctor_set(x_302, 2, x_37);
lean_ctor_set(x_302, 3, x_38);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_235);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_296);
lean_ctor_set(x_303, 2, x_297);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_186);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_186, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_186, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_187);
if (x_307 == 0)
{
uint8_t x_308; 
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_308);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_187, 0);
x_310 = lean_ctor_get(x_187, 1);
x_311 = lean_ctor_get(x_187, 2);
x_312 = lean_ctor_get(x_187, 3);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_187);
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_311);
lean_ctor_set(x_313, 3, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean_ctor_set(x_186, 0, x_313);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_314);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_186, 1);
x_316 = lean_ctor_get(x_186, 2);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_186);
x_317 = lean_ctor_get(x_187, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_187, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_187, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_187, 3);
lean_inc(x_320);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_321 = x_187;
} else {
 lean_dec_ref(x_187);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_322, 2, x_319);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_260);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
lean_ctor_set(x_1, 0, x_324);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
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
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint32_t x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_1, 0);
x_326 = lean_ctor_get(x_1, 1);
x_327 = lean_ctor_get(x_1, 2);
x_328 = lean_ctor_get(x_1, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_1);
x_329 = lean_unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32_t x_331; uint8_t x_332; 
x_331 = lean_unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_327);
lean_dec(x_326);
x_333 = lean_box_uint32(x_2);
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_325);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_334, 2, x_3);
lean_ctor_set(x_334, 3, x_328);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_328, x_2, x_3);
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_326);
lean_ctor_set(x_337, 2, x_327);
lean_ctor_set(x_337, 3, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_328, x_2, x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 3);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 2);
lean_inc(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
x_344 = 0;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_341);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_340);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_325);
lean_ctor_set(x_347, 1, x_326);
lean_ctor_set(x_347, 2, x_327);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = lean_ctor_get(x_338, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_338, 2);
lean_inc(x_350);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_351 = x_338;
} else {
 lean_dec_ref(x_338);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_340, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_340, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 3);
lean_inc(x_355);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_356 = x_340;
} else {
 lean_dec_ref(x_340);
 x_356 = lean_box(0);
}
x_357 = 1;
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_325);
lean_ctor_set(x_358, 1, x_326);
lean_ctor_set(x_358, 2, x_327);
lean_ctor_set(x_358, 3, x_339);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
if (lean_is_scalar(x_351)) {
 x_359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_359 = x_351;
}
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_354);
lean_ctor_set(x_359, 3, x_355);
lean_ctor_set_uint8(x_359, sizeof(void*)*4, x_357);
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_350);
lean_ctor_set(x_360, 3, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_338, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_338, 2);
lean_inc(x_362);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_363 = x_338;
} else {
 lean_dec_ref(x_338);
 x_363 = lean_box(0);
}
x_364 = 0;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_339);
lean_ctor_set(x_365, 1, x_361);
lean_ctor_set(x_365, 2, x_362);
lean_ctor_set(x_365, 3, x_340);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
x_366 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_366, 0, x_325);
lean_ctor_set(x_366, 1, x_326);
lean_ctor_set(x_366, 2, x_327);
lean_ctor_set(x_366, 3, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8_t x_367; 
x_367 = lean_ctor_get_uint8(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_368 = lean_ctor_get(x_338, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_338, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_338, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_371 = x_338;
} else {
 lean_dec_ref(x_338);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_339, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_339, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_339, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_339, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_376 = x_339;
} else {
 lean_dec_ref(x_339);
 x_376 = lean_box(0);
}
x_377 = 1;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_325);
lean_ctor_set(x_378, 1, x_326);
lean_ctor_set(x_378, 2, x_327);
lean_ctor_set(x_378, 3, x_372);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
if (lean_is_scalar(x_371)) {
 x_379 = lean_alloc_ctor(1, 4, 1);
} else {
 x_379 = x_371;
}
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_368);
lean_ctor_set(x_379, 2, x_369);
lean_ctor_set(x_379, 3, x_370);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_377);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_374);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_338, 3);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; 
x_382 = lean_ctor_get(x_338, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_338, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_384 = x_338;
} else {
 lean_dec_ref(x_338);
 x_384 = lean_box(0);
}
x_385 = 0;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_339);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_381);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
x_387 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_387, 0, x_325);
lean_ctor_set(x_387, 1, x_326);
lean_ctor_set(x_387, 2, x_327);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8_t x_388; 
x_388 = lean_ctor_get_uint8(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_389 = lean_ctor_get(x_338, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_338, 2);
lean_inc(x_390);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_391 = x_338;
} else {
 lean_dec_ref(x_338);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_381, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_381, 3);
lean_inc(x_395);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_396 = x_381;
} else {
 lean_dec_ref(x_381);
 x_396 = lean_box(0);
}
lean_inc(x_339);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_325);
lean_ctor_set(x_397, 1, x_326);
lean_ctor_set(x_397, 2, x_327);
lean_ctor_set(x_397, 3, x_339);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_398 = x_339;
} else {
 lean_dec_ref(x_339);
 x_398 = lean_box(0);
}
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_393);
lean_ctor_set(x_399, 2, x_394);
lean_ctor_set(x_399, 3, x_395);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_391)) {
 x_400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_400 = x_391;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_389);
lean_ctor_set(x_400, 2, x_390);
lean_ctor_set(x_400, 3, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; 
x_401 = lean_ctor_get(x_338, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_338, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_403 = x_338;
} else {
 lean_dec_ref(x_338);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_339, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_339, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_339, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_339, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_408 = x_339;
} else {
 lean_dec_ref(x_339);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_404);
lean_ctor_set(x_409, 1, x_405);
lean_ctor_set(x_409, 2, x_406);
lean_ctor_set(x_409, 3, x_407);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean_is_scalar(x_403)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_403;
}
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_401);
lean_ctor_set(x_411, 2, x_402);
lean_ctor_set(x_411, 3, x_381);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_325);
lean_ctor_set(x_412, 1, x_326);
lean_ctor_set(x_412, 2, x_327);
lean_ctor_set(x_412, 3, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_388);
return x_412;
}
}
}
}
}
}
}
else
{
uint8_t x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_325, x_2, x_3);
x_415 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_326);
lean_ctor_set(x_415, 2, x_327);
lean_ctor_set(x_415, 3, x_328);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_325, x_2, x_3);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 3);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 2);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
x_422 = 0;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set(x_423, 2, x_420);
lean_ctor_set(x_423, 3, x_418);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_326);
lean_ctor_set(x_425, 2, x_327);
lean_ctor_set(x_425, 3, x_328);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8_t x_426; 
x_426 = lean_ctor_get_uint8(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_429 = x_416;
} else {
 lean_dec_ref(x_416);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_418, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_418, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_418, 2);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 3);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
 x_434 = lean_box(0);
}
x_435 = 1;
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_417);
lean_ctor_set(x_436, 1, x_427);
lean_ctor_set(x_436, 2, x_428);
lean_ctor_set(x_436, 3, x_430);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_435);
if (lean_is_scalar(x_429)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_429;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_326);
lean_ctor_set(x_437, 2, x_327);
lean_ctor_set(x_437, 3, x_328);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_435);
x_438 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_431);
lean_ctor_set(x_438, 2, x_432);
lean_ctor_set(x_438, 3, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_416, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_416, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_441 = x_416;
} else {
 lean_dec_ref(x_416);
 x_441 = lean_box(0);
}
x_442 = 0;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_417);
lean_ctor_set(x_443, 1, x_439);
lean_ctor_set(x_443, 2, x_440);
lean_ctor_set(x_443, 3, x_418);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
x_444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_326);
lean_ctor_set(x_444, 2, x_327);
lean_ctor_set(x_444, 3, x_328);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8_t x_445; 
x_445 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_416, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_416, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_416, 3);
lean_inc(x_448);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_449 = x_416;
} else {
 lean_dec_ref(x_416);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_417, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_417, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_417, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_417, 3);
lean_inc(x_453);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_454 = x_417;
} else {
 lean_dec_ref(x_417);
 x_454 = lean_box(0);
}
x_455 = 1;
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_451);
lean_ctor_set(x_456, 2, x_452);
lean_ctor_set(x_456, 3, x_453);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
if (lean_is_scalar(x_449)) {
 x_457 = lean_alloc_ctor(1, 4, 1);
} else {
 x_457 = x_449;
}
lean_ctor_set(x_457, 0, x_448);
lean_ctor_set(x_457, 1, x_326);
lean_ctor_set(x_457, 2, x_327);
lean_ctor_set(x_457, 3, x_328);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_455);
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_446);
lean_ctor_set(x_458, 2, x_447);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_416, 3);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_416, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_416, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_462 = x_416;
} else {
 lean_dec_ref(x_416);
 x_462 = lean_box(0);
}
x_463 = 0;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_460);
lean_ctor_set(x_464, 2, x_461);
lean_ctor_set(x_464, 3, x_459);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_463);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_326);
lean_ctor_set(x_465, 2, x_327);
lean_ctor_set(x_465, 3, x_328);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_467 = lean_ctor_get(x_416, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_416, 2);
lean_inc(x_468);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_469 = x_416;
} else {
 lean_dec_ref(x_416);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_459, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_459, 3);
lean_inc(x_473);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_474 = x_459;
} else {
 lean_dec_ref(x_459);
 x_474 = lean_box(0);
}
lean_inc(x_417);
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 4, 1);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_417);
lean_ctor_set(x_475, 1, x_467);
lean_ctor_set(x_475, 2, x_468);
lean_ctor_set(x_475, 3, x_470);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_476 = x_417;
} else {
 lean_dec_ref(x_417);
 x_476 = lean_box(0);
}
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_326);
lean_ctor_set(x_477, 2, x_327);
lean_ctor_set(x_477, 3, x_328);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_469)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_469;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_416, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_416, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_481 = x_416;
} else {
 lean_dec_ref(x_416);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_417, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_417, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_417, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_417, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_486 = x_417;
} else {
 lean_dec_ref(x_417);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_482);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean_is_scalar(x_481)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_481;
}
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_479);
lean_ctor_set(x_489, 2, x_480);
lean_ctor_set(x_489, 3, x_459);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
x_490 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_326);
lean_ctor_set(x_490, 2, x_327);
lean_ctor_set(x_490, 3, x_328);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_466);
return x_490;
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
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__4___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = lean_unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
}
else
{
lean_object* x_19; 
x_19 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = lean_unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = lean_box_uint32(x_2);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_23, x_2, x_3);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_20, x_2, x_3);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = lean_unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_36);
x_43 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_38, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_38, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_35);
lean_ctor_set(x_109, 1, x_36);
lean_ctor_set(x_109, 2, x_37);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_36);
lean_ctor_set(x_119, 2, x_37);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_35);
lean_ctor_set(x_149, 1, x_36);
lean_ctor_set(x_149, 2, x_37);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_159, 2, x_37);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_35, x_2, x_3);
lean_ctor_set(x_1, 0, x_185);
return x_1;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_35, x_2, x_3);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 3);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_186, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_186, 0);
lean_dec(x_191);
x_192 = 0;
lean_ctor_set(x_186, 0, x_188);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_186, 1);
x_195 = lean_ctor_get(x_186, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_186);
x_196 = 0;
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8_t x_199; 
x_199 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_186);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_186, 1);
x_202 = lean_ctor_get(x_186, 2);
x_203 = lean_ctor_get(x_186, 3);
lean_dec(x_203);
x_204 = lean_ctor_get(x_186, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
x_208 = lean_ctor_get(x_188, 2);
x_209 = lean_ctor_get(x_188, 3);
x_210 = 1;
lean_ctor_set(x_188, 3, x_206);
lean_ctor_set(x_188, 2, x_202);
lean_ctor_set(x_188, 1, x_201);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_210);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_209);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_210);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_208);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_188, 0);
x_212 = lean_ctor_get(x_188, 1);
x_213 = lean_ctor_get(x_188, 2);
x_214 = lean_ctor_get(x_188, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_188);
x_215 = 1;
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_187);
lean_ctor_set(x_216, 1, x_201);
lean_ctor_set(x_216, 2, x_202);
lean_ctor_set(x_216, 3, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_215);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_214);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_213);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_186, 1);
x_218 = lean_ctor_get(x_186, 2);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_186);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_188, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_223 = x_188;
} else {
 lean_dec_ref(x_188);
 x_223 = lean_box(0);
}
x_224 = 1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_187);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_218);
lean_ctor_set(x_225, 3, x_219);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
x_226 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_36);
lean_ctor_set(x_226, 2, x_37);
lean_ctor_set(x_226, 3, x_38);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_224);
lean_ctor_set(x_1, 3, x_226);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_186);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_186, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_186, 0);
lean_dec(x_229);
x_230 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_230);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_186, 1);
x_232 = lean_ctor_get(x_186, 2);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_186);
x_233 = 0;
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_187);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
lean_ctor_set(x_234, 3, x_188);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 0, x_234);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8_t x_235; 
x_235 = lean_ctor_get_uint8(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_186);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_186, 1);
x_238 = lean_ctor_get(x_186, 2);
x_239 = lean_ctor_get(x_186, 3);
x_240 = lean_ctor_get(x_186, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_187);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = 1;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_242);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_242);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_187, 0);
x_244 = lean_ctor_get(x_187, 1);
x_245 = lean_ctor_get(x_187, 2);
x_246 = lean_ctor_get(x_187, 3);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_187);
x_247 = 1;
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_245);
lean_ctor_set(x_248, 3, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_249 = lean_ctor_get(x_186, 1);
x_250 = lean_ctor_get(x_186, 2);
x_251 = lean_ctor_get(x_186, 3);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_186);
x_252 = lean_ctor_get(x_187, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_187, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_187, 3);
lean_inc(x_255);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_256 = x_187;
} else {
 lean_dec_ref(x_187);
 x_256 = lean_box(0);
}
x_257 = 1;
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_253);
lean_ctor_set(x_258, 2, x_254);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_36);
lean_ctor_set(x_259, 2, x_37);
lean_ctor_set(x_259, 3, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 3, x_259);
lean_ctor_set(x_1, 2, x_250);
lean_ctor_set(x_1, 1, x_249);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_186, 3);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_186);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_186, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_186, 0);
lean_dec(x_263);
x_264 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_264);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_186, 1);
x_266 = lean_ctor_get(x_186, 2);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_186);
x_267 = 0;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_187);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_260);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_269; 
x_269 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8_t x_270; 
lean_free_object(x_1);
x_270 = !lean_is_exclusive(x_186);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_271 = lean_ctor_get(x_186, 1);
x_272 = lean_ctor_get(x_186, 2);
x_273 = lean_ctor_get(x_186, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_186, 0);
lean_dec(x_274);
x_275 = !lean_is_exclusive(x_260);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_260, 0);
x_277 = lean_ctor_get(x_260, 1);
x_278 = lean_ctor_get(x_260, 2);
x_279 = lean_ctor_get(x_260, 3);
lean_inc(x_187);
lean_ctor_set(x_260, 3, x_276);
lean_ctor_set(x_260, 2, x_272);
lean_ctor_set(x_260, 1, x_271);
lean_ctor_set(x_260, 0, x_187);
x_280 = !lean_is_exclusive(x_187);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_187, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_187, 2);
lean_dec(x_282);
x_283 = lean_ctor_get(x_187, 1);
lean_dec(x_283);
x_284 = lean_ctor_get(x_187, 0);
lean_dec(x_284);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
lean_ctor_set(x_187, 3, x_38);
lean_ctor_set(x_187, 2, x_37);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_279);
lean_ctor_set(x_186, 3, x_187);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
lean_object* x_285; 
lean_dec(x_187);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_36);
lean_ctor_set(x_285, 2, x_37);
lean_ctor_set(x_285, 3, x_38);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_285);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_260, 0);
x_287 = lean_ctor_get(x_260, 1);
x_288 = lean_ctor_get(x_260, 2);
x_289 = lean_ctor_get(x_260, 3);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_260);
lean_inc(x_187);
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_187);
lean_ctor_set(x_290, 1, x_271);
lean_ctor_set(x_290, 2, x_272);
lean_ctor_set(x_290, 3, x_286);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_291 = x_187;
} else {
 lean_dec_ref(x_187);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_36);
lean_ctor_set(x_292, 2, x_37);
lean_ctor_set(x_292, 3, x_38);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_292);
lean_ctor_set(x_186, 2, x_288);
lean_ctor_set(x_186, 1, x_287);
lean_ctor_set(x_186, 0, x_290);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_186, 1);
x_294 = lean_ctor_get(x_186, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_186);
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_260, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_260, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_260, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 x_299 = x_260;
} else {
 lean_dec_ref(x_260);
 x_299 = lean_box(0);
}
lean_inc(x_187);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_187);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_295);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_301 = x_187;
} else {
 lean_dec_ref(x_187);
 x_301 = lean_box(0);
}
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 4, 1);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_36);
lean_ctor_set(x_302, 2, x_37);
lean_ctor_set(x_302, 3, x_38);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_235);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_296);
lean_ctor_set(x_303, 2, x_297);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_186);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_186, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_186, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_187);
if (x_307 == 0)
{
uint8_t x_308; 
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_308);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_187, 0);
x_310 = lean_ctor_get(x_187, 1);
x_311 = lean_ctor_get(x_187, 2);
x_312 = lean_ctor_get(x_187, 3);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_187);
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_311);
lean_ctor_set(x_313, 3, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean_ctor_set(x_186, 0, x_313);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_314);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_186, 1);
x_316 = lean_ctor_get(x_186, 2);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_186);
x_317 = lean_ctor_get(x_187, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_187, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_187, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_187, 3);
lean_inc(x_320);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_321 = x_187;
} else {
 lean_dec_ref(x_187);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_322, 2, x_319);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_260);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
lean_ctor_set(x_1, 0, x_324);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
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
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint32_t x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_1, 0);
x_326 = lean_ctor_get(x_1, 1);
x_327 = lean_ctor_get(x_1, 2);
x_328 = lean_ctor_get(x_1, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_1);
x_329 = lean_unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32_t x_331; uint8_t x_332; 
x_331 = lean_unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_327);
lean_dec(x_326);
x_333 = lean_box_uint32(x_2);
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_325);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_334, 2, x_3);
lean_ctor_set(x_334, 3, x_328);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_328, x_2, x_3);
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_326);
lean_ctor_set(x_337, 2, x_327);
lean_ctor_set(x_337, 3, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_328, x_2, x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 3);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 2);
lean_inc(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
x_344 = 0;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_341);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_340);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_325);
lean_ctor_set(x_347, 1, x_326);
lean_ctor_set(x_347, 2, x_327);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = lean_ctor_get(x_338, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_338, 2);
lean_inc(x_350);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_351 = x_338;
} else {
 lean_dec_ref(x_338);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_340, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_340, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 3);
lean_inc(x_355);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_356 = x_340;
} else {
 lean_dec_ref(x_340);
 x_356 = lean_box(0);
}
x_357 = 1;
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_325);
lean_ctor_set(x_358, 1, x_326);
lean_ctor_set(x_358, 2, x_327);
lean_ctor_set(x_358, 3, x_339);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
if (lean_is_scalar(x_351)) {
 x_359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_359 = x_351;
}
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_354);
lean_ctor_set(x_359, 3, x_355);
lean_ctor_set_uint8(x_359, sizeof(void*)*4, x_357);
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_350);
lean_ctor_set(x_360, 3, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_338, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_338, 2);
lean_inc(x_362);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_363 = x_338;
} else {
 lean_dec_ref(x_338);
 x_363 = lean_box(0);
}
x_364 = 0;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_339);
lean_ctor_set(x_365, 1, x_361);
lean_ctor_set(x_365, 2, x_362);
lean_ctor_set(x_365, 3, x_340);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
x_366 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_366, 0, x_325);
lean_ctor_set(x_366, 1, x_326);
lean_ctor_set(x_366, 2, x_327);
lean_ctor_set(x_366, 3, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8_t x_367; 
x_367 = lean_ctor_get_uint8(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_368 = lean_ctor_get(x_338, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_338, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_338, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_371 = x_338;
} else {
 lean_dec_ref(x_338);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_339, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_339, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_339, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_339, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_376 = x_339;
} else {
 lean_dec_ref(x_339);
 x_376 = lean_box(0);
}
x_377 = 1;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_325);
lean_ctor_set(x_378, 1, x_326);
lean_ctor_set(x_378, 2, x_327);
lean_ctor_set(x_378, 3, x_372);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
if (lean_is_scalar(x_371)) {
 x_379 = lean_alloc_ctor(1, 4, 1);
} else {
 x_379 = x_371;
}
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_368);
lean_ctor_set(x_379, 2, x_369);
lean_ctor_set(x_379, 3, x_370);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_377);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_374);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_338, 3);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; 
x_382 = lean_ctor_get(x_338, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_338, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_384 = x_338;
} else {
 lean_dec_ref(x_338);
 x_384 = lean_box(0);
}
x_385 = 0;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_339);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_381);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
x_387 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_387, 0, x_325);
lean_ctor_set(x_387, 1, x_326);
lean_ctor_set(x_387, 2, x_327);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8_t x_388; 
x_388 = lean_ctor_get_uint8(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_389 = lean_ctor_get(x_338, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_338, 2);
lean_inc(x_390);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_391 = x_338;
} else {
 lean_dec_ref(x_338);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_381, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_381, 3);
lean_inc(x_395);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_396 = x_381;
} else {
 lean_dec_ref(x_381);
 x_396 = lean_box(0);
}
lean_inc(x_339);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_325);
lean_ctor_set(x_397, 1, x_326);
lean_ctor_set(x_397, 2, x_327);
lean_ctor_set(x_397, 3, x_339);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_398 = x_339;
} else {
 lean_dec_ref(x_339);
 x_398 = lean_box(0);
}
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_393);
lean_ctor_set(x_399, 2, x_394);
lean_ctor_set(x_399, 3, x_395);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_391)) {
 x_400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_400 = x_391;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_389);
lean_ctor_set(x_400, 2, x_390);
lean_ctor_set(x_400, 3, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; 
x_401 = lean_ctor_get(x_338, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_338, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_403 = x_338;
} else {
 lean_dec_ref(x_338);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_339, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_339, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_339, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_339, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_408 = x_339;
} else {
 lean_dec_ref(x_339);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_404);
lean_ctor_set(x_409, 1, x_405);
lean_ctor_set(x_409, 2, x_406);
lean_ctor_set(x_409, 3, x_407);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean_is_scalar(x_403)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_403;
}
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_401);
lean_ctor_set(x_411, 2, x_402);
lean_ctor_set(x_411, 3, x_381);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_325);
lean_ctor_set(x_412, 1, x_326);
lean_ctor_set(x_412, 2, x_327);
lean_ctor_set(x_412, 3, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_388);
return x_412;
}
}
}
}
}
}
}
else
{
uint8_t x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_325, x_2, x_3);
x_415 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_326);
lean_ctor_set(x_415, 2, x_327);
lean_ctor_set(x_415, 3, x_328);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_325, x_2, x_3);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 3);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 2);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
x_422 = 0;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set(x_423, 2, x_420);
lean_ctor_set(x_423, 3, x_418);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_326);
lean_ctor_set(x_425, 2, x_327);
lean_ctor_set(x_425, 3, x_328);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8_t x_426; 
x_426 = lean_ctor_get_uint8(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_429 = x_416;
} else {
 lean_dec_ref(x_416);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_418, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_418, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_418, 2);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 3);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
 x_434 = lean_box(0);
}
x_435 = 1;
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_417);
lean_ctor_set(x_436, 1, x_427);
lean_ctor_set(x_436, 2, x_428);
lean_ctor_set(x_436, 3, x_430);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_435);
if (lean_is_scalar(x_429)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_429;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_326);
lean_ctor_set(x_437, 2, x_327);
lean_ctor_set(x_437, 3, x_328);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_435);
x_438 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_431);
lean_ctor_set(x_438, 2, x_432);
lean_ctor_set(x_438, 3, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_416, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_416, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_441 = x_416;
} else {
 lean_dec_ref(x_416);
 x_441 = lean_box(0);
}
x_442 = 0;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_417);
lean_ctor_set(x_443, 1, x_439);
lean_ctor_set(x_443, 2, x_440);
lean_ctor_set(x_443, 3, x_418);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
x_444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_326);
lean_ctor_set(x_444, 2, x_327);
lean_ctor_set(x_444, 3, x_328);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8_t x_445; 
x_445 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_416, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_416, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_416, 3);
lean_inc(x_448);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_449 = x_416;
} else {
 lean_dec_ref(x_416);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_417, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_417, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_417, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_417, 3);
lean_inc(x_453);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_454 = x_417;
} else {
 lean_dec_ref(x_417);
 x_454 = lean_box(0);
}
x_455 = 1;
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_451);
lean_ctor_set(x_456, 2, x_452);
lean_ctor_set(x_456, 3, x_453);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
if (lean_is_scalar(x_449)) {
 x_457 = lean_alloc_ctor(1, 4, 1);
} else {
 x_457 = x_449;
}
lean_ctor_set(x_457, 0, x_448);
lean_ctor_set(x_457, 1, x_326);
lean_ctor_set(x_457, 2, x_327);
lean_ctor_set(x_457, 3, x_328);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_455);
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_446);
lean_ctor_set(x_458, 2, x_447);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_416, 3);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_416, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_416, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_462 = x_416;
} else {
 lean_dec_ref(x_416);
 x_462 = lean_box(0);
}
x_463 = 0;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_460);
lean_ctor_set(x_464, 2, x_461);
lean_ctor_set(x_464, 3, x_459);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_463);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_326);
lean_ctor_set(x_465, 2, x_327);
lean_ctor_set(x_465, 3, x_328);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_467 = lean_ctor_get(x_416, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_416, 2);
lean_inc(x_468);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_469 = x_416;
} else {
 lean_dec_ref(x_416);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_459, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_459, 3);
lean_inc(x_473);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_474 = x_459;
} else {
 lean_dec_ref(x_459);
 x_474 = lean_box(0);
}
lean_inc(x_417);
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 4, 1);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_417);
lean_ctor_set(x_475, 1, x_467);
lean_ctor_set(x_475, 2, x_468);
lean_ctor_set(x_475, 3, x_470);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_476 = x_417;
} else {
 lean_dec_ref(x_417);
 x_476 = lean_box(0);
}
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_326);
lean_ctor_set(x_477, 2, x_327);
lean_ctor_set(x_477, 3, x_328);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_469)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_469;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_416, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_416, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_481 = x_416;
} else {
 lean_dec_ref(x_416);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_417, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_417, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_417, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_417, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_486 = x_417;
} else {
 lean_dec_ref(x_417);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_482);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean_is_scalar(x_481)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_481;
}
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_479);
lean_ctor_set(x_489, 2, x_480);
lean_ctor_set(x_489, 3, x_459);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
x_490 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_326);
lean_ctor_set(x_490, 2, x_327);
lean_ctor_set(x_490, 3, x_328);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_466);
return x_490;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_unbox_uint32(x_10);
x_14 = x_2 < x_13;
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = lean_unbox_uint32(x_10);
x_16 = x_15 < x_2;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
}
else
{
lean_object* x_19; 
x_19 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_unbox_uint32(x_21);
x_25 = x_2 < x_24;
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = lean_unbox_uint32(x_21);
x_27 = x_26 < x_2;
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = lean_box_uint32(x_2);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_23, x_2, x_3);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_20, x_2, x_3);
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_7);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_unbox_uint32(x_36);
x_40 = x_2 < x_39;
if (x_40 == 0)
{
uint32_t x_41; uint8_t x_42; 
x_41 = lean_unbox_uint32(x_36);
x_42 = x_41 < x_2;
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_37);
lean_dec(x_36);
x_43 = lean_box_uint32(x_2);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_43);
return x_1;
}
else
{
uint8_t x_44; 
x_44 = l_RBNode_isRed___rarg(x_38);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_38, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_38, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 1, x_36);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_35);
lean_ctor_set(x_109, 1, x_36);
lean_ctor_set(x_109, 2, x_37);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_35);
lean_ctor_set(x_119, 1, x_36);
lean_ctor_set(x_119, 2, x_37);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_35);
lean_ctor_set(x_149, 1, x_36);
lean_ctor_set(x_149, 2, x_37);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_35);
lean_ctor_set(x_159, 1, x_36);
lean_ctor_set(x_159, 2, x_37);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; 
x_184 = l_RBNode_isRed___rarg(x_35);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_35, x_2, x_3);
lean_ctor_set(x_1, 0, x_185);
return x_1;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_35, x_2, x_3);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 3);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_186, 3);
lean_dec(x_190);
x_191 = lean_ctor_get(x_186, 0);
lean_dec(x_191);
x_192 = 0;
lean_ctor_set(x_186, 0, x_188);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_192);
x_193 = 1;
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_193);
return x_1;
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; uint8_t x_198; 
x_194 = lean_ctor_get(x_186, 1);
x_195 = lean_ctor_get(x_186, 2);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_186);
x_196 = 0;
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_196);
x_198 = 1;
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
}
else
{
uint8_t x_199; 
x_199 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_186);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_186, 1);
x_202 = lean_ctor_get(x_186, 2);
x_203 = lean_ctor_get(x_186, 3);
lean_dec(x_203);
x_204 = lean_ctor_get(x_186, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
x_208 = lean_ctor_get(x_188, 2);
x_209 = lean_ctor_get(x_188, 3);
x_210 = 1;
lean_ctor_set(x_188, 3, x_206);
lean_ctor_set(x_188, 2, x_202);
lean_ctor_set(x_188, 1, x_201);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_210);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_209);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_210);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_208);
lean_ctor_set(x_1, 1, x_207);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_188, 0);
x_212 = lean_ctor_get(x_188, 1);
x_213 = lean_ctor_get(x_188, 2);
x_214 = lean_ctor_get(x_188, 3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_188);
x_215 = 1;
x_216 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_216, 0, x_187);
lean_ctor_set(x_216, 1, x_201);
lean_ctor_set(x_216, 2, x_202);
lean_ctor_set(x_216, 3, x_211);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_215);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_214);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_215);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_213);
lean_ctor_set(x_1, 1, x_212);
lean_ctor_set(x_1, 0, x_216);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_186, 1);
x_218 = lean_ctor_get(x_186, 2);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_186);
x_219 = lean_ctor_get(x_188, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_188, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_223 = x_188;
} else {
 lean_dec_ref(x_188);
 x_223 = lean_box(0);
}
x_224 = 1;
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_187);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_218);
lean_ctor_set(x_225, 3, x_219);
lean_ctor_set_uint8(x_225, sizeof(void*)*4, x_224);
x_226 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_226, 0, x_222);
lean_ctor_set(x_226, 1, x_36);
lean_ctor_set(x_226, 2, x_37);
lean_ctor_set(x_226, 3, x_38);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_224);
lean_ctor_set(x_1, 3, x_226);
lean_ctor_set(x_1, 2, x_221);
lean_ctor_set(x_1, 1, x_220);
lean_ctor_set(x_1, 0, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_186);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_186, 3);
lean_dec(x_228);
x_229 = lean_ctor_get(x_186, 0);
lean_dec(x_229);
x_230 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_230);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_186, 1);
x_232 = lean_ctor_get(x_186, 2);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_186);
x_233 = 0;
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_187);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
lean_ctor_set(x_234, 3, x_188);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 0, x_234);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
}
}
else
{
uint8_t x_235; 
x_235 = lean_ctor_get_uint8(x_187, sizeof(void*)*4);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_186);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_186, 1);
x_238 = lean_ctor_get(x_186, 2);
x_239 = lean_ctor_get(x_186, 3);
x_240 = lean_ctor_get(x_186, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_187);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = 1;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_242);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_242);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_187, 0);
x_244 = lean_ctor_get(x_187, 1);
x_245 = lean_ctor_get(x_187, 2);
x_246 = lean_ctor_get(x_187, 3);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_187);
x_247 = 1;
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_244);
lean_ctor_set(x_248, 2, x_245);
lean_ctor_set(x_248, 3, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_247);
lean_ctor_set(x_186, 3, x_38);
lean_ctor_set(x_186, 2, x_37);
lean_ctor_set(x_186, 1, x_36);
lean_ctor_set(x_186, 0, x_239);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_247);
lean_ctor_set(x_1, 3, x_186);
lean_ctor_set(x_1, 2, x_238);
lean_ctor_set(x_1, 1, x_237);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_249 = lean_ctor_get(x_186, 1);
x_250 = lean_ctor_get(x_186, 2);
x_251 = lean_ctor_get(x_186, 3);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_186);
x_252 = lean_ctor_get(x_187, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_187, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_187, 3);
lean_inc(x_255);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_256 = x_187;
} else {
 lean_dec_ref(x_187);
 x_256 = lean_box(0);
}
x_257 = 1;
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 4, 1);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_253);
lean_ctor_set(x_258, 2, x_254);
lean_ctor_set(x_258, 3, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_36);
lean_ctor_set(x_259, 2, x_37);
lean_ctor_set(x_259, 3, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_257);
lean_ctor_set(x_1, 3, x_259);
lean_ctor_set(x_1, 2, x_250);
lean_ctor_set(x_1, 1, x_249);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_186, 3);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_186);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_186, 3);
lean_dec(x_262);
x_263 = lean_ctor_get(x_186, 0);
lean_dec(x_263);
x_264 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_264);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
else
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_186, 1);
x_266 = lean_ctor_get(x_186, 2);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_186);
x_267 = 0;
x_268 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_268, 0, x_187);
lean_ctor_set(x_268, 1, x_265);
lean_ctor_set(x_268, 2, x_266);
lean_ctor_set(x_268, 3, x_260);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_269; 
x_269 = lean_ctor_get_uint8(x_260, sizeof(void*)*4);
if (x_269 == 0)
{
uint8_t x_270; 
lean_free_object(x_1);
x_270 = !lean_is_exclusive(x_186);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_271 = lean_ctor_get(x_186, 1);
x_272 = lean_ctor_get(x_186, 2);
x_273 = lean_ctor_get(x_186, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_186, 0);
lean_dec(x_274);
x_275 = !lean_is_exclusive(x_260);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_276 = lean_ctor_get(x_260, 0);
x_277 = lean_ctor_get(x_260, 1);
x_278 = lean_ctor_get(x_260, 2);
x_279 = lean_ctor_get(x_260, 3);
lean_inc(x_187);
lean_ctor_set(x_260, 3, x_276);
lean_ctor_set(x_260, 2, x_272);
lean_ctor_set(x_260, 1, x_271);
lean_ctor_set(x_260, 0, x_187);
x_280 = !lean_is_exclusive(x_187);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_187, 3);
lean_dec(x_281);
x_282 = lean_ctor_get(x_187, 2);
lean_dec(x_282);
x_283 = lean_ctor_get(x_187, 1);
lean_dec(x_283);
x_284 = lean_ctor_get(x_187, 0);
lean_dec(x_284);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
lean_ctor_set(x_187, 3, x_38);
lean_ctor_set(x_187, 2, x_37);
lean_ctor_set(x_187, 1, x_36);
lean_ctor_set(x_187, 0, x_279);
lean_ctor_set(x_186, 3, x_187);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
else
{
lean_object* x_285; 
lean_dec(x_187);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_235);
x_285 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_36);
lean_ctor_set(x_285, 2, x_37);
lean_ctor_set(x_285, 3, x_38);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_285);
lean_ctor_set(x_186, 2, x_278);
lean_ctor_set(x_186, 1, x_277);
lean_ctor_set(x_186, 0, x_260);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_260, 0);
x_287 = lean_ctor_get(x_260, 1);
x_288 = lean_ctor_get(x_260, 2);
x_289 = lean_ctor_get(x_260, 3);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_260);
lean_inc(x_187);
x_290 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_290, 0, x_187);
lean_ctor_set(x_290, 1, x_271);
lean_ctor_set(x_290, 2, x_272);
lean_ctor_set(x_290, 3, x_286);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_291 = x_187;
} else {
 lean_dec_ref(x_187);
 x_291 = lean_box(0);
}
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 4, 1);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_36);
lean_ctor_set(x_292, 2, x_37);
lean_ctor_set(x_292, 3, x_38);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_235);
lean_ctor_set(x_186, 3, x_292);
lean_ctor_set(x_186, 2, x_288);
lean_ctor_set(x_186, 1, x_287);
lean_ctor_set(x_186, 0, x_290);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_269);
return x_186;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_293 = lean_ctor_get(x_186, 1);
x_294 = lean_ctor_get(x_186, 2);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_186);
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_260, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_260, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_260, 3);
lean_inc(x_298);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 x_299 = x_260;
} else {
 lean_dec_ref(x_260);
 x_299 = lean_box(0);
}
lean_inc(x_187);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_187);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_295);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_301 = x_187;
} else {
 lean_dec_ref(x_187);
 x_301 = lean_box(0);
}
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_235);
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 4, 1);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_36);
lean_ctor_set(x_302, 2, x_37);
lean_ctor_set(x_302, 3, x_38);
lean_ctor_set_uint8(x_302, sizeof(void*)*4, x_235);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_296);
lean_ctor_set(x_303, 2, x_297);
lean_ctor_set(x_303, 3, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_269);
return x_303;
}
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_186);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_305 = lean_ctor_get(x_186, 3);
lean_dec(x_305);
x_306 = lean_ctor_get(x_186, 0);
lean_dec(x_306);
x_307 = !lean_is_exclusive(x_187);
if (x_307 == 0)
{
uint8_t x_308; 
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_269);
x_308 = 0;
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_308);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_309 = lean_ctor_get(x_187, 0);
x_310 = lean_ctor_get(x_187, 1);
x_311 = lean_ctor_get(x_187, 2);
x_312 = lean_ctor_get(x_187, 3);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_187);
x_313 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_313, 0, x_309);
lean_ctor_set(x_313, 1, x_310);
lean_ctor_set(x_313, 2, x_311);
lean_ctor_set(x_313, 3, x_312);
lean_ctor_set_uint8(x_313, sizeof(void*)*4, x_269);
x_314 = 0;
lean_ctor_set(x_186, 0, x_313);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_314);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
return x_1;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_315 = lean_ctor_get(x_186, 1);
x_316 = lean_ctor_get(x_186, 2);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_186);
x_317 = lean_ctor_get(x_187, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_187, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_187, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_187, 3);
lean_inc(x_320);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 x_321 = x_187;
} else {
 lean_dec_ref(x_187);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 4, 1);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_317);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_322, 2, x_319);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_269);
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_260);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
lean_ctor_set(x_1, 0, x_324);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_269);
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
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint32_t x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_1, 0);
x_326 = lean_ctor_get(x_1, 1);
x_327 = lean_ctor_get(x_1, 2);
x_328 = lean_ctor_get(x_1, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_1);
x_329 = lean_unbox_uint32(x_326);
x_330 = x_2 < x_329;
if (x_330 == 0)
{
uint32_t x_331; uint8_t x_332; 
x_331 = lean_unbox_uint32(x_326);
x_332 = x_331 < x_2;
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_327);
lean_dec(x_326);
x_333 = lean_box_uint32(x_2);
x_334 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_334, 0, x_325);
lean_ctor_set(x_334, 1, x_333);
lean_ctor_set(x_334, 2, x_3);
lean_ctor_set(x_334, 3, x_328);
lean_ctor_set_uint8(x_334, sizeof(void*)*4, x_7);
return x_334;
}
else
{
uint8_t x_335; 
x_335 = l_RBNode_isRed___rarg(x_328);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_328, x_2, x_3);
x_337 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_337, 0, x_325);
lean_ctor_set(x_337, 1, x_326);
lean_ctor_set(x_337, 2, x_327);
lean_ctor_set(x_337, 3, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*4, x_7);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_328, x_2, x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_338, 3);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_338, 2);
lean_inc(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
x_344 = 0;
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 4, 1);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_341);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_340);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
x_346 = 1;
x_347 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_347, 0, x_325);
lean_ctor_set(x_347, 1, x_326);
lean_ctor_set(x_347, 2, x_327);
lean_ctor_set(x_347, 3, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
return x_347;
}
else
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_340, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_349 = lean_ctor_get(x_338, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_338, 2);
lean_inc(x_350);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_351 = x_338;
} else {
 lean_dec_ref(x_338);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_340, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_340, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_340, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_340, 3);
lean_inc(x_355);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_356 = x_340;
} else {
 lean_dec_ref(x_340);
 x_356 = lean_box(0);
}
x_357 = 1;
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_325);
lean_ctor_set(x_358, 1, x_326);
lean_ctor_set(x_358, 2, x_327);
lean_ctor_set(x_358, 3, x_339);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_357);
if (lean_is_scalar(x_351)) {
 x_359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_359 = x_351;
}
lean_ctor_set(x_359, 0, x_352);
lean_ctor_set(x_359, 1, x_353);
lean_ctor_set(x_359, 2, x_354);
lean_ctor_set(x_359, 3, x_355);
lean_ctor_set_uint8(x_359, sizeof(void*)*4, x_357);
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_350);
lean_ctor_set(x_360, 3, x_359);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_348);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_338, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_338, 2);
lean_inc(x_362);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_363 = x_338;
} else {
 lean_dec_ref(x_338);
 x_363 = lean_box(0);
}
x_364 = 0;
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(1, 4, 1);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_339);
lean_ctor_set(x_365, 1, x_361);
lean_ctor_set(x_365, 2, x_362);
lean_ctor_set(x_365, 3, x_340);
lean_ctor_set_uint8(x_365, sizeof(void*)*4, x_364);
x_366 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_366, 0, x_325);
lean_ctor_set(x_366, 1, x_326);
lean_ctor_set(x_366, 2, x_327);
lean_ctor_set(x_366, 3, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*4, x_348);
return x_366;
}
}
}
else
{
uint8_t x_367; 
x_367 = lean_ctor_get_uint8(x_339, sizeof(void*)*4);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_368 = lean_ctor_get(x_338, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_338, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_338, 3);
lean_inc(x_370);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_371 = x_338;
} else {
 lean_dec_ref(x_338);
 x_371 = lean_box(0);
}
x_372 = lean_ctor_get(x_339, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_339, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_339, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_339, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_376 = x_339;
} else {
 lean_dec_ref(x_339);
 x_376 = lean_box(0);
}
x_377 = 1;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(1, 4, 1);
} else {
 x_378 = x_376;
}
lean_ctor_set(x_378, 0, x_325);
lean_ctor_set(x_378, 1, x_326);
lean_ctor_set(x_378, 2, x_327);
lean_ctor_set(x_378, 3, x_372);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_377);
if (lean_is_scalar(x_371)) {
 x_379 = lean_alloc_ctor(1, 4, 1);
} else {
 x_379 = x_371;
}
lean_ctor_set(x_379, 0, x_375);
lean_ctor_set(x_379, 1, x_368);
lean_ctor_set(x_379, 2, x_369);
lean_ctor_set(x_379, 3, x_370);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_377);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_374);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_367);
return x_380;
}
else
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_338, 3);
lean_inc(x_381);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; 
x_382 = lean_ctor_get(x_338, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_338, 2);
lean_inc(x_383);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_384 = x_338;
} else {
 lean_dec_ref(x_338);
 x_384 = lean_box(0);
}
x_385 = 0;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_339);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_381);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
x_387 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_387, 0, x_325);
lean_ctor_set(x_387, 1, x_326);
lean_ctor_set(x_387, 2, x_327);
lean_ctor_set(x_387, 3, x_386);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_367);
return x_387;
}
else
{
uint8_t x_388; 
x_388 = lean_ctor_get_uint8(x_381, sizeof(void*)*4);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_389 = lean_ctor_get(x_338, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_338, 2);
lean_inc(x_390);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_391 = x_338;
} else {
 lean_dec_ref(x_338);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_381, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_381, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_381, 3);
lean_inc(x_395);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_396 = x_381;
} else {
 lean_dec_ref(x_381);
 x_396 = lean_box(0);
}
lean_inc(x_339);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_325);
lean_ctor_set(x_397, 1, x_326);
lean_ctor_set(x_397, 2, x_327);
lean_ctor_set(x_397, 3, x_339);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_398 = x_339;
} else {
 lean_dec_ref(x_339);
 x_398 = lean_box(0);
}
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_393);
lean_ctor_set(x_399, 2, x_394);
lean_ctor_set(x_399, 3, x_395);
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_391)) {
 x_400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_400 = x_391;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_389);
lean_ctor_set(x_400, 2, x_390);
lean_ctor_set(x_400, 3, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_388);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; 
x_401 = lean_ctor_get(x_338, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_338, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_403 = x_338;
} else {
 lean_dec_ref(x_338);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_339, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_339, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_339, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_339, 3);
lean_inc(x_407);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_408 = x_339;
} else {
 lean_dec_ref(x_339);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_404);
lean_ctor_set(x_409, 1, x_405);
lean_ctor_set(x_409, 2, x_406);
lean_ctor_set(x_409, 3, x_407);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_388);
x_410 = 0;
if (lean_is_scalar(x_403)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_403;
}
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_401);
lean_ctor_set(x_411, 2, x_402);
lean_ctor_set(x_411, 3, x_381);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
x_412 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_412, 0, x_325);
lean_ctor_set(x_412, 1, x_326);
lean_ctor_set(x_412, 2, x_327);
lean_ctor_set(x_412, 3, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*4, x_388);
return x_412;
}
}
}
}
}
}
}
else
{
uint8_t x_413; 
x_413 = l_RBNode_isRed___rarg(x_325);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_325, x_2, x_3);
x_415 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_326);
lean_ctor_set(x_415, 2, x_327);
lean_ctor_set(x_415, 3, x_328);
lean_ctor_set_uint8(x_415, sizeof(void*)*4, x_7);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; 
x_416 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_325, x_2, x_3);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 3);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 2);
lean_inc(x_420);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_421 = x_416;
} else {
 lean_dec_ref(x_416);
 x_421 = lean_box(0);
}
x_422 = 0;
if (lean_is_scalar(x_421)) {
 x_423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_423 = x_421;
}
lean_ctor_set(x_423, 0, x_418);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set(x_423, 2, x_420);
lean_ctor_set(x_423, 3, x_418);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_326);
lean_ctor_set(x_425, 2, x_327);
lean_ctor_set(x_425, 3, x_328);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
else
{
uint8_t x_426; 
x_426 = lean_ctor_get_uint8(x_418, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_416, 2);
lean_inc(x_428);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_429 = x_416;
} else {
 lean_dec_ref(x_416);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_418, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_418, 1);
lean_inc(x_431);
x_432 = lean_ctor_get(x_418, 2);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 3);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 lean_ctor_release(x_418, 3);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
 x_434 = lean_box(0);
}
x_435 = 1;
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_417);
lean_ctor_set(x_436, 1, x_427);
lean_ctor_set(x_436, 2, x_428);
lean_ctor_set(x_436, 3, x_430);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_435);
if (lean_is_scalar(x_429)) {
 x_437 = lean_alloc_ctor(1, 4, 1);
} else {
 x_437 = x_429;
}
lean_ctor_set(x_437, 0, x_433);
lean_ctor_set(x_437, 1, x_326);
lean_ctor_set(x_437, 2, x_327);
lean_ctor_set(x_437, 3, x_328);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_435);
x_438 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_431);
lean_ctor_set(x_438, 2, x_432);
lean_ctor_set(x_438, 3, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*4, x_426);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_416, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_416, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_441 = x_416;
} else {
 lean_dec_ref(x_416);
 x_441 = lean_box(0);
}
x_442 = 0;
if (lean_is_scalar(x_441)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_441;
}
lean_ctor_set(x_443, 0, x_417);
lean_ctor_set(x_443, 1, x_439);
lean_ctor_set(x_443, 2, x_440);
lean_ctor_set(x_443, 3, x_418);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
x_444 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_326);
lean_ctor_set(x_444, 2, x_327);
lean_ctor_set(x_444, 3, x_328);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_426);
return x_444;
}
}
}
else
{
uint8_t x_445; 
x_445 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_416, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_416, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_416, 3);
lean_inc(x_448);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_449 = x_416;
} else {
 lean_dec_ref(x_416);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_417, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_417, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_417, 2);
lean_inc(x_452);
x_453 = lean_ctor_get(x_417, 3);
lean_inc(x_453);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_454 = x_417;
} else {
 lean_dec_ref(x_417);
 x_454 = lean_box(0);
}
x_455 = 1;
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_450);
lean_ctor_set(x_456, 1, x_451);
lean_ctor_set(x_456, 2, x_452);
lean_ctor_set(x_456, 3, x_453);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
if (lean_is_scalar(x_449)) {
 x_457 = lean_alloc_ctor(1, 4, 1);
} else {
 x_457 = x_449;
}
lean_ctor_set(x_457, 0, x_448);
lean_ctor_set(x_457, 1, x_326);
lean_ctor_set(x_457, 2, x_327);
lean_ctor_set(x_457, 3, x_328);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_455);
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_446);
lean_ctor_set(x_458, 2, x_447);
lean_ctor_set(x_458, 3, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_445);
return x_458;
}
else
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_416, 3);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_416, 1);
lean_inc(x_460);
x_461 = lean_ctor_get(x_416, 2);
lean_inc(x_461);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_462 = x_416;
} else {
 lean_dec_ref(x_416);
 x_462 = lean_box(0);
}
x_463 = 0;
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_460);
lean_ctor_set(x_464, 2, x_461);
lean_ctor_set(x_464, 3, x_459);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_463);
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_326);
lean_ctor_set(x_465, 2, x_327);
lean_ctor_set(x_465, 3, x_328);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_445);
return x_465;
}
else
{
uint8_t x_466; 
x_466 = lean_ctor_get_uint8(x_459, sizeof(void*)*4);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_467 = lean_ctor_get(x_416, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_416, 2);
lean_inc(x_468);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_469 = x_416;
} else {
 lean_dec_ref(x_416);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_459, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_459, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_459, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_459, 3);
lean_inc(x_473);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 lean_ctor_release(x_459, 2);
 lean_ctor_release(x_459, 3);
 x_474 = x_459;
} else {
 lean_dec_ref(x_459);
 x_474 = lean_box(0);
}
lean_inc(x_417);
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 4, 1);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_417);
lean_ctor_set(x_475, 1, x_467);
lean_ctor_set(x_475, 2, x_468);
lean_ctor_set(x_475, 3, x_470);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_476 = x_417;
} else {
 lean_dec_ref(x_417);
 x_476 = lean_box(0);
}
lean_ctor_set_uint8(x_475, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_326);
lean_ctor_set(x_477, 2, x_327);
lean_ctor_set(x_477, 3, x_328);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_445);
if (lean_is_scalar(x_469)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_469;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_466);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_479 = lean_ctor_get(x_416, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_416, 2);
lean_inc(x_480);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_481 = x_416;
} else {
 lean_dec_ref(x_416);
 x_481 = lean_box(0);
}
x_482 = lean_ctor_get(x_417, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_417, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_417, 2);
lean_inc(x_484);
x_485 = lean_ctor_get(x_417, 3);
lean_inc(x_485);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_486 = x_417;
} else {
 lean_dec_ref(x_417);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_482);
lean_ctor_set(x_487, 1, x_483);
lean_ctor_set(x_487, 2, x_484);
lean_ctor_set(x_487, 3, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*4, x_466);
x_488 = 0;
if (lean_is_scalar(x_481)) {
 x_489 = lean_alloc_ctor(1, 4, 1);
} else {
 x_489 = x_481;
}
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_479);
lean_ctor_set(x_489, 2, x_480);
lean_ctor_set(x_489, 3, x_459);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_488);
x_490 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_326);
lean_ctor_set(x_490, 2, x_327);
lean_ctor_set(x_490, 3, x_328);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_466);
return x_490;
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
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__6___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at___private_Init_Lean_Parser_Trie_2__insertAux___main___spec__7___rarg(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
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
lean_object* initialize_Init_Data_RBMap_Default(lean_object*);
lean_object* initialize_Init_Lean_Format(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Trie(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RBMap_Default(lean_io_mk_world());
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
