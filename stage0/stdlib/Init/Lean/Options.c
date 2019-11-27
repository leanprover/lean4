// Lean compiler output
// Module: Init.Lean.Options
// Imports: Init.System.IO Init.Data.ToString Init.Lean.KVMap
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
extern lean_object* l_Lean_Name_toString___closed__1;
uint8_t l_String_isInt(lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toNat(lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Options_1__initOptionDeclsRef(lean_object*);
lean_object* l_Lean_getOptionDefaulValue(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl___closed__1;
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Options_2__optionDeclsRef;
lean_object* l_Lean_registerOption___closed__1;
lean_object* l_Lean_registerOption___closed__2;
lean_object* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__4;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l_Lean_Options_empty;
lean_object* l_Lean_setOptionFromString___closed__5;
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Lean_setOptionFromString(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* l_Lean_registerOption(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_String_toInt(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__2;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_Lean_Options_HasEmptyc;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDescr(lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__3;
lean_object* l_List_map___main___at_Lean_setOptionFromString___spec__1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* _init_l_Lean_Options_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_Options_HasEmptyc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Options_empty;
return x_1;
}
}
lean_object* l___private_Init_Lean_Options_1__initOptionDeclsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_registerOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid option declaration '");
return x_1;
}
}
lean_object* _init_l_Lean_registerOption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', option already exists");
return x_1;
}
}
lean_object* l_Lean_registerOption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Options_2__optionDeclsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_NameMap_contains___rarg(x_7, x_1);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_5);
x_12 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_13 = lean_io_ref_set(x_4, x_12, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_2);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_1);
x_16 = l_Lean_registerOption___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerOption___closed__2;
x_19 = lean_string_append(x_17, x_18);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = l_Lean_NameMap_contains___rarg(x_20, x_1);
x_23 = 1;
x_24 = l_Bool_DecidableEq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_20, x_1, x_2);
x_26 = lean_io_ref_set(x_4, x_25, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_2);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_registerOption___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_registerOption___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_getOptionDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Options_2__optionDeclsRef;
x_3 = lean_io_ref_get(x_2, x_1);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = l_Lean_Name_quickLt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_getOptionDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown option '");
return x_1;
}
}
lean_object* l_Lean_getOptionDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Options_2__optionDeclsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_getOptionDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_15, x_1);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_getOptionDecl___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_getOptionDefaulValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_getOptionDescr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_List_map___main___at_Lean_setOptionFromString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_String_trim(x_4);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_String_trim(x_8);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid configuration option entry, it must be of the form '<key> = <value>'");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Bool option value '");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Nat option value '");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Int option value '");
return x_1;
}
}
lean_object* l_Lean_setOptionFromString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_setOptionFromString___closed__1;
x_5 = l_String_splitOn(x_2, x_4);
x_6 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = l_Lean_setOptionFromString___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_10 = l_Lean_setOptionFromString___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
lean_inc(x_13);
x_15 = l_String_toName(x_13);
x_16 = l_Lean_getOptionDefaulValue(x_15, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_18; 
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_name_mk_string(x_20, x_13);
x_22 = l_Lean_KVMap_setString(x_1, x_21, x_14);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_name_mk_string(x_24, x_13);
x_26 = l_Lean_KVMap_setString(x_1, x_25, x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
case 1:
{
uint8_t x_28; 
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = l_Bool_HasRepr___closed__2;
x_31 = lean_string_dec_eq(x_13, x_30);
x_32 = 1;
x_33 = l_Bool_DecidableEq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_34 = l_Bool_HasRepr___closed__1;
x_35 = lean_string_dec_eq(x_13, x_34);
x_36 = l_Bool_DecidableEq(x_35, x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_1);
x_37 = l_Lean_setOptionFromString___closed__3;
x_38 = lean_string_append(x_37, x_14);
lean_dec(x_14);
x_39 = l_Char_HasRepr___closed__1;
x_40 = lean_string_append(x_38, x_39);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_40);
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_14);
x_41 = lean_box(0);
x_42 = lean_name_mk_string(x_41, x_13);
x_43 = 0;
x_44 = l_Lean_KVMap_setBool(x_1, x_42, x_43);
lean_ctor_set(x_16, 0, x_44);
return x_16;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
x_45 = lean_box(0);
x_46 = lean_name_mk_string(x_45, x_13);
x_47 = l_Lean_KVMap_setBool(x_1, x_46, x_32);
lean_ctor_set(x_16, 0, x_47);
return x_16;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_dec(x_16);
x_49 = l_Bool_HasRepr___closed__2;
x_50 = lean_string_dec_eq(x_13, x_49);
x_51 = 1;
x_52 = l_Bool_DecidableEq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_53 = l_Bool_HasRepr___closed__1;
x_54 = lean_string_dec_eq(x_13, x_53);
x_55 = l_Bool_DecidableEq(x_54, x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_13);
lean_dec(x_1);
x_56 = l_Lean_setOptionFromString___closed__3;
x_57 = lean_string_append(x_56, x_14);
lean_dec(x_14);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_48);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_14);
x_61 = lean_box(0);
x_62 = lean_name_mk_string(x_61, x_13);
x_63 = 0;
x_64 = l_Lean_KVMap_setBool(x_1, x_62, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_48);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_14);
x_66 = lean_box(0);
x_67 = lean_name_mk_string(x_66, x_13);
x_68 = l_Lean_KVMap_setBool(x_1, x_67, x_51);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_48);
return x_69;
}
}
}
case 2:
{
uint8_t x_70; 
lean_dec(x_17);
x_70 = !lean_is_exclusive(x_16);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_16, 0);
lean_dec(x_71);
x_72 = lean_box(0);
x_73 = lean_name_mk_string(x_72, x_13);
x_74 = l_String_toName(x_14);
x_75 = l_Lean_KVMap_setName(x_1, x_73, x_74);
lean_ctor_set(x_16, 0, x_75);
return x_16;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_16, 1);
lean_inc(x_76);
lean_dec(x_16);
x_77 = lean_box(0);
x_78 = lean_name_mk_string(x_77, x_13);
x_79 = l_String_toName(x_14);
x_80 = l_Lean_KVMap_setName(x_1, x_78, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
}
case 3:
{
uint8_t x_82; 
lean_dec(x_17);
x_82 = !lean_is_exclusive(x_16);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_16, 0);
lean_dec(x_83);
x_84 = l_String_isNat(x_14);
x_85 = 1;
x_86 = l_Bool_DecidableEq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_13);
lean_dec(x_1);
x_87 = l_Lean_setOptionFromString___closed__4;
x_88 = lean_string_append(x_87, x_14);
lean_dec(x_14);
x_89 = l_Char_HasRepr___closed__1;
x_90 = lean_string_append(x_88, x_89);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_90);
return x_16;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = lean_name_mk_string(x_91, x_13);
x_93 = l_String_toNat(x_14);
lean_dec(x_14);
x_94 = l_Lean_KVMap_setNat(x_1, x_92, x_93);
lean_ctor_set(x_16, 0, x_94);
return x_16;
}
}
else
{
lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_16, 1);
lean_inc(x_95);
lean_dec(x_16);
x_96 = l_String_isNat(x_14);
x_97 = 1;
x_98 = l_Bool_DecidableEq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_13);
lean_dec(x_1);
x_99 = l_Lean_setOptionFromString___closed__4;
x_100 = lean_string_append(x_99, x_14);
lean_dec(x_14);
x_101 = l_Char_HasRepr___closed__1;
x_102 = lean_string_append(x_100, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_box(0);
x_105 = lean_name_mk_string(x_104, x_13);
x_106 = l_String_toNat(x_14);
lean_dec(x_14);
x_107 = l_Lean_KVMap_setNat(x_1, x_105, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_95);
return x_108;
}
}
}
default: 
{
uint8_t x_109; 
lean_dec(x_17);
x_109 = !lean_is_exclusive(x_16);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_16, 0);
lean_dec(x_110);
lean_inc(x_14);
x_111 = l_String_isInt(x_14);
x_112 = 1;
x_113 = l_Bool_DecidableEq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_13);
lean_dec(x_1);
x_114 = l_Lean_setOptionFromString___closed__5;
x_115 = lean_string_append(x_114, x_14);
lean_dec(x_14);
x_116 = l_Char_HasRepr___closed__1;
x_117 = lean_string_append(x_115, x_116);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_117);
return x_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_box(0);
x_119 = lean_name_mk_string(x_118, x_13);
x_120 = l_String_toInt(x_14);
x_121 = l_Lean_KVMap_setInt(x_1, x_119, x_120);
lean_ctor_set(x_16, 0, x_121);
return x_16;
}
}
else
{
lean_object* x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_16, 1);
lean_inc(x_122);
lean_dec(x_16);
lean_inc(x_14);
x_123 = l_String_isInt(x_14);
x_124 = 1;
x_125 = l_Bool_DecidableEq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_13);
lean_dec(x_1);
x_126 = l_Lean_setOptionFromString___closed__5;
x_127 = lean_string_append(x_126, x_14);
lean_dec(x_14);
x_128 = l_Char_HasRepr___closed__1;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_box(0);
x_132 = lean_name_mk_string(x_131, x_13);
x_133 = l_String_toInt(x_14);
x_134 = l_Lean_KVMap_setInt(x_1, x_132, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_122);
return x_135;
}
}
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_16);
if (x_136 == 0)
{
return x_16;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_16, 0);
x_138 = lean_ctor_get(x_16, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_16);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_140 = l_Lean_setOptionFromString___closed__2;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_3);
return x_141;
}
}
}
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Lean_KVMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Options(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean_mark_persistent(l_Lean_Options_empty);
l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean_mark_persistent(l_Lean_Options_HasEmptyc);
res = l___private_Init_Lean_Options_1__initOptionDeclsRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Init_Lean_Options_2__optionDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Init_Lean_Options_2__optionDeclsRef);
lean_dec_ref(res);
l_Lean_registerOption___closed__1 = _init_l_Lean_registerOption___closed__1();
lean_mark_persistent(l_Lean_registerOption___closed__1);
l_Lean_registerOption___closed__2 = _init_l_Lean_registerOption___closed__2();
lean_mark_persistent(l_Lean_registerOption___closed__2);
l_Lean_getOptionDecl___closed__1 = _init_l_Lean_getOptionDecl___closed__1();
lean_mark_persistent(l_Lean_getOptionDecl___closed__1);
l_Lean_setOptionFromString___closed__1 = _init_l_Lean_setOptionFromString___closed__1();
lean_mark_persistent(l_Lean_setOptionFromString___closed__1);
l_Lean_setOptionFromString___closed__2 = _init_l_Lean_setOptionFromString___closed__2();
lean_mark_persistent(l_Lean_setOptionFromString___closed__2);
l_Lean_setOptionFromString___closed__3 = _init_l_Lean_setOptionFromString___closed__3();
lean_mark_persistent(l_Lean_setOptionFromString___closed__3);
l_Lean_setOptionFromString___closed__4 = _init_l_Lean_setOptionFromString___closed__4();
lean_mark_persistent(l_Lean_setOptionFromString___closed__4);
l_Lean_setOptionFromString___closed__5 = _init_l_Lean_setOptionFromString___closed__5();
lean_mark_persistent(l_Lean_setOptionFromString___closed__5);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
