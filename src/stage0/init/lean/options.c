// Lean compiler output
// Module: Init.Lean.Options
// Imports: Init.Lean.KVMap Init.System.IO Init.Control.Combinators Init.Data.ToString
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
lean_object* l_Lean_setOptionFromString___closed__2;
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
lean_object* l_String_toNat(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__5;
lean_object* l_Lean_Options_HasEmptyc;
lean_object* l_Lean_KVMap_setNat(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_setOptionFromString___spec__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl___closed__1;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Options_empty;
lean_object* l_Lean_registerOption___closed__1;
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Options_1__initOptionDeclsRef(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_registerOption(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__4;
uint8_t l_String_isInt(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_Prim_mkRef(lean_object*, lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_String_split(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Options_2__optionDeclsRef;
lean_object* l_Lean_getOptionDescr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__3;
lean_object* l_Lean_getOptionDefaulValue(lean_object*, lean_object*);
lean_object* l_Lean_registerOption___closed__2;
lean_object* l_Lean_setOptionFromString(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_String_toInt(lean_object*);
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_NameMap_contains___rarg(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
x_10 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_11 = lean_io_ref_set(x_4, x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_2);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_registerOption___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_registerOption___closed__2;
x_17 = lean_string_append(x_15, x_16);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = l_Lean_NameMap_contains___rarg(x_18, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_18, x_1, x_2);
x_24 = lean_io_ref_set(x_4, x_23, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_2);
x_25 = l_System_FilePath_dirName___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_1);
x_27 = l_Lean_registerOption___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Lean_registerOption___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
return x_5;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
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
x_8 = l_System_FilePath_dirName___closed__1;
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
x_18 = l_System_FilePath_dirName___closed__1;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l_Lean_setOptionFromString___closed__1;
x_7 = l_String_split(x_2, x_6);
x_8 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_setOptionFromString___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = l_Lean_setOptionFromString___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
lean_ctor_set(x_3, 0, x_15);
lean_inc(x_13);
x_16 = l_String_toName(x_13);
x_17 = l_Lean_getOptionDefaulValue(x_16, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_name_mk_string(x_21, x_13);
x_23 = l_Lean_KVMap_setString(x_1, x_22, x_14);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_name_mk_string(x_25, x_13);
x_27 = l_Lean_KVMap_setString(x_1, x_26, x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
case 1:
{
uint8_t x_29; 
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_17, 0);
lean_dec(x_30);
x_31 = l_Bool_HasRepr___closed__2;
x_32 = lean_string_dec_eq(x_13, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Bool_HasRepr___closed__1;
x_34 = lean_string_dec_eq(x_13, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_1);
x_35 = l_Lean_setOptionFromString___closed__3;
x_36 = lean_string_append(x_35, x_14);
lean_dec(x_14);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean_string_append(x_36, x_37);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_38);
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = lean_name_mk_string(x_39, x_13);
x_41 = 0;
x_42 = l_Lean_KVMap_setBool(x_1, x_40, x_41);
lean_ctor_set(x_17, 0, x_42);
return x_17;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_14);
x_43 = lean_box(0);
x_44 = lean_name_mk_string(x_43, x_13);
x_45 = 1;
x_46 = l_Lean_KVMap_setBool(x_1, x_44, x_45);
lean_ctor_set(x_17, 0, x_46);
return x_17;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_dec(x_17);
x_48 = l_Bool_HasRepr___closed__2;
x_49 = lean_string_dec_eq(x_13, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Bool_HasRepr___closed__1;
x_51 = lean_string_dec_eq(x_13, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_13);
lean_dec(x_1);
x_52 = l_Lean_setOptionFromString___closed__3;
x_53 = lean_string_append(x_52, x_14);
lean_dec(x_14);
x_54 = l_Char_HasRepr___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_14);
x_57 = lean_box(0);
x_58 = lean_name_mk_string(x_57, x_13);
x_59 = 0;
x_60 = l_Lean_KVMap_setBool(x_1, x_58, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_14);
x_62 = lean_box(0);
x_63 = lean_name_mk_string(x_62, x_13);
x_64 = 1;
x_65 = l_Lean_KVMap_setBool(x_1, x_63, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_47);
return x_66;
}
}
}
case 2:
{
uint8_t x_67; 
lean_dec(x_18);
x_67 = !lean_is_exclusive(x_17);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_17, 0);
lean_dec(x_68);
x_69 = lean_box(0);
x_70 = lean_name_mk_string(x_69, x_13);
x_71 = l_String_toName(x_14);
x_72 = l_Lean_KVMap_setName(x_1, x_70, x_71);
lean_ctor_set(x_17, 0, x_72);
return x_17;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_17, 1);
lean_inc(x_73);
lean_dec(x_17);
x_74 = lean_box(0);
x_75 = lean_name_mk_string(x_74, x_13);
x_76 = l_String_toName(x_14);
x_77 = l_Lean_KVMap_setName(x_1, x_75, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
}
case 3:
{
uint8_t x_79; 
lean_dec(x_18);
x_79 = !lean_is_exclusive(x_17);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_17, 0);
lean_dec(x_80);
x_81 = l_String_isNat(x_14);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_1);
x_82 = l_Lean_setOptionFromString___closed__4;
x_83 = lean_string_append(x_82, x_14);
lean_dec(x_14);
x_84 = l_Char_HasRepr___closed__1;
x_85 = lean_string_append(x_83, x_84);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_85);
return x_17;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_box(0);
x_87 = lean_name_mk_string(x_86, x_13);
x_88 = l_String_toNat(x_14);
lean_dec(x_14);
x_89 = l_Lean_KVMap_setNat(x_1, x_87, x_88);
lean_ctor_set(x_17, 0, x_89);
return x_17;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_dec(x_17);
x_91 = l_String_isNat(x_14);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_13);
lean_dec(x_1);
x_92 = l_Lean_setOptionFromString___closed__4;
x_93 = lean_string_append(x_92, x_14);
lean_dec(x_14);
x_94 = l_Char_HasRepr___closed__1;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_box(0);
x_98 = lean_name_mk_string(x_97, x_13);
x_99 = l_String_toNat(x_14);
lean_dec(x_14);
x_100 = l_Lean_KVMap_setNat(x_1, x_98, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_90);
return x_101;
}
}
}
default: 
{
uint8_t x_102; 
lean_dec(x_18);
x_102 = !lean_is_exclusive(x_17);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_17, 0);
lean_dec(x_103);
lean_inc(x_14);
x_104 = l_String_isInt(x_14);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_13);
lean_dec(x_1);
x_105 = l_Lean_setOptionFromString___closed__5;
x_106 = lean_string_append(x_105, x_14);
lean_dec(x_14);
x_107 = l_Char_HasRepr___closed__1;
x_108 = lean_string_append(x_106, x_107);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_108);
return x_17;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_box(0);
x_110 = lean_name_mk_string(x_109, x_13);
x_111 = l_String_toInt(x_14);
x_112 = l_Lean_KVMap_setInt(x_1, x_110, x_111);
lean_ctor_set(x_17, 0, x_112);
return x_17;
}
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_17, 1);
lean_inc(x_113);
lean_dec(x_17);
lean_inc(x_14);
x_114 = l_String_isInt(x_14);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_13);
lean_dec(x_1);
x_115 = l_Lean_setOptionFromString___closed__5;
x_116 = lean_string_append(x_115, x_14);
lean_dec(x_14);
x_117 = l_Char_HasRepr___closed__1;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_box(0);
x_121 = lean_name_mk_string(x_120, x_13);
x_122 = l_String_toInt(x_14);
x_123 = l_Lean_KVMap_setInt(x_1, x_121, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_113);
return x_124;
}
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_17);
if (x_125 == 0)
{
return x_17;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_17, 0);
x_127 = lean_ctor_get(x_17, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_17);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_129 = l_Lean_setOptionFromString___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_129);
return x_3;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_3, 1);
lean_inc(x_130);
lean_dec(x_3);
x_131 = l_Lean_setOptionFromString___closed__1;
x_132 = l_String_split(x_2, x_131);
x_133 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_1);
x_134 = l_Lean_setOptionFromString___closed__2;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_1);
x_137 = l_Lean_setOptionFromString___closed__2;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
return x_138;
}
else
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
lean_dec(x_133);
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
lean_inc(x_140);
x_144 = l_String_toName(x_140);
x_145 = l_Lean_getOptionDefaulValue(x_144, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
switch (lean_obj_tag(x_146)) {
case 0:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_box(0);
x_150 = lean_name_mk_string(x_149, x_140);
x_151 = l_Lean_KVMap_setString(x_1, x_150, x_141);
if (lean_is_scalar(x_148)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_148;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
return x_152;
}
case 1:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_146);
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_154 = x_145;
} else {
 lean_dec_ref(x_145);
 x_154 = lean_box(0);
}
x_155 = l_Bool_HasRepr___closed__2;
x_156 = lean_string_dec_eq(x_140, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Bool_HasRepr___closed__1;
x_158 = lean_string_dec_eq(x_140, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_140);
lean_dec(x_1);
x_159 = l_Lean_setOptionFromString___closed__3;
x_160 = lean_string_append(x_159, x_141);
lean_dec(x_141);
x_161 = l_Char_HasRepr___closed__1;
x_162 = lean_string_append(x_160, x_161);
if (lean_is_scalar(x_154)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_154;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_153);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_141);
x_164 = lean_box(0);
x_165 = lean_name_mk_string(x_164, x_140);
x_166 = 0;
x_167 = l_Lean_KVMap_setBool(x_1, x_165, x_166);
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_153);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_141);
x_169 = lean_box(0);
x_170 = lean_name_mk_string(x_169, x_140);
x_171 = 1;
x_172 = l_Lean_KVMap_setBool(x_1, x_170, x_171);
if (lean_is_scalar(x_154)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_154;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_153);
return x_173;
}
}
case 2:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_146);
x_174 = lean_ctor_get(x_145, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_175 = x_145;
} else {
 lean_dec_ref(x_145);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
x_177 = lean_name_mk_string(x_176, x_140);
x_178 = l_String_toName(x_141);
x_179 = l_Lean_KVMap_setName(x_1, x_177, x_178);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
case 3:
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_146);
x_181 = lean_ctor_get(x_145, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_182 = x_145;
} else {
 lean_dec_ref(x_145);
 x_182 = lean_box(0);
}
x_183 = l_String_isNat(x_141);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_140);
lean_dec(x_1);
x_184 = l_Lean_setOptionFromString___closed__4;
x_185 = lean_string_append(x_184, x_141);
lean_dec(x_141);
x_186 = l_Char_HasRepr___closed__1;
x_187 = lean_string_append(x_185, x_186);
if (lean_is_scalar(x_182)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_182;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_box(0);
x_190 = lean_name_mk_string(x_189, x_140);
x_191 = l_String_toNat(x_141);
lean_dec(x_141);
x_192 = l_Lean_KVMap_setNat(x_1, x_190, x_191);
if (lean_is_scalar(x_182)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_182;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_181);
return x_193;
}
}
default: 
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_146);
x_194 = lean_ctor_get(x_145, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_195 = x_145;
} else {
 lean_dec_ref(x_145);
 x_195 = lean_box(0);
}
lean_inc(x_141);
x_196 = l_String_isInt(x_141);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_140);
lean_dec(x_1);
x_197 = l_Lean_setOptionFromString___closed__5;
x_198 = lean_string_append(x_197, x_141);
lean_dec(x_141);
x_199 = l_Char_HasRepr___closed__1;
x_200 = lean_string_append(x_198, x_199);
if (lean_is_scalar(x_195)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_195;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_194);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_box(0);
x_203 = lean_name_mk_string(x_202, x_140);
x_204 = l_String_toInt(x_141);
x_205 = l_Lean_KVMap_setInt(x_1, x_203, x_204);
if (lean_is_scalar(x_195)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_195;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_194);
return x_206;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_1);
x_207 = lean_ctor_get(x_145, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_145, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_209 = x_145;
} else {
 lean_dec_ref(x_145);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_139);
lean_dec(x_136);
lean_dec(x_133);
lean_dec(x_1);
x_211 = l_Lean_setOptionFromString___closed__2;
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_130);
return x_212;
}
}
}
}
}
}
lean_object* initialize_Init_Lean_KVMap(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Control_Combinators(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Options(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_KVMap(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_System_IO(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Combinators(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_ToString(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean_mark_persistent(l_Lean_Options_empty);
l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean_mark_persistent(l_Lean_Options_HasEmptyc);
w = l___private_Init_Lean_Options_1__initOptionDeclsRef(w);
if (lean_io_result_is_error(w)) return w;
l___private_Init_Lean_Options_2__optionDeclsRef = lean_io_result_get_value(w);
lean_mark_persistent(l___private_Init_Lean_Options_2__optionDeclsRef);
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
return w;
}
#ifdef __cplusplus
}
#endif
