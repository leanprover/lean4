// Lean compiler output
// Module: Init.Lean.Data.Options
// Imports: Init.System.IO Init.Data.Array Init.Data.ToString Init.Lean.Data.KVMap
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
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_verboseOption___closed__3;
lean_object* l_String_toNat(lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setString(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_maxMemoryOption(lean_object*);
lean_object* l_Lean_getOptionDefaulValue(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl___closed__1;
uint8_t l_Lean_NameMap_contains___rarg(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_HasToString(lean_object*);
lean_object* l_Lean_Options_HasToString___closed__1;
lean_object* l_Lean_timeoutOption___closed__4;
lean_object* l_Lean_registerOption___closed__1;
lean_object* l_Lean_registerOption___closed__2;
lean_object* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__4;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Options_Inhabited;
lean_object* l_Lean_Options_HasToString;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* lean_get_option_decls_array(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setInt(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isNat(lean_object*);
lean_object* l_Lean_verboseOption___closed__4;
lean_object* l_Lean_Options_empty;
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_setOptionFromString___closed__5;
lean_object* l_Lean_maxMemoryOption___closed__5;
lean_object* l_Lean_maxMemoryOption___closed__3;
lean_object* l_Lean_KVMap_setName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Lean_timeoutOption___closed__2;
lean_object* l_Lean_setOptionFromString(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setOptionFromString___closed__6;
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l___private_Init_Lean_Data_Options_1__initOptionDeclsRef(lean_object*);
lean_object* l_Lean_verboseOption___closed__2;
lean_object* l_Lean_setOptionFromString___closed__1;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_verboseOption___closed__1;
lean_object* l_Lean_timeoutOption___closed__1;
lean_object* l_Lean_maxMemoryOption___closed__1;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
lean_object* l_Lean_maxMemoryOption___closed__2;
lean_object* l_String_toInt(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__2;
lean_object* l_Lean_timeoutOption___closed__3;
lean_object* l_Lean_Options_HasEmptyc;
lean_object* l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_verboseOption___closed__5;
lean_object* l_Lean_getOptionDescr(lean_object*, lean_object*);
lean_object* l_Lean_timeoutOption(lean_object*);
lean_object* l_Lean_setOptionFromString___closed__3;
lean_object* l_Lean_maxMemoryOption___closed__4;
lean_object* l___private_Init_Lean_Data_Options_2__optionDeclsRef;
lean_object* l_List_map___main___at_Lean_setOptionFromString___spec__1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_verboseOption(lean_object*);
lean_object* l_Lean_timeoutOption___closed__5;
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
lean_object* _init_l_Lean_Options_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Options_empty;
return x_1;
}
}
lean_object* _init_l_Lean_Options_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_KVMap_HasToString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Options_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Options_HasToString___closed__1;
return x_1;
}
}
lean_object* l___private_Init_Lean_Data_Options_1__initOptionDeclsRef(lean_object* x_1) {
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
lean_object* lean_register_option(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Data_Options_2__optionDeclsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_NameMap_contains___rarg(x_7, x_1);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_5);
x_11 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_12 = lean_io_ref_set(x_4, x_11, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_2);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_1);
x_15 = l_Lean_registerOption___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_registerOption___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = l_Lean_NameMap_contains___rarg(x_20, x_1);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_20, x_1, x_2);
x_25 = lean_io_ref_set(x_4, x_24, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_2);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_registerOption___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_registerOption___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
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
x_2 = l___private_Init_Lean_Data_Options_2__optionDeclsRef;
x_3 = lean_io_ref_get(x_2, x_1);
return x_3;
}
}
lean_object* l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
lean_object* lean_get_option_decls_array(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Data_Options_2__optionDeclsRef;
x_3 = lean_io_ref_get(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Array_empty___closed__1;
x_7 = l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(x_6, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = l_Array_empty___closed__1;
x_11 = l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(x_10, x_8);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_getOptionDeclsArray___spec__1(x_1, x_2);
lean_dec(x_2);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = l_Lean_Name_quickLt(x_5, x_2);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
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
x_3 = l___private_Init_Lean_Data_Options_2__optionDeclsRef;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_getOptionDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_1);
x_21 = l_Lean_getOptionDecl___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setOptionFromString___closed__2;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Bool option value '");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid Nat option value '");
return x_1;
}
}
lean_object* _init_l_Lean_setOptionFromString___closed__6() {
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
x_7 = l_Lean_setOptionFromString___closed__3;
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
x_10 = l_Lean_setOptionFromString___closed__3;
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = l_Bool_HasRepr___closed__2;
x_31 = lean_string_dec_eq(x_13, x_30);
x_32 = l_coeDecidableEq(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_33 = l_Bool_HasRepr___closed__1;
x_34 = lean_string_dec_eq(x_13, x_33);
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_1);
x_36 = l_Lean_setOptionFromString___closed__4;
x_37 = lean_string_append(x_36, x_14);
lean_dec(x_14);
x_38 = l_Char_HasRepr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
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
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_14);
x_45 = lean_box(0);
x_46 = lean_name_mk_string(x_45, x_13);
x_47 = 1;
x_48 = l_Lean_KVMap_setBool(x_1, x_46, x_47);
lean_ctor_set(x_16, 0, x_48);
return x_16;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_dec(x_16);
x_50 = l_Bool_HasRepr___closed__2;
x_51 = lean_string_dec_eq(x_13, x_50);
x_52 = l_coeDecidableEq(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_53 = l_Bool_HasRepr___closed__1;
x_54 = lean_string_dec_eq(x_13, x_53);
x_55 = l_coeDecidableEq(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_13);
lean_dec(x_1);
x_56 = l_Lean_setOptionFromString___closed__4;
x_57 = lean_string_append(x_56, x_14);
lean_dec(x_14);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_14);
x_62 = lean_box(0);
x_63 = lean_name_mk_string(x_62, x_13);
x_64 = 0;
x_65 = l_Lean_KVMap_setBool(x_1, x_63, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_49);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_14);
x_67 = lean_box(0);
x_68 = lean_name_mk_string(x_67, x_13);
x_69 = 1;
x_70 = l_Lean_KVMap_setBool(x_1, x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_49);
return x_71;
}
}
}
case 2:
{
uint8_t x_72; 
lean_dec(x_17);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_16, 0);
lean_dec(x_73);
x_74 = lean_box(0);
x_75 = lean_name_mk_string(x_74, x_13);
x_76 = l_String_toName(x_14);
x_77 = l_Lean_KVMap_setName(x_1, x_75, x_76);
lean_ctor_set(x_16, 0, x_77);
return x_16;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_16, 1);
lean_inc(x_78);
lean_dec(x_16);
x_79 = lean_box(0);
x_80 = lean_name_mk_string(x_79, x_13);
x_81 = l_String_toName(x_14);
x_82 = l_Lean_KVMap_setName(x_1, x_80, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_78);
return x_83;
}
}
case 3:
{
uint8_t x_84; 
lean_dec(x_17);
x_84 = !lean_is_exclusive(x_16);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_16, 0);
lean_dec(x_85);
x_86 = l_String_isNat(x_14);
x_87 = l_coeDecidableEq(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_13);
lean_dec(x_1);
x_88 = l_Lean_setOptionFromString___closed__5;
x_89 = lean_string_append(x_88, x_14);
lean_dec(x_14);
x_90 = l_Char_HasRepr___closed__1;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_92);
return x_16;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_box(0);
x_94 = lean_name_mk_string(x_93, x_13);
x_95 = l_String_toNat(x_14);
lean_dec(x_14);
x_96 = l_Lean_KVMap_setNat(x_1, x_94, x_95);
lean_ctor_set(x_16, 0, x_96);
return x_16;
}
}
else
{
lean_object* x_97; uint8_t x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_16, 1);
lean_inc(x_97);
lean_dec(x_16);
x_98 = l_String_isNat(x_14);
x_99 = l_coeDecidableEq(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_13);
lean_dec(x_1);
x_100 = l_Lean_setOptionFromString___closed__5;
x_101 = lean_string_append(x_100, x_14);
lean_dec(x_14);
x_102 = l_Char_HasRepr___closed__1;
x_103 = lean_string_append(x_101, x_102);
x_104 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_97);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_box(0);
x_107 = lean_name_mk_string(x_106, x_13);
x_108 = l_String_toNat(x_14);
lean_dec(x_14);
x_109 = l_Lean_KVMap_setNat(x_1, x_107, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_97);
return x_110;
}
}
}
default: 
{
uint8_t x_111; 
lean_dec(x_17);
x_111 = !lean_is_exclusive(x_16);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_16, 0);
lean_dec(x_112);
lean_inc(x_14);
x_113 = l_String_isInt(x_14);
x_114 = l_coeDecidableEq(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_13);
lean_dec(x_1);
x_115 = l_Lean_setOptionFromString___closed__6;
x_116 = lean_string_append(x_115, x_14);
lean_dec(x_14);
x_117 = l_Char_HasRepr___closed__1;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_119);
return x_16;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_box(0);
x_121 = lean_name_mk_string(x_120, x_13);
x_122 = l_String_toInt(x_14);
x_123 = l_Lean_KVMap_setInt(x_1, x_121, x_122);
lean_ctor_set(x_16, 0, x_123);
return x_16;
}
}
else
{
lean_object* x_124; uint8_t x_125; uint8_t x_126; 
x_124 = lean_ctor_get(x_16, 1);
lean_inc(x_124);
lean_dec(x_16);
lean_inc(x_14);
x_125 = l_String_isInt(x_14);
x_126 = l_coeDecidableEq(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_13);
lean_dec(x_1);
x_127 = l_Lean_setOptionFromString___closed__6;
x_128 = lean_string_append(x_127, x_14);
lean_dec(x_14);
x_129 = l_Char_HasRepr___closed__1;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_box(0);
x_134 = lean_name_mk_string(x_133, x_13);
x_135 = l_String_toInt(x_14);
x_136 = l_Lean_KVMap_setInt(x_1, x_134, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_124);
return x_137;
}
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_16);
if (x_138 == 0)
{
return x_16;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_16, 0);
x_140 = lean_ctor_get(x_16, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_16);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_142 = l_Lean_setOptionFromString___closed__3;
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
return x_143;
}
}
}
}
}
lean_object* _init_l_Lean_verboseOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("verbose");
return x_1;
}
}
lean_object* _init_l_Lean_verboseOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_verboseOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_verboseOption___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_verboseOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("disable/enable verbose messages");
return x_1;
}
}
lean_object* _init_l_Lean_verboseOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_verboseOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_verboseOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_verboseOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_verboseOption___closed__2;
x_3 = l_Lean_verboseOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_timeoutOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("timeout");
return x_1;
}
}
lean_object* _init_l_Lean_timeoutOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_timeoutOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_timeoutOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_timeoutOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("the (deterministic) timeout is measured as the maximum of memory allocations (in thousands) per task, the default is unbounded");
return x_1;
}
}
lean_object* _init_l_Lean_timeoutOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_timeoutOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_timeoutOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_timeoutOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_timeoutOption___closed__2;
x_3 = l_Lean_timeoutOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_maxMemoryOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxMemory");
return x_1;
}
}
lean_object* _init_l_Lean_maxMemoryOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_maxMemoryOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_maxMemoryOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2048u);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_maxMemoryOption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum amount of memory available for Lean in megabytes");
return x_1;
}
}
lean_object* _init_l_Lean_maxMemoryOption___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_maxMemoryOption___closed__3;
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_maxMemoryOption___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_maxMemoryOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_maxMemoryOption___closed__2;
x_3 = l_Lean_maxMemoryOption___closed__5;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Lean_Data_KVMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Data_Options(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean_mark_persistent(l_Lean_Options_empty);
l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean_mark_persistent(l_Lean_Options_HasEmptyc);
l_Lean_Options_Inhabited = _init_l_Lean_Options_Inhabited();
lean_mark_persistent(l_Lean_Options_Inhabited);
l_Lean_Options_HasToString___closed__1 = _init_l_Lean_Options_HasToString___closed__1();
lean_mark_persistent(l_Lean_Options_HasToString___closed__1);
l_Lean_Options_HasToString = _init_l_Lean_Options_HasToString();
lean_mark_persistent(l_Lean_Options_HasToString);
res = l___private_Init_Lean_Data_Options_1__initOptionDeclsRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Init_Lean_Data_Options_2__optionDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Init_Lean_Data_Options_2__optionDeclsRef);
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
l_Lean_setOptionFromString___closed__6 = _init_l_Lean_setOptionFromString___closed__6();
lean_mark_persistent(l_Lean_setOptionFromString___closed__6);
l_Lean_verboseOption___closed__1 = _init_l_Lean_verboseOption___closed__1();
lean_mark_persistent(l_Lean_verboseOption___closed__1);
l_Lean_verboseOption___closed__2 = _init_l_Lean_verboseOption___closed__2();
lean_mark_persistent(l_Lean_verboseOption___closed__2);
l_Lean_verboseOption___closed__3 = _init_l_Lean_verboseOption___closed__3();
lean_mark_persistent(l_Lean_verboseOption___closed__3);
l_Lean_verboseOption___closed__4 = _init_l_Lean_verboseOption___closed__4();
lean_mark_persistent(l_Lean_verboseOption___closed__4);
l_Lean_verboseOption___closed__5 = _init_l_Lean_verboseOption___closed__5();
lean_mark_persistent(l_Lean_verboseOption___closed__5);
res = l_Lean_verboseOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_timeoutOption___closed__1 = _init_l_Lean_timeoutOption___closed__1();
lean_mark_persistent(l_Lean_timeoutOption___closed__1);
l_Lean_timeoutOption___closed__2 = _init_l_Lean_timeoutOption___closed__2();
lean_mark_persistent(l_Lean_timeoutOption___closed__2);
l_Lean_timeoutOption___closed__3 = _init_l_Lean_timeoutOption___closed__3();
lean_mark_persistent(l_Lean_timeoutOption___closed__3);
l_Lean_timeoutOption___closed__4 = _init_l_Lean_timeoutOption___closed__4();
lean_mark_persistent(l_Lean_timeoutOption___closed__4);
l_Lean_timeoutOption___closed__5 = _init_l_Lean_timeoutOption___closed__5();
lean_mark_persistent(l_Lean_timeoutOption___closed__5);
res = l_Lean_timeoutOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_maxMemoryOption___closed__1 = _init_l_Lean_maxMemoryOption___closed__1();
lean_mark_persistent(l_Lean_maxMemoryOption___closed__1);
l_Lean_maxMemoryOption___closed__2 = _init_l_Lean_maxMemoryOption___closed__2();
lean_mark_persistent(l_Lean_maxMemoryOption___closed__2);
l_Lean_maxMemoryOption___closed__3 = _init_l_Lean_maxMemoryOption___closed__3();
lean_mark_persistent(l_Lean_maxMemoryOption___closed__3);
l_Lean_maxMemoryOption___closed__4 = _init_l_Lean_maxMemoryOption___closed__4();
lean_mark_persistent(l_Lean_maxMemoryOption___closed__4);
l_Lean_maxMemoryOption___closed__5 = _init_l_Lean_maxMemoryOption___closed__5();
lean_mark_persistent(l_Lean_maxMemoryOption___closed__5);
res = l_Lean_maxMemoryOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
