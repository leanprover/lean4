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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_NameMap_contains___rarg(x_7, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_5);
x_10 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_11 = lean_io_ref_set(x_4, x_10, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_2);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_registerOption___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_registerOption___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = l_Lean_NameMap_contains___rarg(x_19, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_19, x_1, x_2);
x_23 = lean_io_ref_set(x_4, x_22, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_2);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_1);
x_26 = l_Lean_registerOption___closed__1;
x_27 = lean_string_append(x_26, x_25);
lean_dec(x_25);
x_28 = l_Lean_registerOption___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = l_Bool_HasRepr___closed__2;
x_31 = lean_string_dec_eq(x_13, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Bool_HasRepr___closed__1;
x_33 = lean_string_dec_eq(x_13, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_1);
x_34 = l_Lean_setOptionFromString___closed__4;
x_35 = lean_string_append(x_34, x_14);
lean_dec(x_14);
x_36 = l_Char_HasRepr___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_38);
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = lean_name_mk_string(x_39, x_13);
x_41 = 0;
x_42 = l_Lean_KVMap_setBool(x_1, x_40, x_41);
lean_ctor_set(x_16, 0, x_42);
return x_16;
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
lean_ctor_set(x_16, 0, x_46);
return x_16;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = l_Bool_HasRepr___closed__2;
x_49 = lean_string_dec_eq(x_13, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Bool_HasRepr___closed__1;
x_51 = lean_string_dec_eq(x_13, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
lean_dec(x_1);
x_52 = l_Lean_setOptionFromString___closed__4;
x_53 = lean_string_append(x_52, x_14);
lean_dec(x_14);
x_54 = l_Char_HasRepr___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_14);
x_58 = lean_box(0);
x_59 = lean_name_mk_string(x_58, x_13);
x_60 = 0;
x_61 = l_Lean_KVMap_setBool(x_1, x_59, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_14);
x_63 = lean_box(0);
x_64 = lean_name_mk_string(x_63, x_13);
x_65 = 1;
x_66 = l_Lean_KVMap_setBool(x_1, x_64, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_47);
return x_67;
}
}
}
case 2:
{
uint8_t x_68; 
lean_dec(x_17);
x_68 = !lean_is_exclusive(x_16);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_70 = lean_box(0);
x_71 = lean_name_mk_string(x_70, x_13);
x_72 = l_String_toName(x_14);
x_73 = l_Lean_KVMap_setName(x_1, x_71, x_72);
lean_ctor_set(x_16, 0, x_73);
return x_16;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_dec(x_16);
x_75 = lean_box(0);
x_76 = lean_name_mk_string(x_75, x_13);
x_77 = l_String_toName(x_14);
x_78 = l_Lean_KVMap_setName(x_1, x_76, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
}
case 3:
{
uint8_t x_80; 
lean_dec(x_17);
x_80 = !lean_is_exclusive(x_16);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_16, 0);
lean_dec(x_81);
x_82 = l_String_isNat(x_14);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_13);
lean_dec(x_1);
x_83 = l_Lean_setOptionFromString___closed__5;
x_84 = lean_string_append(x_83, x_14);
lean_dec(x_14);
x_85 = l_Char_HasRepr___closed__1;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_87);
return x_16;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_box(0);
x_89 = lean_name_mk_string(x_88, x_13);
x_90 = l_String_toNat(x_14);
lean_dec(x_14);
x_91 = l_Lean_KVMap_setNat(x_1, x_89, x_90);
lean_ctor_set(x_16, 0, x_91);
return x_16;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_16, 1);
lean_inc(x_92);
lean_dec(x_16);
x_93 = l_String_isNat(x_14);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_13);
lean_dec(x_1);
x_94 = l_Lean_setOptionFromString___closed__5;
x_95 = lean_string_append(x_94, x_14);
lean_dec(x_14);
x_96 = l_Char_HasRepr___closed__1;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_name_mk_string(x_100, x_13);
x_102 = l_String_toNat(x_14);
lean_dec(x_14);
x_103 = l_Lean_KVMap_setNat(x_1, x_101, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_92);
return x_104;
}
}
}
default: 
{
uint8_t x_105; 
lean_dec(x_17);
x_105 = !lean_is_exclusive(x_16);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_16, 0);
lean_dec(x_106);
lean_inc(x_14);
x_107 = l_String_isInt(x_14);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_13);
lean_dec(x_1);
x_108 = l_Lean_setOptionFromString___closed__6;
x_109 = lean_string_append(x_108, x_14);
lean_dec(x_14);
x_110 = l_Char_HasRepr___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_112);
return x_16;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_box(0);
x_114 = lean_name_mk_string(x_113, x_13);
x_115 = l_String_toInt(x_14);
x_116 = l_Lean_KVMap_setInt(x_1, x_114, x_115);
lean_ctor_set(x_16, 0, x_116);
return x_16;
}
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_16, 1);
lean_inc(x_117);
lean_dec(x_16);
lean_inc(x_14);
x_118 = l_String_isInt(x_14);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_13);
lean_dec(x_1);
x_119 = l_Lean_setOptionFromString___closed__6;
x_120 = lean_string_append(x_119, x_14);
lean_dec(x_14);
x_121 = l_Char_HasRepr___closed__1;
x_122 = lean_string_append(x_120, x_121);
x_123 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_box(0);
x_126 = lean_name_mk_string(x_125, x_13);
x_127 = l_String_toInt(x_14);
x_128 = l_Lean_KVMap_setInt(x_1, x_126, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_117);
return x_129;
}
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_16);
if (x_130 == 0)
{
return x_16;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_16, 0);
x_132 = lean_ctor_get(x_16, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_16);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_134 = l_Lean_setOptionFromString___closed__3;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_3);
return x_135;
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
