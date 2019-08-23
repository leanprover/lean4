// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap init.system.io init.control.combinators init.data.tostring
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l___private_init_lean_options_1__initOptionDeclsRef(obj*);
obj* l_Lean_setOptionFromString___closed__2;
obj* l_Lean_KVMap_setBool(obj*, obj*, uint8);
obj* l_String_toNat(obj*);
obj* l_Lean_setOptionFromString___closed__5;
obj* l_Lean_Options_HasEmptyc;
obj* l_Lean_KVMap_setNat(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_setOptionFromString___spec__1(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_getOptionDecl___closed__1;
obj* l_Lean_getOptionDecl(obj*, obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Options_empty;
obj* l_Lean_registerOption___closed__1;
extern obj* l_Bool_HasRepr___closed__2;
obj* l_Lean_setOptionFromString___closed__1;
obj* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(obj*, obj*);
obj* l_Lean_KVMap_setInt(obj*, obj*, obj*);
extern "C" obj* lean_string_append(obj*, obj*);
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerOption(obj*, obj*, obj*);
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
obj* l_Lean_setOptionFromString___closed__4;
uint8 l_String_isInt(obj*);
extern "C" uint8 lean_string_dec_eq(obj*, obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_String_trim(obj*);
extern obj* l_System_FilePath_dirName___closed__1;
obj* l_String_split(obj*, obj*);
obj* l___private_init_lean_options_2__optionDeclsRef;
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_getOptionDescr(obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_getOptionDecls(obj*);
uint8 l_String_isNat(obj*);
obj* l_String_toName(obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_setOptionFromString___closed__3;
obj* l_Lean_getOptionDefaulValue(obj*, obj*);
obj* l_Lean_registerOption___closed__2;
obj* l_Lean_setOptionFromString(obj*, obj*, obj*);
extern obj* l_Bool_HasRepr___closed__1;
obj* l_String_toInt(obj*);
obj* _init_l_Lean_Options_empty() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_Options_HasEmptyc() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Options_empty;
return x_1;
}
}
obj* l___private_init_lean_options_1__initOptionDeclsRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_registerOption___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid option declaration '");
return x_1;
}
}
obj* _init_l_Lean_registerOption___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("', option already exists");
return x_1;
}
}
obj* l_Lean_registerOption(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l___private_init_lean_options_2__optionDeclsRef;
x_5 = lean_io_ref_get(x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = l_Lean_NameMap_contains___rarg(x_7, x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::box(0);
lean::cnstr_set(x_5, 0, x_9);
x_10 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_1, x_2);
x_11 = lean_io_ref_set(x_4, x_10, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_7);
lean::dec(x_2);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l_Lean_registerOption___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean::dec(x_13);
x_16 = l_Lean_registerOption___closed__2;
x_17 = lean_string_append(x_15, x_16);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_17);
return x_5;
}
}
else
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::cnstr_get(x_5, 0);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_5);
x_20 = l_Lean_NameMap_contains___rarg(x_18, x_1);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
x_23 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_18, x_1, x_2);
x_24 = lean_io_ref_set(x_4, x_23, x_22);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_18);
lean::dec(x_2);
x_25 = l_System_FilePath_dirName___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_1);
x_27 = l_Lean_registerOption___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean::dec(x_26);
x_29 = l_Lean_registerOption___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_19);
return x_31;
}
}
}
else
{
uint8 x_32; 
lean::dec(x_2);
lean::dec(x_1);
x_32 = !lean::is_exclusive(x_5);
if (x_32 == 0)
{
return x_5;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_5, 0);
x_34 = lean::cnstr_get(x_5, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_5);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
}
}
obj* l_Lean_getOptionDecls(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_lean_options_2__optionDeclsRef;
x_3 = lean_io_ref_get(x_2, x_1);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
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
obj* _init_l_Lean_getOptionDecl___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unknown option '");
return x_1;
}
}
obj* l_Lean_getOptionDecl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_options_2__optionDeclsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_6, x_1);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_System_FilePath_dirName___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l_Lean_getOptionDecl___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean::dec(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean_string_append(x_11, x_12);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_13);
return x_4;
}
else
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_14);
return x_4;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_4, 0);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_4);
x_17 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_15, x_1);
lean::dec(x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = l_System_FilePath_dirName___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = l_Lean_getOptionDecl___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean::dec(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_16);
return x_24;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_16);
return x_26;
}
}
}
else
{
uint8 x_27; 
lean::dec(x_1);
x_27 = !lean::is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_4, 0);
x_29 = lean::cnstr_get(x_4, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_4);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_getOptionDecl___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_getOptionDecl___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_getOptionDefaulValue(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_Lean_getOptionDescr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_getOptionDecl(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_5, 2);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_7, 2);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_List_map___main___at_Lean_setOptionFromString___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_String_trim(x_4);
lean::dec(x_4);
x_7 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = l_String_trim(x_8);
lean::dec(x_8);
x_11 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* _init_l_Lean_setOptionFromString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("=");
return x_1;
}
}
obj* _init_l_Lean_setOptionFromString___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid configuration option entry, it must be of the form '<key> = <value>'");
return x_1;
}
}
obj* _init_l_Lean_setOptionFromString___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid Bool option value '");
return x_1;
}
}
obj* _init_l_Lean_setOptionFromString___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid Nat option value '");
return x_1;
}
}
obj* _init_l_Lean_setOptionFromString___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid Int option value '");
return x_1;
}
}
obj* l_Lean_setOptionFromString(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::dec(x_5);
x_6 = l_Lean_setOptionFromString___closed__1;
x_7 = l_String_split(x_2, x_6);
x_8 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = l_Lean_setOptionFromString___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; 
lean::dec(x_8);
lean::dec(x_1);
x_11 = l_Lean_setOptionFromString___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_15 = lean::box(0);
lean::cnstr_set(x_3, 0, x_15);
lean::inc(x_13);
x_16 = l_String_toName(x_13);
x_17 = l_Lean_getOptionDefaulValue(x_16, x_3);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
switch (lean::obj_tag(x_18)) {
case 0:
{
uint8 x_19; 
lean::dec(x_18);
x_19 = !lean::is_exclusive(x_17);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_17, 0);
lean::dec(x_20);
x_21 = lean::box(0);
x_22 = lean_name_mk_string(x_21, x_13);
x_23 = l_Lean_KVMap_setString(x_1, x_22, x_14);
lean::cnstr_set(x_17, 0, x_23);
return x_17;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_17, 1);
lean::inc(x_24);
lean::dec(x_17);
x_25 = lean::box(0);
x_26 = lean_name_mk_string(x_25, x_13);
x_27 = l_Lean_KVMap_setString(x_1, x_26, x_14);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
}
case 1:
{
uint8 x_29; 
lean::dec(x_18);
x_29 = !lean::is_exclusive(x_17);
if (x_29 == 0)
{
obj* x_30; obj* x_31; uint8 x_32; 
x_30 = lean::cnstr_get(x_17, 0);
lean::dec(x_30);
x_31 = l_Bool_HasRepr___closed__2;
x_32 = lean_string_dec_eq(x_13, x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = l_Bool_HasRepr___closed__1;
x_34 = lean_string_dec_eq(x_13, x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_13);
lean::dec(x_1);
x_35 = l_Lean_setOptionFromString___closed__3;
x_36 = lean_string_append(x_35, x_14);
lean::dec(x_14);
x_37 = l_Char_HasRepr___closed__1;
x_38 = lean_string_append(x_36, x_37);
lean::cnstr_set_tag(x_17, 1);
lean::cnstr_set(x_17, 0, x_38);
return x_17;
}
else
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; 
lean::dec(x_14);
x_39 = lean::box(0);
x_40 = lean_name_mk_string(x_39, x_13);
x_41 = 0;
x_42 = l_Lean_KVMap_setBool(x_1, x_40, x_41);
lean::cnstr_set(x_17, 0, x_42);
return x_17;
}
}
else
{
obj* x_43; obj* x_44; uint8 x_45; obj* x_46; 
lean::dec(x_14);
x_43 = lean::box(0);
x_44 = lean_name_mk_string(x_43, x_13);
x_45 = 1;
x_46 = l_Lean_KVMap_setBool(x_1, x_44, x_45);
lean::cnstr_set(x_17, 0, x_46);
return x_17;
}
}
else
{
obj* x_47; obj* x_48; uint8 x_49; 
x_47 = lean::cnstr_get(x_17, 1);
lean::inc(x_47);
lean::dec(x_17);
x_48 = l_Bool_HasRepr___closed__2;
x_49 = lean_string_dec_eq(x_13, x_48);
if (x_49 == 0)
{
obj* x_50; uint8 x_51; 
x_50 = l_Bool_HasRepr___closed__1;
x_51 = lean_string_dec_eq(x_13, x_50);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_13);
lean::dec(x_1);
x_52 = l_Lean_setOptionFromString___closed__3;
x_53 = lean_string_append(x_52, x_14);
lean::dec(x_14);
x_54 = l_Char_HasRepr___closed__1;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_47);
return x_56;
}
else
{
obj* x_57; obj* x_58; uint8 x_59; obj* x_60; obj* x_61; 
lean::dec(x_14);
x_57 = lean::box(0);
x_58 = lean_name_mk_string(x_57, x_13);
x_59 = 0;
x_60 = l_Lean_KVMap_setBool(x_1, x_58, x_59);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_47);
return x_61;
}
}
else
{
obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
lean::dec(x_14);
x_62 = lean::box(0);
x_63 = lean_name_mk_string(x_62, x_13);
x_64 = 1;
x_65 = l_Lean_KVMap_setBool(x_1, x_63, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_47);
return x_66;
}
}
}
case 2:
{
uint8 x_67; 
lean::dec(x_18);
x_67 = !lean::is_exclusive(x_17);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_17, 0);
lean::dec(x_68);
x_69 = lean::box(0);
x_70 = lean_name_mk_string(x_69, x_13);
x_71 = l_String_toName(x_14);
x_72 = l_Lean_KVMap_setName(x_1, x_70, x_71);
lean::cnstr_set(x_17, 0, x_72);
return x_17;
}
else
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_73 = lean::cnstr_get(x_17, 1);
lean::inc(x_73);
lean::dec(x_17);
x_74 = lean::box(0);
x_75 = lean_name_mk_string(x_74, x_13);
x_76 = l_String_toName(x_14);
x_77 = l_Lean_KVMap_setName(x_1, x_75, x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_73);
return x_78;
}
}
case 3:
{
uint8 x_79; 
lean::dec(x_18);
x_79 = !lean::is_exclusive(x_17);
if (x_79 == 0)
{
obj* x_80; uint8 x_81; 
x_80 = lean::cnstr_get(x_17, 0);
lean::dec(x_80);
x_81 = l_String_isNat(x_14);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_13);
lean::dec(x_1);
x_82 = l_Lean_setOptionFromString___closed__4;
x_83 = lean_string_append(x_82, x_14);
lean::dec(x_14);
x_84 = l_Char_HasRepr___closed__1;
x_85 = lean_string_append(x_83, x_84);
lean::cnstr_set_tag(x_17, 1);
lean::cnstr_set(x_17, 0, x_85);
return x_17;
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_86 = lean::box(0);
x_87 = lean_name_mk_string(x_86, x_13);
x_88 = l_String_toNat(x_14);
lean::dec(x_14);
x_89 = l_Lean_KVMap_setNat(x_1, x_87, x_88);
lean::cnstr_set(x_17, 0, x_89);
return x_17;
}
}
else
{
obj* x_90; uint8 x_91; 
x_90 = lean::cnstr_get(x_17, 1);
lean::inc(x_90);
lean::dec(x_17);
x_91 = l_String_isNat(x_14);
if (x_91 == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_13);
lean::dec(x_1);
x_92 = l_Lean_setOptionFromString___closed__4;
x_93 = lean_string_append(x_92, x_14);
lean::dec(x_14);
x_94 = l_Char_HasRepr___closed__1;
x_95 = lean_string_append(x_93, x_94);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_90);
return x_96;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_97 = lean::box(0);
x_98 = lean_name_mk_string(x_97, x_13);
x_99 = l_String_toNat(x_14);
lean::dec(x_14);
x_100 = l_Lean_KVMap_setNat(x_1, x_98, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_90);
return x_101;
}
}
}
default: 
{
uint8 x_102; 
lean::dec(x_18);
x_102 = !lean::is_exclusive(x_17);
if (x_102 == 0)
{
obj* x_103; uint8 x_104; 
x_103 = lean::cnstr_get(x_17, 0);
lean::dec(x_103);
lean::inc(x_14);
x_104 = l_String_isInt(x_14);
if (x_104 == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_13);
lean::dec(x_1);
x_105 = l_Lean_setOptionFromString___closed__5;
x_106 = lean_string_append(x_105, x_14);
lean::dec(x_14);
x_107 = l_Char_HasRepr___closed__1;
x_108 = lean_string_append(x_106, x_107);
lean::cnstr_set_tag(x_17, 1);
lean::cnstr_set(x_17, 0, x_108);
return x_17;
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_109 = lean::box(0);
x_110 = lean_name_mk_string(x_109, x_13);
x_111 = l_String_toInt(x_14);
x_112 = l_Lean_KVMap_setInt(x_1, x_110, x_111);
lean::cnstr_set(x_17, 0, x_112);
return x_17;
}
}
else
{
obj* x_113; uint8 x_114; 
x_113 = lean::cnstr_get(x_17, 1);
lean::inc(x_113);
lean::dec(x_17);
lean::inc(x_14);
x_114 = l_String_isInt(x_14);
if (x_114 == 0)
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_13);
lean::dec(x_1);
x_115 = l_Lean_setOptionFromString___closed__5;
x_116 = lean_string_append(x_115, x_14);
lean::dec(x_14);
x_117 = l_Char_HasRepr___closed__1;
x_118 = lean_string_append(x_116, x_117);
x_119 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_113);
return x_119;
}
else
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_120 = lean::box(0);
x_121 = lean_name_mk_string(x_120, x_13);
x_122 = l_String_toInt(x_14);
x_123 = l_Lean_KVMap_setInt(x_1, x_121, x_122);
x_124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_113);
return x_124;
}
}
}
}
}
else
{
uint8 x_125; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_1);
x_125 = !lean::is_exclusive(x_17);
if (x_125 == 0)
{
return x_17;
}
else
{
obj* x_126; obj* x_127; obj* x_128; 
x_126 = lean::cnstr_get(x_17, 0);
x_127 = lean::cnstr_get(x_17, 1);
lean::inc(x_127);
lean::inc(x_126);
lean::dec(x_17);
x_128 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_128, 0, x_126);
lean::cnstr_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
obj* x_129; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
x_129 = l_Lean_setOptionFromString___closed__2;
lean::cnstr_set_tag(x_3, 1);
lean::cnstr_set(x_3, 0, x_129);
return x_3;
}
}
}
}
else
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_3, 1);
lean::inc(x_130);
lean::dec(x_3);
x_131 = l_Lean_setOptionFromString___closed__1;
x_132 = l_String_split(x_2, x_131);
x_133 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_132);
if (lean::obj_tag(x_133) == 0)
{
obj* x_134; obj* x_135; 
lean::dec(x_1);
x_134 = l_Lean_setOptionFromString___closed__2;
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_130);
return x_135;
}
else
{
obj* x_136; 
x_136 = lean::cnstr_get(x_133, 1);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_137; obj* x_138; 
lean::dec(x_133);
lean::dec(x_1);
x_137 = l_Lean_setOptionFromString___closed__2;
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_130);
return x_138;
}
else
{
obj* x_139; 
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_140 = lean::cnstr_get(x_133, 0);
lean::inc(x_140);
lean::dec(x_133);
x_141 = lean::cnstr_get(x_136, 0);
lean::inc(x_141);
lean::dec(x_136);
x_142 = lean::box(0);
x_143 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_130);
lean::inc(x_140);
x_144 = l_String_toName(x_140);
x_145 = l_Lean_getOptionDefaulValue(x_144, x_143);
if (lean::obj_tag(x_145) == 0)
{
obj* x_146; 
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
switch (lean::obj_tag(x_146)) {
case 0:
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_146);
x_147 = lean::cnstr_get(x_145, 1);
lean::inc(x_147);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_148 = x_145;
} else {
 lean::dec_ref(x_145);
 x_148 = lean::box(0);
}
x_149 = lean::box(0);
x_150 = lean_name_mk_string(x_149, x_140);
x_151 = l_Lean_KVMap_setString(x_1, x_150, x_141);
if (lean::is_scalar(x_148)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_148;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_147);
return x_152;
}
case 1:
{
obj* x_153; obj* x_154; obj* x_155; uint8 x_156; 
lean::dec(x_146);
x_153 = lean::cnstr_get(x_145, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_154 = x_145;
} else {
 lean::dec_ref(x_145);
 x_154 = lean::box(0);
}
x_155 = l_Bool_HasRepr___closed__2;
x_156 = lean_string_dec_eq(x_140, x_155);
if (x_156 == 0)
{
obj* x_157; uint8 x_158; 
x_157 = l_Bool_HasRepr___closed__1;
x_158 = lean_string_dec_eq(x_140, x_157);
if (x_158 == 0)
{
obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
lean::dec(x_140);
lean::dec(x_1);
x_159 = l_Lean_setOptionFromString___closed__3;
x_160 = lean_string_append(x_159, x_141);
lean::dec(x_141);
x_161 = l_Char_HasRepr___closed__1;
x_162 = lean_string_append(x_160, x_161);
if (lean::is_scalar(x_154)) {
 x_163 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_163 = x_154;
 lean::cnstr_set_tag(x_163, 1);
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_153);
return x_163;
}
else
{
obj* x_164; obj* x_165; uint8 x_166; obj* x_167; obj* x_168; 
lean::dec(x_141);
x_164 = lean::box(0);
x_165 = lean_name_mk_string(x_164, x_140);
x_166 = 0;
x_167 = l_Lean_KVMap_setBool(x_1, x_165, x_166);
if (lean::is_scalar(x_154)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_154;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_153);
return x_168;
}
}
else
{
obj* x_169; obj* x_170; uint8 x_171; obj* x_172; obj* x_173; 
lean::dec(x_141);
x_169 = lean::box(0);
x_170 = lean_name_mk_string(x_169, x_140);
x_171 = 1;
x_172 = l_Lean_KVMap_setBool(x_1, x_170, x_171);
if (lean::is_scalar(x_154)) {
 x_173 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_173 = x_154;
}
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_153);
return x_173;
}
}
case 2:
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
lean::dec(x_146);
x_174 = lean::cnstr_get(x_145, 1);
lean::inc(x_174);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_175 = x_145;
} else {
 lean::dec_ref(x_145);
 x_175 = lean::box(0);
}
x_176 = lean::box(0);
x_177 = lean_name_mk_string(x_176, x_140);
x_178 = l_String_toName(x_141);
x_179 = l_Lean_KVMap_setName(x_1, x_177, x_178);
if (lean::is_scalar(x_175)) {
 x_180 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_180 = x_175;
}
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_180, 1, x_174);
return x_180;
}
case 3:
{
obj* x_181; obj* x_182; uint8 x_183; 
lean::dec(x_146);
x_181 = lean::cnstr_get(x_145, 1);
lean::inc(x_181);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_182 = x_145;
} else {
 lean::dec_ref(x_145);
 x_182 = lean::box(0);
}
x_183 = l_String_isNat(x_141);
if (x_183 == 0)
{
obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
lean::dec(x_140);
lean::dec(x_1);
x_184 = l_Lean_setOptionFromString___closed__4;
x_185 = lean_string_append(x_184, x_141);
lean::dec(x_141);
x_186 = l_Char_HasRepr___closed__1;
x_187 = lean_string_append(x_185, x_186);
if (lean::is_scalar(x_182)) {
 x_188 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_188 = x_182;
 lean::cnstr_set_tag(x_188, 1);
}
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_181);
return x_188;
}
else
{
obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_189 = lean::box(0);
x_190 = lean_name_mk_string(x_189, x_140);
x_191 = l_String_toNat(x_141);
lean::dec(x_141);
x_192 = l_Lean_KVMap_setNat(x_1, x_190, x_191);
if (lean::is_scalar(x_182)) {
 x_193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_193 = x_182;
}
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_181);
return x_193;
}
}
default: 
{
obj* x_194; obj* x_195; uint8 x_196; 
lean::dec(x_146);
x_194 = lean::cnstr_get(x_145, 1);
lean::inc(x_194);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_195 = x_145;
} else {
 lean::dec_ref(x_145);
 x_195 = lean::box(0);
}
lean::inc(x_141);
x_196 = l_String_isInt(x_141);
if (x_196 == 0)
{
obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
lean::dec(x_140);
lean::dec(x_1);
x_197 = l_Lean_setOptionFromString___closed__5;
x_198 = lean_string_append(x_197, x_141);
lean::dec(x_141);
x_199 = l_Char_HasRepr___closed__1;
x_200 = lean_string_append(x_198, x_199);
if (lean::is_scalar(x_195)) {
 x_201 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_201 = x_195;
 lean::cnstr_set_tag(x_201, 1);
}
lean::cnstr_set(x_201, 0, x_200);
lean::cnstr_set(x_201, 1, x_194);
return x_201;
}
else
{
obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; 
x_202 = lean::box(0);
x_203 = lean_name_mk_string(x_202, x_140);
x_204 = l_String_toInt(x_141);
x_205 = l_Lean_KVMap_setInt(x_1, x_203, x_204);
if (lean::is_scalar(x_195)) {
 x_206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_206 = x_195;
}
lean::cnstr_set(x_206, 0, x_205);
lean::cnstr_set(x_206, 1, x_194);
return x_206;
}
}
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_141);
lean::dec(x_140);
lean::dec(x_1);
x_207 = lean::cnstr_get(x_145, 0);
lean::inc(x_207);
x_208 = lean::cnstr_get(x_145, 1);
lean::inc(x_208);
if (lean::is_exclusive(x_145)) {
 lean::cnstr_release(x_145, 0);
 lean::cnstr_release(x_145, 1);
 x_209 = x_145;
} else {
 lean::dec_ref(x_145);
 x_209 = lean::box(0);
}
if (lean::is_scalar(x_209)) {
 x_210 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_210 = x_209;
}
lean::cnstr_set(x_210, 0, x_207);
lean::cnstr_set(x_210, 1, x_208);
return x_210;
}
}
else
{
obj* x_211; obj* x_212; 
lean::dec(x_139);
lean::dec(x_136);
lean::dec(x_133);
lean::dec(x_1);
x_211 = l_Lean_setOptionFromString___closed__2;
x_212 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_212, 0, x_211);
lean::cnstr_set(x_212, 1, x_130);
return x_212;
}
}
}
}
}
}
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_system_io(obj*);
obj* initialize_init_control_combinators(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_options(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_system_io(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean::mark_persistent(l_Lean_Options_empty);
l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean::mark_persistent(l_Lean_Options_HasEmptyc);
w = l___private_init_lean_options_1__initOptionDeclsRef(w);
if (lean::io_result_is_error(w)) return w;
l___private_init_lean_options_2__optionDeclsRef = lean::io_result_get_value(w);
lean::mark_persistent(l___private_init_lean_options_2__optionDeclsRef);
l_Lean_registerOption___closed__1 = _init_l_Lean_registerOption___closed__1();
lean::mark_persistent(l_Lean_registerOption___closed__1);
l_Lean_registerOption___closed__2 = _init_l_Lean_registerOption___closed__2();
lean::mark_persistent(l_Lean_registerOption___closed__2);
l_Lean_getOptionDecl___closed__1 = _init_l_Lean_getOptionDecl___closed__1();
lean::mark_persistent(l_Lean_getOptionDecl___closed__1);
l_Lean_setOptionFromString___closed__1 = _init_l_Lean_setOptionFromString___closed__1();
lean::mark_persistent(l_Lean_setOptionFromString___closed__1);
l_Lean_setOptionFromString___closed__2 = _init_l_Lean_setOptionFromString___closed__2();
lean::mark_persistent(l_Lean_setOptionFromString___closed__2);
l_Lean_setOptionFromString___closed__3 = _init_l_Lean_setOptionFromString___closed__3();
lean::mark_persistent(l_Lean_setOptionFromString___closed__3);
l_Lean_setOptionFromString___closed__4 = _init_l_Lean_setOptionFromString___closed__4();
lean::mark_persistent(l_Lean_setOptionFromString___closed__4);
l_Lean_setOptionFromString___closed__5 = _init_l_Lean_setOptionFromString___closed__5();
lean::mark_persistent(l_Lean_setOptionFromString___closed__5);
return w;
}
