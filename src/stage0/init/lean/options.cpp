// Lean compiler output
// Module: init.lean.options
// Imports: init.lean.kvmap init.io init.control.combinators init.data.tostring
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
obj* l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
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
obj* l_Lean_Options_empty;
obj* l_Lean_registerOption___closed__1;
extern obj* l_Bool_HasRepr___closed__2;
obj* l_Lean_setOptionFromString___closed__1;
obj* l_Lean_KVMap_setInt(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_KVMap_setName(obj*, obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerOption(obj*, obj*, obj*);
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
obj* l_Lean_setOptionFromString___closed__4;
uint8 l_String_isInt(obj*);
obj* l_RBMap_find___main___at_Lean_getOptionDecl___spec__1(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_String_trim(obj*);
obj* l_RBMap_find___main___at_Lean_getOptionDecl___spec__1___boxed(obj*, obj*);
obj* l_String_split(obj*, obj*);
obj* l___private_init_lean_options_2__optionDeclsRef;
obj* l_Lean_getOptionDescr(obj*, obj*);
obj* l_Lean_getOptionDecls(obj*);
uint8 l_String_isNat(obj*);
obj* l_String_toName(obj*);
obj* l_Lean_KVMap_setString(obj*, obj*, obj*);
obj* l_Lean_setOptionFromString___closed__3;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_getOptionDefaulValue(obj*, obj*);
obj* l_Lean_registerOption___closed__2;
obj* l_Lean_setOptionFromString(obj*, obj*, obj*);
extern obj* l_IO_RefPointed;
extern obj* l_Bool_HasRepr___closed__1;
obj* l_String_toInt(obj*);
obj* _init_l_Lean_Options_empty() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_Options_HasEmptyc() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Options_empty;
return x_0;
}
}
obj* l___private_init_lean_options_1__initOptionDeclsRef(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::io_mk_ref(x_1, x_0);
return x_2;
}
}
obj* _init_l_Lean_registerOption___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid option declaration '");
return x_0;
}
}
obj* _init_l_Lean_registerOption___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', option already exists");
return x_0;
}
}
obj* l_Lean_registerOption(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l___private_init_lean_options_2__optionDeclsRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_11; 
x_5 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
lean::inc(x_5);
x_11 = l_Lean_NameMap_contains___rarg(x_5, x_0);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_9;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
x_14 = l_RBMap_insert___main___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_0, x_1);
x_15 = lean::io_ref_set(x_3, x_14, x_13);
return x_15;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_5);
lean::dec(x_1);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_0);
x_20 = l_Lean_registerOption___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = l_Lean_registerOption___closed__2;
x_24 = lean::string_append(x_21, x_23);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_25 = x_9;
 lean::cnstr_set_tag(x_9, 1);
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_7);
return x_25;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_4, 0);
x_30 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_32 = x_4;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_4);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_Lean_getOptionDecls(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l___private_init_lean_options_2__optionDeclsRef;
x_2 = lean::io_ref_get(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_getOptionDecl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* _init_l_Lean_getOptionDecl___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unknown option '");
return x_0;
}
}
obj* l_Lean_getOptionDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_lean_options_2__optionDeclsRef;
x_3 = lean::io_ref_get(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_RBMap_find___main___at_Lean_getOptionDecl___spec__1(x_4, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_0);
x_12 = l_Lean_getOptionDecl___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_13, x_15);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_8;
 lean::cnstr_set_tag(x_8, 1);
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_6);
return x_17;
}
else
{
obj* x_19; obj* x_22; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_9, 0);
lean::inc(x_19);
lean::dec(x_9);
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_8;
}
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_6);
return x_22;
}
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_24 = lean::cnstr_get(x_3, 0);
x_26 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_28 = x_3;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_3);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_26);
return x_29;
}
}
}
obj* l_RBMap_find___main___at_Lean_getOptionDecl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_getOptionDecl___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_getOptionDefaulValue(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getOptionDecl(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_16 = x_2;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
}
}
obj* l_Lean_getOptionDescr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getOptionDecl(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_7 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_5);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_16 = x_2;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_2);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
}
}
obj* l_List_map___main___at_Lean_setOptionFromString___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = l_String_trim(x_2);
lean::dec(x_2);
x_9 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
}
obj* _init_l_Lean_setOptionFromString___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("=");
return x_0;
}
}
obj* _init_l_Lean_setOptionFromString___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid configuration option entry, it must be of the form '<key> = <value>'");
return x_0;
}
}
obj* _init_l_Lean_setOptionFromString___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid Bool option value '");
return x_0;
}
}
obj* _init_l_Lean_setOptionFromString___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid Nat option value '");
return x_0;
}
}
obj* _init_l_Lean_setOptionFromString___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid Int option value '");
return x_0;
}
}
obj* l_Lean_setOptionFromString(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = l_Lean_setOptionFromString___closed__1;
x_7 = l_String_split(x_1, x_6);
x_8 = l_List_map___main___at_Lean_setOptionFromString___spec__1(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_0);
x_10 = l_Lean_setOptionFromString___closed__2;
if (lean::is_scalar(x_5)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_3);
return x_11;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_8);
lean::dec(x_0);
x_16 = l_Lean_setOptionFromString___closed__2;
if (lean::is_scalar(x_5)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_3);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_12, 1);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
lean::dec(x_8);
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
lean::dec(x_12);
x_26 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_5;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_3);
lean::inc(x_20);
x_29 = l_String_toName(x_20);
x_30 = l_Lean_getOptionDefaulValue(x_29, x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_31);
x_34 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_36 = x_30;
} else {
 lean::inc(x_34);
 lean::dec(x_30);
 x_36 = lean::box(0);
}
x_37 = lean::box(0);
x_38 = lean_name_mk_string(x_37, x_20);
x_39 = l_Lean_KVMap_setString(x_0, x_38, x_23);
if (lean::is_scalar(x_36)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_36;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_34);
return x_40;
}
case 1:
{
obj* x_42; obj* x_44; obj* x_45; uint8 x_46; 
lean::dec(x_31);
x_42 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_44 = x_30;
} else {
 lean::inc(x_42);
 lean::dec(x_30);
 x_44 = lean::box(0);
}
x_45 = l_Bool_HasRepr___closed__2;
x_46 = lean::string_dec_eq(x_20, x_45);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = l_Bool_HasRepr___closed__1;
x_48 = lean::string_dec_eq(x_20, x_47);
if (x_48 == 0)
{
obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_0);
lean::dec(x_20);
x_51 = l_Lean_setOptionFromString___closed__3;
x_52 = lean::string_append(x_51, x_23);
lean::dec(x_23);
x_54 = l_Char_HasRepr___closed__1;
x_55 = lean::string_append(x_52, x_54);
if (lean::is_scalar(x_44)) {
 x_56 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_56 = x_44;
 lean::cnstr_set_tag(x_44, 1);
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_42);
return x_56;
}
else
{
obj* x_58; obj* x_59; uint8 x_60; obj* x_61; obj* x_62; 
lean::dec(x_23);
x_58 = lean::box(0);
x_59 = lean_name_mk_string(x_58, x_20);
x_60 = 0;
x_61 = l_Lean_KVMap_setBool(x_0, x_59, x_60);
if (lean::is_scalar(x_44)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_44;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_42);
return x_62;
}
}
else
{
obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
lean::dec(x_23);
x_64 = lean::box(0);
x_65 = lean_name_mk_string(x_64, x_20);
x_66 = 1;
x_67 = l_Lean_KVMap_setBool(x_0, x_65, x_66);
if (lean::is_scalar(x_44)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_44;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_42);
return x_68;
}
}
case 2:
{
obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_31);
x_70 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_72 = x_30;
} else {
 lean::inc(x_70);
 lean::dec(x_30);
 x_72 = lean::box(0);
}
x_73 = lean::box(0);
x_74 = lean_name_mk_string(x_73, x_20);
x_75 = l_String_toName(x_23);
x_76 = l_Lean_KVMap_setName(x_0, x_74, x_75);
if (lean::is_scalar(x_72)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_72;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_70);
return x_77;
}
case 3:
{
obj* x_79; obj* x_81; uint8 x_82; 
lean::dec(x_31);
x_79 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_81 = x_30;
} else {
 lean::inc(x_79);
 lean::dec(x_30);
 x_81 = lean::box(0);
}
x_82 = l_String_isNat(x_23);
if (x_82 == 0)
{
obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_0);
lean::dec(x_20);
x_85 = l_Lean_setOptionFromString___closed__4;
x_86 = lean::string_append(x_85, x_23);
lean::dec(x_23);
x_88 = l_Char_HasRepr___closed__1;
x_89 = lean::string_append(x_86, x_88);
if (lean::is_scalar(x_81)) {
 x_90 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_90 = x_81;
 lean::cnstr_set_tag(x_81, 1);
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_79);
return x_90;
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; 
x_91 = lean::box(0);
x_92 = lean_name_mk_string(x_91, x_20);
x_93 = l_String_toNat(x_23);
lean::dec(x_23);
x_95 = l_Lean_KVMap_setNat(x_0, x_92, x_93);
if (lean::is_scalar(x_81)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_81;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_79);
return x_96;
}
}
default:
{
obj* x_98; obj* x_100; uint8 x_102; 
lean::dec(x_31);
x_98 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_set(x_30, 1, lean::box(0));
 x_100 = x_30;
} else {
 lean::inc(x_98);
 lean::dec(x_30);
 x_100 = lean::box(0);
}
lean::inc(x_23);
x_102 = l_String_isInt(x_23);
if (x_102 == 0)
{
obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_0);
lean::dec(x_20);
x_105 = l_Lean_setOptionFromString___closed__5;
x_106 = lean::string_append(x_105, x_23);
lean::dec(x_23);
x_108 = l_Char_HasRepr___closed__1;
x_109 = lean::string_append(x_106, x_108);
if (lean::is_scalar(x_100)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_100;
 lean::cnstr_set_tag(x_100, 1);
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_98);
return x_110;
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_111 = lean::box(0);
x_112 = lean_name_mk_string(x_111, x_20);
x_113 = l_String_toInt(x_23);
x_114 = l_Lean_KVMap_setInt(x_0, x_112, x_113);
if (lean::is_scalar(x_100)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_100;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_98);
return x_115;
}
}
}
}
else
{
obj* x_119; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_0);
lean::dec(x_23);
lean::dec(x_20);
x_119 = lean::cnstr_get(x_30, 0);
x_121 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_123 = x_30;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_30);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_119);
lean::cnstr_set(x_124, 1, x_121);
return x_124;
}
}
else
{
obj* x_129; obj* x_130; 
lean::dec(x_12);
lean::dec(x_18);
lean::dec(x_8);
lean::dec(x_0);
x_129 = l_Lean_setOptionFromString___closed__2;
if (lean::is_scalar(x_5)) {
 x_130 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_130 = x_5;
 lean::cnstr_set_tag(x_5, 1);
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_3);
return x_130;
}
}
}
}
}
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_io(obj*);
obj* initialize_init_control_combinators(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_options(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
w = initialize_init_io(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
 l_Lean_Options_empty = _init_l_Lean_Options_empty();
lean::mark_persistent(l_Lean_Options_empty);
 l_Lean_Options_HasEmptyc = _init_l_Lean_Options_HasEmptyc();
lean::mark_persistent(l_Lean_Options_HasEmptyc);
w = l___private_init_lean_options_1__initOptionDeclsRef(w);
if (io_result_is_error(w)) return w;
 l___private_init_lean_options_2__optionDeclsRef = io_result_get_value(w);
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
