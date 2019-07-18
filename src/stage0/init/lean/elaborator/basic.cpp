// Lean compiler output
// Module: init.lean.elaborator.basic
// Imports: init.lean.namegenerator init.lean.parser.module
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
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Elab_runIO___rarg(obj*);
obj* l_Lean_Elab_runIOUnsafe(obj*);
obj* l_Lean_Elab_runIOUnsafe___rarg(obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__5;
extern obj* l_Lean_AttributeImpl_inhabited___closed__5;
obj* l_Lean_Elab_runIO(obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1(obj*, obj*, obj*, uint8, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
obj* l_Lean_registerBuiltinTermElabAttr___closed__7;
obj* l_Lean_registerBuiltinTermElabAttr___closed__4;
obj* l_Lean_registerAttribute(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
extern obj* l_Lean_mkInitAttr___lambda__1___closed__1;
extern obj* l_Lean_AttributeImpl_inhabited___closed__4;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1;
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2;
obj* l_Lean_Elab_runIO___boxed(obj*, obj*);
obj* l_Lean_mkBuiltinCommandElabTable(obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6;
obj* l_Lean_registerBuiltinTermElabAttr(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__6;
obj* l_Lean_ElabException_Inhabited;
obj* l_mkHashMap___at_Lean_mkBuiltinCommandElabTable___spec__2(obj*);
obj* l_Lean_mkBuiltinTermElabTable(obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7;
obj* l_Lean_ElabException_Inhabited___closed__1;
obj* l_mkHashMap___at_Lean_mkBuiltinTermElabTable___spec__2(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
obj* l_Lean_ElabException_Inhabited___closed__2;
obj* l_Lean_registerTagAttribute___lambda__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
obj* l_Lean_ConstantInfo_type(obj*);
namespace lean {
obj* environment_find_core(obj*, obj*);
}
obj* l_Lean_registerBuiltinTermElabAttr___closed__2;
extern obj* l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
obj* l_Lean_declareBuiltinTermElab___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_declareBuiltinTermElab(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_registerBuiltinTermElabAttr___closed__1;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1;
obj* l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1;
obj* l_Lean_builtinCommandElabTable;
extern obj* l_Lean_nameToExprAux___main___closed__4;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_registerBuiltinTermElabAttr___closed__3;
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_builtinTermElabTable;
obj* l_Lean_registerTagAttribute___lambda__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _init_l_Lean_ElabException_Inhabited___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("error");
return x_1;
}
}
obj* _init_l_Lean_ElabException_Inhabited___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_ElabException_Inhabited___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_ElabException_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_Lean_ElabException_Inhabited___closed__2;
return x_1;
}
}
obj* l_mkHashMap___at_Lean_mkBuiltinTermElabTable___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1() {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2;
return x_1;
}
}
obj* l_Lean_mkBuiltinTermElabTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_mkHashMap___at_Lean_mkBuiltinCommandElabTable___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2() {
_start:
{
obj* x_1; uint8 x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = 1;
x_3 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set_scalar(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
obj* _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1() {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2;
return x_1;
}
}
obj* l_Lean_mkBuiltinCommandElabTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1;
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* l_Lean_declareBuiltinTermElab(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 0);
lean::dec(x_6);
lean::cnstr_set(x_4, 0, x_1);
return x_4;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
}
obj* l_Lean_declareBuiltinTermElab___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_declareBuiltinTermElab(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("invalid attribute 'builtinTermElab', must be persistent");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("unexpected term elaborator type at '");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' `TermElab` expected");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("TermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("kind");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
_start:
{
if (x_4 == 0)
{
uint8 x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
lean::dec(x_7);
x_8 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1;
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_5);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 0);
lean::dec(x_14);
x_15 = lean::box(0);
lean::inc(x_13);
lean::cnstr_set(x_5, 0, x_15);
lean::inc(x_2);
lean::inc(x_1);
x_16 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_17 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_20 = l_Lean_ConstantInfo_type(x_19);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 4)
{
obj* x_21; obj* x_22; uint8 x_23; 
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_23 = lean_name_dec_eq(x_21, x_22);
lean::dec(x_21);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_5);
lean::dec(x_1);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_2);
x_26 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_27 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_28 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_29 = lean::string_append(x_27, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_13);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_13);
x_31 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7;
x_32 = l_Lean_declareBuiltinTermElab(x_1, x_31, x_2, x_5);
lean::dec(x_2);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_20);
lean::dec(x_5);
lean::dec(x_1);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_2);
x_35 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_36 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_37 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_38 = lean::string_append(x_36, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_13);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_40 = lean::cnstr_get(x_5, 1);
lean::inc(x_40);
lean::dec(x_5);
x_41 = lean::box(0);
lean::inc(x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
lean::inc(x_2);
lean::inc(x_1);
x_43 = lean::environment_find_core(x_1, x_2);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_42);
lean::dec(x_2);
lean::dec(x_1);
x_44 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
return x_45;
}
else
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
lean::dec(x_43);
x_47 = l_Lean_ConstantInfo_type(x_46);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 4)
{
obj* x_48; obj* x_49; uint8 x_50; 
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
lean::dec(x_47);
x_49 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_50 = lean_name_dec_eq(x_48, x_49);
lean::dec(x_48);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_42);
lean::dec(x_1);
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_2);
x_53 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_55 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_56 = lean::string_append(x_54, x_55);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_40);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_40);
x_58 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7;
x_59 = l_Lean_declareBuiltinTermElab(x_1, x_58, x_2, x_42);
lean::dec(x_2);
return x_59;
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_47);
lean::dec(x_42);
lean::dec(x_1);
x_60 = l_Lean_Name_toString___closed__1;
x_61 = l_Lean_Name_toStringWithSep___main(x_60, x_2);
x_62 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_63 = lean::string_append(x_62, x_61);
lean::dec(x_61);
x_64 = l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_65 = lean::string_append(x_63, x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_40);
return x_66;
}
}
}
}
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("builtinTermElab");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerTagAttribute___lambda__7___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Builtin term elaborator");
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
obj* _init_l_Lean_registerBuiltinTermElabAttr___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_1 = l_Lean_registerBuiltinTermElabAttr___closed__2;
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinTermElabAttr___closed__6;
x_4 = l_Lean_registerBuiltinTermElabAttr___closed__3;
x_5 = l_Lean_registerBuiltinTermElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean::alloc_cnstr(0, 8, 1);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_4);
lean::cnstr_set(x_9, 4, x_5);
lean::cnstr_set(x_9, 5, x_6);
lean::cnstr_set(x_9, 6, x_7);
lean::cnstr_set(x_9, 7, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
obj* l_Lean_registerBuiltinTermElabAttr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_registerBuiltinTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
obj* l_Lean_registerBuiltinTermElabAttr___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = l_Lean_registerBuiltinTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Elab_runIOUnsafe___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_runBuiltinParserUnsafe___closed__2;
x_4 = lean::apply_1(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::cnstr_get(x_2, 0);
lean::dec(x_7);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
else
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_2, 0);
lean::dec(x_12);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set_tag(x_2, 1);
lean::cnstr_set(x_2, 0, x_13);
return x_2;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_10);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
}
}
}
obj* l_Lean_Elab_runIOUnsafe(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_runIOUnsafe___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Elab_runIO___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::dec(x_3);
x_4 = l_Lean_ElabException_Inhabited___closed__2;
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_ElabException_Inhabited___closed__2;
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}
obj* l_Lean_Elab_runIO(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Elab_runIO___rarg), 1, 0);
return x_3;
}
}
obj* l_Lean_Elab_runIO___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Elab_runIO(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* initialize_init_lean_namegenerator(obj*);
obj* initialize_init_lean_parser_module(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_elaborator_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_namegenerator(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_module(w);
if (io_result_is_error(w)) return w;
l_Lean_ElabException_Inhabited___closed__1 = _init_l_Lean_ElabException_Inhabited___closed__1();
lean::mark_persistent(l_Lean_ElabException_Inhabited___closed__1);
l_Lean_ElabException_Inhabited___closed__2 = _init_l_Lean_ElabException_Inhabited___closed__2();
lean::mark_persistent(l_Lean_ElabException_Inhabited___closed__2);
l_Lean_ElabException_Inhabited = _init_l_Lean_ElabException_Inhabited();
lean::mark_persistent(l_Lean_ElabException_Inhabited);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "ElabException"), "Inhabited"), l_Lean_ElabException_Inhabited);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinTermElabTable___spec__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkBuiltinTermElabTable"), 1, l_Lean_mkBuiltinTermElabTable);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1();
lean::mark_persistent(l_Lean_SMap_empty___at_Lean_mkBuiltinCommandElabTable___spec__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkBuiltinCommandElabTable"), 1, l_Lean_mkBuiltinCommandElabTable);
w = l_Lean_mkBuiltinTermElabTable(w);
if (io_result_is_error(w)) return w;
l_Lean_builtinTermElabTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_builtinTermElabTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "builtinTermElabTable"), l_Lean_builtinTermElabTable);
w = l_Lean_mkBuiltinCommandElabTable(w);
if (io_result_is_error(w)) return w;
l_Lean_builtinCommandElabTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_builtinCommandElabTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "builtinCommandElabTable"), l_Lean_builtinCommandElabTable);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "declareBuiltinTermElab"), 4, l_Lean_declareBuiltinTermElab___boxed);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__1);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__2);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__3);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__4);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__5);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__6);
l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7 = _init_l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___lambda__1___closed__7);
l_Lean_registerBuiltinTermElabAttr___closed__1 = _init_l_Lean_registerBuiltinTermElabAttr___closed__1();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__1);
l_Lean_registerBuiltinTermElabAttr___closed__2 = _init_l_Lean_registerBuiltinTermElabAttr___closed__2();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__2);
l_Lean_registerBuiltinTermElabAttr___closed__3 = _init_l_Lean_registerBuiltinTermElabAttr___closed__3();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__3);
l_Lean_registerBuiltinTermElabAttr___closed__4 = _init_l_Lean_registerBuiltinTermElabAttr___closed__4();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__4);
l_Lean_registerBuiltinTermElabAttr___closed__5 = _init_l_Lean_registerBuiltinTermElabAttr___closed__5();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__5);
l_Lean_registerBuiltinTermElabAttr___closed__6 = _init_l_Lean_registerBuiltinTermElabAttr___closed__6();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__6);
l_Lean_registerBuiltinTermElabAttr___closed__7 = _init_l_Lean_registerBuiltinTermElabAttr___closed__7();
lean::mark_persistent(l_Lean_registerBuiltinTermElabAttr___closed__7);
w = l_Lean_registerBuiltinTermElabAttr(w);
if (io_result_is_error(w)) return w;
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Elab"), "runIOUnsafe"), 1, l_Lean_Elab_runIOUnsafe);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Elab"), "runIO"), 2, l_Lean_Elab_runIO___boxed);
return w;
}
