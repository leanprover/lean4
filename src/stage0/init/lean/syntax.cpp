// Lean compiler output
// Module: init.lean.syntax
// Imports: init.lean.name init.lean.format init.data.array.default
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
obj* l_Lean_mkChoiceKind(obj*);
obj* l_Lean_SyntaxNodeKind_fix___main(obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_mkManyKind(obj*);
obj* l_Lean_Syntax_getHeadInfo___boxed(obj*);
obj* l_Lean_Syntax_replace(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Syntax_reprint___main___boxed(obj*);
obj* l_Lean_Syntax_flipScopes___rarg(obj*);
obj* l_Lean_mkNullKind(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_stxInh;
obj* l_Lean_mkHoleKind___closed__1;
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_replace___spec__1(obj*, obj*);
obj* l_Lean_mkHoleKind(obj*);
namespace lean {
obj* mk_syntax_atom_core(obj*);
}
extern obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Syntax_formatStx___main___closed__5;
obj* l_Lean_Syntax_isOfKind___boxed(obj*, obj*);
obj* l_Lean_withArgs___rarg(obj*, obj*);
obj* l_Lean_Syntax_toSyntaxNode(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(obj*, obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_fixKinds___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_mkManyKind___closed__1;
obj* l___private_init_lean_syntax_3__reprintLeaf___main___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf(obj*, obj*);
obj* l_Lean_Syntax_replace___boxed(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_toSyntaxNode___spec__1(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
uint8 l_Lean_stxKindBeq(obj*, obj*);
obj* l_Lean_Syntax_formatStx___main(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(obj*, obj*);
uint8 l_Lean_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_Syntax_updateTrailing(obj*, obj*);
obj* l_Lean_updateArgs(obj*, obj*);
obj* l_Lean_Syntax_fixKinds(obj*, obj*);
obj* l_Lean_MacroScopes_flip(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l___private_init_lean_syntax_2__updateLeadingAux___main(obj*, obj*);
obj* l_Lean_nameToKindTable;
obj* l_Lean_Syntax_updateTrailing___main(obj*, obj*);
obj* l_Lean_stxKindInh;
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_isIdent___main___boxed(obj*);
obj* l_Lean_Syntax_isMissing___main___boxed(obj*);
obj* l_Lean_Syntax_reprint___boxed(obj*);
obj* l_Lean_Syntax_formatStx___main___closed__2;
obj* l_Lean_nextKind___closed__1;
obj* l_Lean_Syntax_flipScopes___main(obj*);
obj* l_Lean_Syntax_HasToString;
obj* l_Lean_Syntax_formatStx___main___closed__4;
obj* l_Lean_SyntaxNodeKind_fix(obj*, obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_join___closed__1;
obj* l_Lean_nextKind___closed__2;
obj* l_Lean_nextUniqId;
obj* l_Lean_SourceInfo_updateTrailing(obj*, obj*);
obj* l___private_init_lean_syntax_1__updateInfo___main(obj*, obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Lean_Syntax_replace___rarg(obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_manyKind;
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Syntax_isMissing___boxed(obj*);
obj* l_Lean_Syntax_mreplace___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main___closed__1;
obj* l_Lean_Syntax_mreplace___boxed(obj*);
obj* l_Lean_unreachIsNodeIdent___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkChoiceKind___closed__1;
obj* l_Lean_MacroScope_DecidableEq;
obj* l_Lean_stxKindBeq___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(obj*);
obj* l_Lean_Syntax_fixKinds___main(obj*, obj*);
obj* l_Lean_Syntax_getPos___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_Lean_HasFormat;
obj* l_Lean_mkNullKind___closed__1;
obj* l_Lean_SyntaxNodeKind_fix___main___closed__1;
obj* l_Lean_Syntax_formatStx(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_mkOptionSomeKind(obj*);
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_2__updateLeadingAux(obj*, obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(obj*, obj*);
uint8 l_Lean_Syntax_isOfKind(obj*, obj*);
obj* l_Lean_Syntax_getHeadInfo___main(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_mkOptionSomeKind___closed__1;
obj* l_Lean_Syntax_formatStx___main___closed__1;
uint8 l_Lean_Syntax_isIdent___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_nextKind(obj*, obj*);
obj* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeAtom(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__2(obj*, obj*, obj*, obj*);
uint8 l_Lean_Syntax_isMissing___main(obj*);
obj* l_List_append___rarg(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___closed__3;
obj* l_Lean_natHasFormat(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_nullKind;
uint8 l_Lean_NameMap_contains___rarg(obj*, obj*);
obj* l_Lean_choiceKind;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(obj*);
obj* l_Lean_Syntax_reprint(obj*);
obj* l_Lean_Syntax_getHeadInfo(obj*);
obj* l_Lean_Syntax_mreplace___rarg(obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeMissing(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_HasRepr___lambda__1(obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_mkOptionNoneKind___closed__1;
uint8 l_Lean_Syntax_isIdent(obj*);
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(obj*, obj*);
obj* l_Lean_Syntax_updateLeading(obj*);
obj* l_Lean_mkOptionNoneKind(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2___boxed(obj*, obj*);
obj* l_Lean_optionNoneKind;
obj* l___private_init_lean_syntax_1__updateInfo(obj*, obj*);
obj* l_Lean_Syntax_flipScopes(obj*);
obj* l_Lean_optionSomeKind;
obj* l_Lean_Syntax_reprint___main___closed__2;
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__3;
obj* l_Lean_MacroScope_Lean_HasFormat;
extern obj* l_Lean_formatKVMap___closed__1;
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_mkNameToKindTable(obj*);
obj* l_Lean_Syntax_flipScopes___boxed(obj*);
obj* l_Lean_Syntax_getPos(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
namespace lean {
obj* mk_syntax_list_core(obj*);
}
obj* l___private_init_lean_syntax_3__reprintLeaf___boxed(obj*, obj*);
obj* l_Lean_mkUniqIdRef(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeAtom___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_formatDataValue___main___closed__3;
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___boxed(obj*);
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
obj* l_Lean_Syntax_isOfKind___main___boxed(obj*, obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_Lean_Syntax_mreplace___main___boxed(obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf___main(obj*, obj*);
obj* l_Lean_MacroScopes_flip___main(obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___closed__6;
obj* l_String_quote(obj*);
obj* l_Lean_Syntax_mreplace(obj*);
obj* l_Lean_Syntax_mreplace___main(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_withArgs(obj*);
obj* l_Lean_MacroScopes_flip___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_replace___spec__2(obj*, obj*, obj*);
obj* l_Lean_Syntax_toSyntaxNode___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_isIdent___boxed(obj*);
obj* l_Lean_Syntax_getHeadInfo___main___boxed(obj*);
obj* l_Lean_SourceInfo_updateTrailing___main(obj*, obj*);
namespace lean {
obj* mk_syntax_ident_core(obj*);
}
obj* l_Lean_Syntax_toSyntaxNode___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeIdent(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Syntax_isMissing(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_MacroScopes_flip___main___boxed(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* _init_l_Lean_MacroScope_DecidableEq() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_MacroScope_Lean_HasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_natHasFormat), 1, 0);
return x_1;
}
}
obj* l_Lean_SourceInfo_updateTrailing___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 2);
lean::dec(x_4);
lean::cnstr_set(x_1, 2, x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_2);
return x_7;
}
}
}
obj* l_Lean_SourceInfo_updateTrailing(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SourceInfo_updateTrailing___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkUniqIdRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_stxKindInh() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
uint8 l_Lean_stxKindBeq(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::nat_dec_eq(x_3, x_4);
return x_5;
}
}
obj* l_Lean_stxKindBeq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_stxKindBeq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_mkNameToKindTable(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::io_mk_ref(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_nextKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("kind '");
return x_1;
}
}
obj* _init_l_Lean_nextKind___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' already exists");
return x_1;
}
}
obj* l_Lean_nextKind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_nameToKindTable;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_Lean_NameMap_contains___rarg(x_6, x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::box(0);
lean::cnstr_set(x_4, 0, x_8);
x_9 = l_Lean_nextUniqId;
x_10 = lean::io_ref_get(x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_10, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::inc(x_12);
lean::inc(x_1);
x_13 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_1, x_12);
x_14 = lean::io_ref_set(x_3, x_13, x_10);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_14, 0);
lean::dec(x_16);
lean::cnstr_set(x_14, 0, x_8);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_12, x_17);
x_19 = lean::io_ref_set(x_9, x_18, x_14);
if (lean::obj_tag(x_19) == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_19, 0);
lean::dec(x_21);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_12);
lean::cnstr_set(x_19, 0, x_22);
return x_19;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_19, 1);
lean::inc(x_23);
lean::dec(x_19);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_1);
lean::cnstr_set(x_24, 1, x_12);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8 x_26; 
lean::dec(x_12);
lean::dec(x_1);
x_26 = !lean::is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_19, 0);
x_28 = lean::cnstr_get(x_19, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_19);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_14, 1);
lean::inc(x_30);
lean::dec(x_14);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_add(x_12, x_32);
x_34 = lean::io_ref_set(x_9, x_33, x_31);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_36 = x_34;
} else {
 lean::dec_ref(x_34);
 x_36 = lean::box(0);
}
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_12);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_12);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_34, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_34, 1);
lean::inc(x_40);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_41 = x_34;
} else {
 lean::dec_ref(x_34);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8 x_43; 
lean::dec(x_12);
lean::dec(x_1);
x_43 = !lean::is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = lean::cnstr_get(x_14, 0);
x_45 = lean::cnstr_get(x_14, 1);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_14);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_10, 0);
x_48 = lean::cnstr_get(x_10, 1);
lean::inc(x_48);
lean::inc(x_47);
lean::dec(x_10);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_8);
lean::cnstr_set(x_49, 1, x_48);
lean::inc(x_47);
lean::inc(x_1);
x_50 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_1, x_47);
x_51 = lean::io_ref_set(x_3, x_50, x_49);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_51, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_53 = x_51;
} else {
 lean::dec_ref(x_51);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_8);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::mk_nat_obj(1u);
x_56 = lean::nat_add(x_47, x_55);
x_57 = lean::io_ref_set(x_9, x_56, x_54);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_57, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_59 = x_57;
} else {
 lean::dec_ref(x_57);
 x_59 = lean::box(0);
}
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_1);
lean::cnstr_set(x_60, 1, x_47);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_47);
lean::dec(x_1);
x_62 = lean::cnstr_get(x_57, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_57, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_64 = x_57;
} else {
 lean::dec_ref(x_57);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_47);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_51, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_51, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_68 = x_51;
} else {
 lean::dec_ref(x_51);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
uint8 x_70; 
lean::dec(x_6);
lean::dec(x_1);
x_70 = !lean::is_exclusive(x_10);
if (x_70 == 0)
{
return x_10;
}
else
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_10, 0);
x_72 = lean::cnstr_get(x_10, 1);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_10);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_6);
x_74 = l_Lean_Name_toString___closed__1;
x_75 = l_Lean_Name_toStringWithSep___main(x_74, x_1);
x_76 = l_Lean_nextKind___closed__1;
x_77 = lean::string_append(x_76, x_75);
lean::dec(x_75);
x_78 = l_Lean_nextKind___closed__2;
x_79 = lean::string_append(x_77, x_78);
lean::cnstr_set_tag(x_4, 1);
lean::cnstr_set(x_4, 0, x_79);
return x_4;
}
}
else
{
obj* x_80; obj* x_81; uint8 x_82; 
x_80 = lean::cnstr_get(x_4, 0);
x_81 = lean::cnstr_get(x_4, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_4);
x_82 = l_Lean_NameMap_contains___rarg(x_80, x_1);
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_83 = lean::box(0);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
x_85 = l_Lean_nextUniqId;
x_86 = lean::io_ref_get(x_85, x_84);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_83);
lean::cnstr_set(x_90, 1, x_88);
lean::inc(x_87);
lean::inc(x_1);
x_91 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_80, x_1, x_87);
x_92 = lean::io_ref_set(x_3, x_91, x_90);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_94 = x_92;
} else {
 lean::dec_ref(x_92);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_83);
lean::cnstr_set(x_95, 1, x_93);
x_96 = lean::mk_nat_obj(1u);
x_97 = lean::nat_add(x_87, x_96);
x_98 = lean::io_ref_set(x_85, x_97, x_95);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_100 = x_98;
} else {
 lean::dec_ref(x_98);
 x_100 = lean::box(0);
}
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_1);
lean::cnstr_set(x_101, 1, x_87);
if (lean::is_scalar(x_100)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_100;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_99);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_87);
lean::dec(x_1);
x_103 = lean::cnstr_get(x_98, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_98, 1);
lean::inc(x_104);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_105 = x_98;
} else {
 lean::dec_ref(x_98);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_104);
return x_106;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_87);
lean::dec(x_1);
x_107 = lean::cnstr_get(x_92, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get(x_92, 1);
lean::inc(x_108);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_109 = x_92;
} else {
 lean::dec_ref(x_92);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_108);
return x_110;
}
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_80);
lean::dec(x_1);
x_111 = lean::cnstr_get(x_86, 0);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_86, 1);
lean::inc(x_112);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_113 = x_86;
} else {
 lean::dec_ref(x_86);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
lean::cnstr_set(x_114, 1, x_112);
return x_114;
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_80);
x_115 = l_Lean_Name_toString___closed__1;
x_116 = l_Lean_Name_toStringWithSep___main(x_115, x_1);
x_117 = l_Lean_nextKind___closed__1;
x_118 = lean::string_append(x_117, x_116);
lean::dec(x_116);
x_119 = l_Lean_nextKind___closed__2;
x_120 = lean::string_append(x_118, x_119);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_81);
return x_121;
}
}
}
else
{
uint8 x_122; 
lean::dec(x_1);
x_122 = !lean::is_exclusive(x_4);
if (x_122 == 0)
{
return x_4;
}
else
{
obj* x_123; obj* x_124; obj* x_125; 
x_123 = lean::cnstr_get(x_4, 0);
x_124 = lean::cnstr_get(x_4, 1);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_4);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_123);
lean::cnstr_set(x_125, 1, x_124);
return x_125;
}
}
}
}
obj* _init_l_Lean_mkNullKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("null");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkNullKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkNullKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkChoiceKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("choice");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkChoiceKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkChoiceKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkOptionSomeKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("some");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkOptionSomeKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkOptionSomeKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkOptionNoneKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("none");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkOptionNoneKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkOptionNoneKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkManyKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("many");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkManyKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkManyKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_mkHoleKind___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("hole");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkHoleKind(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_mkHoleKind___closed__1;
x_3 = l_Lean_nextKind(x_2, x_1);
return x_3;
}
}
obj* _init_l_Lean_stxInh() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
uint8 l_Lean_Syntax_isMissing___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Lean_Syntax_isMissing___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isMissing___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Syntax_isMissing(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Syntax_isMissing___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isMissing___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isMissing(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(obj* x_1, obj* x_2) {
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
obj* _init_l_Lean_SyntaxNodeKind_fix___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Error unknown Syntax kind '");
return x_1;
}
}
obj* l_Lean_SyntaxNodeKind_fix___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
lean::dec(x_5);
x_6 = l_Lean_nameToKindTable;
x_7 = lean::io_ref_get(x_6, x_2);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(x_9, x_4);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::free_heap_obj(x_1);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_4);
x_13 = l_Lean_SyntaxNodeKind_fix___main___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_15 = l_Char_HasRepr___closed__1;
x_16 = lean::string_append(x_14, x_15);
lean::cnstr_set_tag(x_7, 1);
lean::cnstr_set(x_7, 0, x_16);
return x_7;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
lean::cnstr_set(x_1, 1, x_17);
lean::cnstr_set(x_7, 0, x_1);
return x_7;
}
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_7, 0);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_7);
x_20 = l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(x_18, x_4);
lean::dec(x_18);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::free_heap_obj(x_1);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_4);
x_23 = l_Lean_SyntaxNodeKind_fix___main___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_25 = l_Char_HasRepr___closed__1;
x_26 = lean::string_append(x_24, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_19);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
lean::cnstr_set(x_1, 1, x_28);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_19);
return x_29;
}
}
}
else
{
uint8 x_30; 
lean::free_heap_obj(x_1);
lean::dec(x_4);
x_30 = !lean::is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_7, 0);
x_32 = lean::cnstr_get(x_7, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_7);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
lean::dec(x_1);
x_35 = l_Lean_nameToKindTable;
x_36 = lean::io_ref_get(x_35, x_2);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_39 = x_36;
} else {
 lean::dec_ref(x_36);
 x_39 = lean::box(0);
}
x_40 = l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(x_37, x_34);
lean::dec(x_37);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_41 = l_Lean_Name_toString___closed__1;
x_42 = l_Lean_Name_toStringWithSep___main(x_41, x_34);
x_43 = l_Lean_SyntaxNodeKind_fix___main___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_45 = l_Char_HasRepr___closed__1;
x_46 = lean::string_append(x_44, x_45);
if (lean::is_scalar(x_39)) {
 x_47 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_47 = x_39;
 lean::cnstr_set_tag(x_47, 1);
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_38);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_34);
lean::cnstr_set(x_49, 1, x_48);
if (lean::is_scalar(x_39)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_39;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_38);
return x_50;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_34);
x_51 = lean::cnstr_get(x_36, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_36, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_53 = x_36;
} else {
 lean::dec_ref(x_36);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
return x_54;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_SyntaxNodeKind_fix___main___spec__1(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SyntaxNodeKind_fix(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SyntaxNodeKind_fix___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_fixKinds___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 0);
lean::dec(x_7);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
lean::cnstr_set(x_3, 0, x_9);
return x_3;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_11 = l_Array_empty___closed__1;
x_12 = x_2;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::array_fget(x_2, x_1);
x_15 = lean::box(0);
lean::inc(x_14);
x_16 = x_15;
x_17 = lean::array_fset(x_2, x_1, x_16);
lean::inc(x_14);
x_18 = l_Lean_Syntax_fixKinds___main(x_14, x_3);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_18, 0);
lean::cnstr_set(x_18, 0, x_15);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_1, x_21);
x_23 = x_20;
x_24 = lean::array_fset(x_17, x_1, x_23);
lean::dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_3 = x_18;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_18, 0);
x_27 = lean::cnstr_get(x_18, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_18);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_1, x_29);
x_31 = x_26;
x_32 = lean::array_fset(x_17, x_1, x_31);
lean::dec(x_1);
x_1 = x_30;
x_2 = x_32;
x_3 = x_28;
goto _start;
}
}
else
{
uint8 x_34; 
lean::dec(x_17);
lean::dec(x_14);
lean::dec(x_1);
x_34 = !lean::is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::cnstr_get(x_18, 0);
x_36 = lean::cnstr_get(x_18, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_18);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
obj* l_Lean_Syntax_fixKinds___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_1) == 1)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::cnstr_get(x_1, 2);
x_13 = l_Lean_SyntaxNodeKind_fix___main(x_10, x_2);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = lean::box(0);
lean::cnstr_set(x_13, 0, x_16);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Array_ummapAux___main___at_Lean_Syntax_fixKinds___main___spec__1(x_17, x_11, x_13);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; 
x_20 = lean::cnstr_get(x_18, 0);
lean::cnstr_set(x_1, 1, x_20);
lean::cnstr_set(x_1, 0, x_15);
lean::cnstr_set(x_18, 0, x_1);
return x_18;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_18, 0);
x_22 = lean::cnstr_get(x_18, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_18);
lean::cnstr_set(x_1, 1, x_21);
lean::cnstr_set(x_1, 0, x_15);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8 x_24; 
lean::dec(x_15);
lean::free_heap_obj(x_1);
lean::dec(x_12);
x_24 = !lean::is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_18, 0);
x_26 = lean::cnstr_get(x_18, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_18);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_28 = lean::cnstr_get(x_13, 0);
x_29 = lean::cnstr_get(x_13, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_13);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
x_32 = lean::mk_nat_obj(0u);
x_33 = l_Array_ummapAux___main___at_Lean_Syntax_fixKinds___main___spec__1(x_32, x_11, x_31);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_36 = x_33;
} else {
 lean::dec_ref(x_33);
 x_36 = lean::box(0);
}
lean::cnstr_set(x_1, 1, x_34);
lean::cnstr_set(x_1, 0, x_28);
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_28);
lean::free_heap_obj(x_1);
lean::dec(x_12);
x_38 = lean::cnstr_get(x_33, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_33, 1);
lean::inc(x_39);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_40 = x_33;
} else {
 lean::dec_ref(x_33);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8 x_42; 
lean::free_heap_obj(x_1);
lean::dec(x_12);
lean::dec(x_11);
x_42 = !lean::is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_13, 0);
x_44 = lean::cnstr_get(x_13, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_13);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_46 = lean::cnstr_get(x_1, 0);
x_47 = lean::cnstr_get(x_1, 1);
x_48 = lean::cnstr_get(x_1, 2);
lean::inc(x_48);
lean::inc(x_47);
lean::inc(x_46);
lean::dec(x_1);
x_49 = l_Lean_SyntaxNodeKind_fix___main(x_46, x_2);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
x_55 = lean::mk_nat_obj(0u);
x_56 = l_Array_ummapAux___main___at_Lean_Syntax_fixKinds___main___spec__1(x_55, x_47, x_54);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
x_60 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_60, 0, x_50);
lean::cnstr_set(x_60, 1, x_57);
lean::cnstr_set(x_60, 2, x_48);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_50);
lean::dec(x_48);
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_56, 1);
lean::inc(x_63);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_64 = x_56;
} else {
 lean::dec_ref(x_56);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_63);
return x_65;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_48);
lean::dec(x_47);
x_66 = lean::cnstr_get(x_49, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_49, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_68 = x_49;
} else {
 lean::dec_ref(x_49);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
}
}
else
{
obj* x_70; 
x_70 = lean::box(0);
x_3 = x_70;
goto block_8;
}
block_8:
{
uint8 x_4; 
lean::dec(x_3);
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_2, 0);
lean::dec(x_5);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
}
}
obj* l_Lean_Syntax_fixKinds(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_fixKinds___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_unreachIsNodeMissing(obj* x_1, obj* x_2) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeAtom(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeAtom___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_unreachIsNodeAtom(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_unreachIsNodeIdent(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeIdent___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_unreachIsNodeIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_8;
}
}
obj* l_Lean_withArgs___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = lean::apply_1(x_2, x_3);
return x_4;
}
}
obj* l_Lean_withArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_withArgs___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_updateArgs(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::apply_1(x_2, x_4);
lean::cnstr_set(x_1, 1, x_5);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::apply_1(x_2, x_7);
x_10 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_8);
return x_10;
}
}
}
obj* l_Lean_MacroScopes_flip___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_Lean_MacroScopes_flip___main(x_1, x_5);
if (lean::obj_tag(x_6) == 0)
{
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::nat_dec_eq(x_4, x_7);
lean::dec(x_7);
if (x_9 == 0)
{
lean::dec(x_8);
lean::cnstr_set(x_2, 1, x_6);
return x_2;
}
else
{
lean::dec(x_6);
lean::free_heap_obj(x_2);
lean::dec(x_4);
return x_8;
}
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_2);
x_12 = l_Lean_MacroScopes_flip___main(x_1, x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
x_16 = lean::nat_dec_eq(x_10, x_14);
lean::dec(x_14);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
else
{
lean::dec(x_12);
lean::dec(x_10);
return x_15;
}
}
}
}
}
}
obj* l_Lean_MacroScopes_flip___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_MacroScopes_flip___main(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_MacroScopes_flip(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_MacroScopes_flip___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_MacroScopes_flip___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_MacroScopes_flip(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_Syntax_isIdent___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 3)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Lean_Syntax_isIdent___main___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isIdent___main(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Syntax_isIdent(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Syntax_isIdent___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isIdent___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isIdent(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_Syntax_isOfKind___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::nat_dec_eq(x_4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
obj* l_Lean_Syntax_isOfKind___main___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Syntax_isOfKind___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_Syntax_isOfKind(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Syntax_isOfKind___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_isOfKind___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Syntax_flipScopes___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
return x_1;
}
case 1:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
x_4 = l_Lean_MacroScopes_flip___main(x_3, x_3);
lean::dec(x_3);
lean::cnstr_set(x_1, 2, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_7);
x_8 = l_Lean_MacroScopes_flip___main(x_7, x_7);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
}
case 2:
{
return x_1;
}
default: 
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_1);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
x_12 = l_Lean_MacroScopes_flip___main(x_11, x_11);
lean::dec(x_11);
lean::cnstr_set(x_1, 4, x_12);
return x_1;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
x_15 = lean::cnstr_get(x_1, 2);
x_16 = lean::cnstr_get(x_1, 3);
x_17 = lean::cnstr_get(x_1, 4);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_17);
x_18 = l_Lean_MacroScopes_flip___main(x_17, x_17);
lean::dec(x_17);
x_19 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_14);
lean::cnstr_set(x_19, 2, x_15);
lean::cnstr_set(x_19, 3, x_16);
lean::cnstr_set(x_19, 4, x_18);
return x_19;
}
}
}
}
}
obj* l_Lean_Syntax_flipScopes___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_flipScopes___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_flipScopes(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_flipScopes___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_flipScopes___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_flipScopes(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_toSyntaxNode___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean::array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_Syntax_flipScopes___main(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean::array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Lean_Syntax_toSyntaxNode___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::apply_1(x_3, x_1);
return x_5;
}
else
{
uint8 x_6; 
lean::dec(x_4);
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
lean::dec(x_8);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_ummapAux___main___at_Lean_Syntax_toSyntaxNode___spec__1(x_9, x_7);
x_11 = lean::box(0);
lean::cnstr_set(x_1, 2, x_11);
lean::cnstr_set(x_1, 1, x_10);
x_12 = lean::apply_1(x_3, x_1);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_1);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_ummapAux___main___at_Lean_Syntax_toSyntaxNode___spec__1(x_15, x_14);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_18, 0, x_13);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
x_19 = lean::apply_1(x_3, x_18);
return x_19;
}
}
}
else
{
lean::dec(x_3);
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_Lean_Syntax_toSyntaxNode(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_toSyntaxNode___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_toSyntaxNode___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_toSyntaxNode___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(x_4, x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::array_fget(x_4, x_3);
x_13 = lean::box(0);
lean::inc(x_12);
x_14 = x_13;
x_15 = lean::array_fset(x_4, x_3, x_14);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_18, 0, x_3);
lean::closure_set(x_18, 1, x_12);
lean::closure_set(x_18, 2, x_15);
lean::closure_set(x_18, 3, x_1);
lean::closure_set(x_18, 4, x_2);
x_19 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::apply_2(x_5, lean::box(0), x_2);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_10 = lean::apply_2(x_8, lean::box(0), x_9);
return x_10;
}
}
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_3);
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
return x_8;
}
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_9 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(x_1, x_2, x_8, x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg___lambda__2), 4, 3);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_4);
lean::closure_set(x_10, 2, x_5);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::apply_2(x_14, lean::box(0), x_12);
return x_15;
}
}
}
obj* l_Lean_Syntax_mreplace___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 1)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::inc(x_2);
x_14 = lean::apply_1(x_2, x_3);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg___lambda__3), 7, 6);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_2);
lean::closure_set(x_15, 2, x_11);
lean::closure_set(x_15, 3, x_10);
lean::closure_set(x_15, 4, x_12);
lean::closure_set(x_15, 5, x_13);
x_16 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::box(0);
x_4 = x_17;
goto block_9;
}
block_9:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_4);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::inc(x_3);
x_6 = lean::apply_1(x_2, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
}
obj* l_Lean_Syntax_mreplace___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_mreplace___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_mreplace___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_mreplace___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_mreplace___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Syntax_mreplace(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_mreplace___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_mreplace(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_replace___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
lean::inc(x_8);
lean::inc(x_1);
x_12 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_replace___spec__1(x_1, x_8);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean::array_fset(x_11, x_2, x_15);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_replace___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_2) == 1)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
lean::inc(x_1);
lean::inc(x_2);
x_10 = lean::apply_1(x_1, x_2);
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_2, 2);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_2, 1);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_2, 0);
lean::dec(x_14);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_ummapAux___main___at_Lean_Syntax_replace___spec__2(x_1, x_15, x_8);
lean::cnstr_set(x_2, 1, x_16);
return x_2;
}
else
{
obj* x_17; 
lean::free_heap_obj(x_2);
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
return x_17;
}
}
else
{
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::mk_nat_obj(0u);
x_19 = l_Array_ummapAux___main___at_Lean_Syntax_replace___spec__2(x_1, x_18, x_8);
x_20 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_9);
return x_20;
}
else
{
obj* x_21; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_10, 0);
lean::inc(x_21);
lean::dec(x_10);
return x_21;
}
}
}
else
{
obj* x_22; 
x_22 = lean::box(0);
x_3 = x_22;
goto block_6;
}
block_6:
{
obj* x_4; 
lean::dec(x_3);
lean::inc(x_2);
x_4 = lean::apply_1(x_1, x_2);
if (lean::obj_tag(x_4) == 0)
{
return x_2;
}
else
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
}
}
obj* l_Lean_Syntax_replace___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_replace___spec__1(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_replace(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_replace___rarg), 2, 0);
return x_4;
}
}
obj* l_Lean_Syntax_replace___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_replace(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_1__updateInfo___main(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_4, 2);
lean::dec(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::dec(x_8);
lean::inc(x_6);
lean::cnstr_set(x_4, 2, x_6);
lean::cnstr_set(x_4, 1, x_2);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_1, 0, x_11);
return x_1;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_16 = x_12;
} else {
 lean::dec_ref(x_12);
 x_16 = lean::box(0);
}
lean::inc(x_13);
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_2);
lean::cnstr_set(x_17, 2, x_13);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
lean::cnstr_set(x_18, 2, x_14);
return x_18;
}
}
}
obj* l___private_init_lean_syntax_1__updateInfo(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_syntax_1__updateInfo___main(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_syntax_2__updateLeadingAux___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
case 1:
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
case 2:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_1);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_13, 2);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_14, 2);
lean::inc(x_15);
lean::dec(x_14);
x_16 = l___private_init_lean_syntax_1__updateInfo___main(x_13, x_2);
lean::cnstr_set(x_7, 0, x_16);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::cnstr_get(x_19, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_20, 2);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l___private_init_lean_syntax_1__updateInfo___main(x_19, x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_1, 0, x_23);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_28 = x_7;
} else {
 lean::dec_ref(x_7);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_27, 2);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_29, 2);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l___private_init_lean_syntax_1__updateInfo___main(x_27, x_2);
if (lean::is_scalar(x_28)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_28;
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
}
}
default: 
{
obj* x_36; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_1);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_2);
return x_38;
}
else
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_1);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = lean::cnstr_get(x_1, 0);
lean::dec(x_40);
x_41 = !lean::is_exclusive(x_36);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_36, 0);
x_43 = lean::cnstr_get(x_42, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_43, 2);
lean::inc(x_44);
lean::dec(x_43);
x_45 = l___private_init_lean_syntax_1__updateInfo___main(x_42, x_2);
lean::cnstr_set(x_36, 0, x_45);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_1);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
lean::dec(x_36);
x_49 = lean::cnstr_get(x_48, 2);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_49, 2);
lean::inc(x_50);
lean::dec(x_49);
x_51 = l___private_init_lean_syntax_1__updateInfo___main(x_48, x_2);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_1, 0, x_52);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_1);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
return x_54;
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_55 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_1, 2);
x_57 = lean::cnstr_get(x_1, 3);
x_58 = lean::cnstr_get(x_1, 4);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_1);
x_59 = lean::cnstr_get(x_36, 0);
lean::inc(x_59);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_60 = x_36;
} else {
 lean::dec_ref(x_36);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_59, 2);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_61, 2);
lean::inc(x_62);
lean::dec(x_61);
x_63 = l___private_init_lean_syntax_1__updateInfo___main(x_59, x_2);
if (lean::is_scalar(x_60)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_60;
}
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_55);
lean::cnstr_set(x_65, 2, x_56);
lean::cnstr_set(x_65, 3, x_57);
lean::cnstr_set(x_65, 4, x_58);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_62);
return x_67;
}
}
}
}
}
}
obj* l___private_init_lean_syntax_2__updateLeadingAux(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
case 1:
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
case 2:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_1);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_7);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_13, 2);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_14, 2);
lean::inc(x_15);
lean::dec(x_14);
x_16 = l___private_init_lean_syntax_1__updateInfo___main(x_13, x_2);
lean::cnstr_set(x_7, 0, x_16);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_1);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_20 = lean::cnstr_get(x_19, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_20, 2);
lean::inc(x_21);
lean::dec(x_20);
x_22 = l___private_init_lean_syntax_1__updateInfo___main(x_19, x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_1, 0, x_23);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_1);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_28 = x_7;
} else {
 lean::dec_ref(x_7);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_27, 2);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_29, 2);
lean::inc(x_30);
lean::dec(x_29);
x_31 = l___private_init_lean_syntax_1__updateInfo___main(x_27, x_2);
if (lean::is_scalar(x_28)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_28;
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
}
}
default: 
{
obj* x_36; 
x_36 = lean::cnstr_get(x_1, 0);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
lean::dec(x_1);
x_37 = lean::box(0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_2);
return x_38;
}
else
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_1);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; 
x_40 = lean::cnstr_get(x_1, 0);
lean::dec(x_40);
x_41 = !lean::is_exclusive(x_36);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_36, 0);
x_43 = lean::cnstr_get(x_42, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_43, 2);
lean::inc(x_44);
lean::dec(x_43);
x_45 = l___private_init_lean_syntax_1__updateInfo___main(x_42, x_2);
lean::cnstr_set(x_36, 0, x_45);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_1);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_48 = lean::cnstr_get(x_36, 0);
lean::inc(x_48);
lean::dec(x_36);
x_49 = lean::cnstr_get(x_48, 2);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_49, 2);
lean::inc(x_50);
lean::dec(x_49);
x_51 = l___private_init_lean_syntax_1__updateInfo___main(x_48, x_2);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_1, 0, x_52);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_1);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_50);
return x_54;
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_55 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_1, 2);
x_57 = lean::cnstr_get(x_1, 3);
x_58 = lean::cnstr_get(x_1, 4);
lean::inc(x_58);
lean::inc(x_57);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_1);
x_59 = lean::cnstr_get(x_36, 0);
lean::inc(x_59);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_60 = x_36;
} else {
 lean::dec_ref(x_36);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_59, 2);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_61, 2);
lean::inc(x_62);
lean::dec(x_61);
x_63 = l___private_init_lean_syntax_1__updateInfo___main(x_59, x_2);
if (lean::is_scalar(x_60)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_60;
}
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_55);
lean::cnstr_set(x_65, 2, x_56);
lean::cnstr_set(x_65, 3, x_57);
lean::cnstr_set(x_65, 4, x_58);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_62);
return x_67;
}
}
}
}
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_2;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_9 = lean::array_fget(x_2, x_1);
x_10 = lean::box(0);
lean::inc(x_9);
x_11 = x_10;
x_12 = lean::array_fset(x_2, x_1, x_11);
lean::inc(x_9);
x_13 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_9, x_3);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean::array_fset(x_12, x_1, x_18);
lean::dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_3 = x_15;
goto _start;
}
}
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(x_5, x_4, x_2);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::cnstr_set(x_1, 1, x_8);
lean::cnstr_set(x_6, 0, x_1);
return x_6;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_6, 0);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_6);
lean::cnstr_set(x_1, 1, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(x_15, x_13, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_19 = x_16;
} else {
 lean::dec_ref(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_14);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
else
{
obj* x_22; 
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
return x_22;
}
}
}
obj* l_Lean_Syntax_updateLeading(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Syntax_updateTrailing___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
lean::dec(x_1);
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
x_6 = lean::array_get_size(x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_2);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::cnstr_get(x_2, 2);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_2, 1);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 0);
lean::dec(x_12);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_6, x_13);
lean::dec(x_6);
x_15 = l_Lean_stxInh;
x_16 = lean::array_get(x_15, x_4, x_14);
x_17 = l_Lean_Syntax_updateTrailing___main(x_1, x_16);
x_18 = lean::array_set(x_4, x_14, x_17);
lean::dec(x_14);
lean::cnstr_set(x_2, 1, x_18);
return x_2;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_2);
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_6, x_19);
lean::dec(x_6);
x_21 = l_Lean_stxInh;
x_22 = lean::array_get(x_21, x_4, x_20);
x_23 = l_Lean_Syntax_updateTrailing___main(x_1, x_22);
x_24 = lean::array_set(x_4, x_20, x_23);
lean::dec(x_20);
x_25 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_5);
return x_25;
}
}
else
{
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
}
case 2:
{
obj* x_26; 
x_26 = lean::cnstr_get(x_2, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_27; 
x_27 = !lean::is_exclusive(x_2);
if (x_27 == 0)
{
obj* x_28; uint8 x_29; 
x_28 = lean::cnstr_get(x_2, 0);
lean::dec(x_28);
x_29 = !lean::is_exclusive(x_26);
if (x_29 == 0)
{
obj* x_30; obj* x_31; 
x_30 = lean::cnstr_get(x_26, 0);
x_31 = l_Lean_SourceInfo_updateTrailing___main(x_30, x_1);
lean::cnstr_set(x_26, 0, x_31);
return x_2;
}
else
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
x_33 = l_Lean_SourceInfo_updateTrailing___main(x_32, x_1);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_2, 0, x_34);
return x_2;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_2, 1);
lean::inc(x_35);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_37 = x_26;
} else {
 lean::dec_ref(x_26);
 x_37 = lean::box(0);
}
x_38 = l_Lean_SourceInfo_updateTrailing___main(x_36, x_1);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_35);
return x_40;
}
}
}
default: 
{
obj* x_41; 
x_41 = lean::cnstr_get(x_2, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_42; 
x_42 = !lean::is_exclusive(x_2);
if (x_42 == 0)
{
obj* x_43; uint8 x_44; 
x_43 = lean::cnstr_get(x_2, 0);
lean::dec(x_43);
x_44 = !lean::is_exclusive(x_41);
if (x_44 == 0)
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_41, 0);
x_46 = l_Lean_SourceInfo_updateTrailing___main(x_45, x_1);
lean::cnstr_set(x_41, 0, x_46);
return x_2;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_41, 0);
lean::inc(x_47);
lean::dec(x_41);
x_48 = l_Lean_SourceInfo_updateTrailing___main(x_47, x_1);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_2, 0, x_49);
return x_2;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_50 = lean::cnstr_get(x_2, 1);
x_51 = lean::cnstr_get(x_2, 2);
x_52 = lean::cnstr_get(x_2, 3);
x_53 = lean::cnstr_get(x_2, 4);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_2);
x_54 = lean::cnstr_get(x_41, 0);
lean::inc(x_54);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_55 = x_41;
} else {
 lean::dec_ref(x_41);
 x_55 = lean::box(0);
}
x_56 = l_Lean_SourceInfo_updateTrailing___main(x_54, x_1);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_50);
lean::cnstr_set(x_58, 2, x_51);
lean::cnstr_set(x_58, 3, x_52);
lean::cnstr_set(x_58, 4, x_53);
return x_58;
}
}
}
}
}
}
obj* l_Lean_Syntax_updateTrailing(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_updateTrailing___main(x_1, x_2);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::array_fget(x_1, x_2);
x_7 = l_Lean_Syntax_getHeadInfo___main(x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_2, x_8);
lean::dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_2);
return x_7;
}
}
}
}
obj* l_Lean_Syntax_getHeadInfo___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_3, x_4);
return x_5;
}
default: 
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
return x_6;
}
}
}
}
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_getHeadInfo___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getPos(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_Lean_Syntax_getPos___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getPos(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_3__reprintLeaf___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_3, 2);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::cnstr_get(x_4, 2);
x_9 = lean::string_utf8_extract(x_6, x_7, x_8);
x_10 = lean::string_append(x_9, x_2);
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_13 = lean::cnstr_get(x_5, 2);
x_14 = lean::string_utf8_extract(x_11, x_12, x_13);
x_15 = lean::string_append(x_10, x_14);
lean::dec(x_14);
return x_15;
}
}
}
obj* l___private_init_lean_syntax_3__reprintLeaf___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_syntax_3__reprintLeaf___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_syntax_3__reprintLeaf(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_syntax_3__reprintLeaf___main(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_syntax_3__reprintLeaf___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_syntax_3__reprintLeaf(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::string_append(x_4, x_11);
lean::dec(x_11);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::array_fget(x_2, x_3);
x_9 = l_Lean_Syntax_reprint___main(x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::string_dec_eq(x_4, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_4);
lean::dec(x_3);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_3 = x_15;
goto _start;
}
}
}
}
}
obj* _init_l_Lean_Syntax_reprint___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("");
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_reprint___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_choiceKind;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Syntax_reprint___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_3, 1);
x_6 = l_Lean_Syntax_reprint___main___closed__2;
x_7 = lean::nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::mk_nat_obj(0u);
x_9 = l_String_splitAux___main___closed__1;
x_10 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(x_4, x_4, x_8, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::array_get_size(x_4);
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::nat_dec_eq(x_11, x_12);
lean::dec(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = l_Lean_stxInh;
x_15 = lean::array_get(x_14, x_4, x_12);
x_16 = l_Lean_Syntax_reprint___main(x_15);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; 
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
lean::dec(x_16);
x_19 = lean::mk_nat_obj(1u);
x_20 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(x_4, x_4, x_19, x_18);
return x_20;
}
}
else
{
obj* x_21; 
x_21 = lean::box(0);
return x_21;
}
}
}
case 2:
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_1, 0);
x_23 = lean::cnstr_get(x_1, 1);
x_24 = l___private_init_lean_syntax_3__reprintLeaf___main(x_22, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
default: 
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_1, 1);
x_27 = lean::cnstr_get(x_1, 0);
x_28 = lean::cnstr_get(x_26, 0);
x_29 = lean::cnstr_get(x_26, 1);
x_30 = lean::cnstr_get(x_26, 2);
x_31 = lean::string_utf8_extract(x_28, x_29, x_30);
x_32 = l___private_init_lean_syntax_3__reprintLeaf___main(x_27, x_31);
lean::dec(x_31);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Syntax_reprint___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_reprint(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_reprint___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(obj* x_1) {
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
x_6 = l_Lean_Syntax_formatStx___main(x_4);
x_7 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_5);
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
x_10 = l_Lean_Syntax_formatStx___main(x_8);
x_11 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
return x_5;
}
else
{
obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = 0;
lean::inc(x_2);
lean::inc(x_6);
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_7);
x_9 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_4, x_2);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
return x_10;
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Nat_repr(x_5);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = l_Nat_repr(x_8);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = 0;
lean::inc(x_2);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_11);
x_13 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(x_4, x_2);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_11);
return x_14;
}
}
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(obj* x_1) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(x_5);
lean::cnstr_set(x_1, 1, x_9);
lean::cnstr_set(x_1, 0, x_8);
return x_1;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_1);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_10);
x_14 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(x_11);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(obj* x_1) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = l_Nat_repr(x_4);
x_7 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_8 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(x_5);
lean::cnstr_set(x_1, 1, x_8);
lean::cnstr_set(x_1, 0, x_7);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_1);
x_11 = l_Nat_repr(x_9);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("<missing>");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("noKind");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("}");
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___closed__6() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("{");
x_2 = lean::string_length(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_formatStx___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Syntax_formatStx___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = l_Lean_Syntax_formatStx___main___closed__2;
x_8 = lean_name_dec_eq(x_6, x_7);
if (lean::obj_tag(x_5) == 0)
{
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_9 = l_Lean_Syntax_formatStx___main___closed__3;
x_10 = lean::box(0);
x_11 = l_Lean_Name_replacePrefix___main(x_6, x_9, x_10);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_11);
x_14 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = 0;
x_16 = l_Lean_Format_join___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_19 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(1);
x_22 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_20, x_21);
lean::dec(x_20);
x_23 = l_Lean_Format_paren___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_15);
x_25 = l_Lean_Format_paren___closed__2;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_15);
x_27 = l_Lean_Format_paren___closed__3;
x_28 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = l_Lean_Format_group___main(x_28);
return x_29;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_6);
x_30 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_31 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_30);
x_32 = lean::box(1);
x_33 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_31, x_32);
lean::dec(x_31);
x_34 = 0;
x_35 = l_Lean_Format_join___closed__1;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_33);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_34);
x_37 = l_Lean_Format_sbracket___closed__1;
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_34);
x_39 = l_Lean_Format_sbracket___closed__2;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_34);
x_41 = l_Lean_Format_sbracket___closed__3;
x_42 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_Lean_Format_group___main(x_42);
return x_43;
}
}
else
{
obj* x_44; uint8 x_45; 
lean::inc(x_5);
x_44 = l_List_reverse___rarg(x_5);
x_45 = !lean::is_exclusive(x_5);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_46 = lean::cnstr_get(x_5, 1);
lean::dec(x_46);
x_47 = lean::cnstr_get(x_5, 0);
lean::dec(x_47);
x_48 = l_Lean_formatKVMap___closed__1;
x_49 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(x_44, x_48);
x_50 = 0;
x_51 = l_Lean_Syntax_formatStx___main___closed__4;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_49);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_50);
x_53 = l_Lean_Syntax_formatStx___main___closed__5;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_50);
x_55 = l_Lean_Syntax_formatStx___main___closed__6;
x_56 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_54);
x_57 = l_Lean_Format_group___main(x_56);
if (x_8 == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_58 = l_Lean_Syntax_formatStx___main___closed__3;
x_59 = lean::box(0);
x_60 = l_Lean_Name_replacePrefix___main(x_6, x_58, x_59);
x_61 = l_Lean_Name_toString___closed__1;
x_62 = l_Lean_Name_toStringWithSep___main(x_61, x_60);
x_63 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_57);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_50);
x_65 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_66 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_65);
lean::cnstr_set(x_5, 1, x_66);
lean::cnstr_set(x_5, 0, x_64);
x_67 = lean::box(1);
x_68 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_5, x_67);
lean::dec(x_5);
x_69 = l_Lean_Format_paren___closed__1;
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_68);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_50);
x_71 = l_Lean_Format_paren___closed__2;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_50);
x_73 = l_Lean_Format_paren___closed__3;
x_74 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_72);
x_75 = l_Lean_Format_group___main(x_74);
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::free_heap_obj(x_5);
lean::dec(x_6);
x_76 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_77 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_76);
x_78 = lean::box(1);
x_79 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_77, x_78);
lean::dec(x_77);
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_57);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_50);
x_81 = l_Lean_Format_sbracket___closed__1;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_50);
x_83 = l_Lean_Format_sbracket___closed__2;
x_84 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
lean::cnstr_set_scalar(x_84, sizeof(void*)*2, x_50);
x_85 = l_Lean_Format_sbracket___closed__3;
x_86 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_84);
x_87 = l_Lean_Format_group___main(x_86);
return x_87;
}
}
else
{
obj* x_88; obj* x_89; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_5);
x_88 = l_Lean_formatKVMap___closed__1;
x_89 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(x_44, x_88);
x_90 = 0;
x_91 = l_Lean_Syntax_formatStx___main___closed__4;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_89);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_90);
x_93 = l_Lean_Syntax_formatStx___main___closed__5;
x_94 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*2, x_90);
x_95 = l_Lean_Syntax_formatStx___main___closed__6;
x_96 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_94);
x_97 = l_Lean_Format_group___main(x_96);
if (x_8 == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_98 = l_Lean_Syntax_formatStx___main___closed__3;
x_99 = lean::box(0);
x_100 = l_Lean_Name_replacePrefix___main(x_6, x_98, x_99);
x_101 = l_Lean_Name_toString___closed__1;
x_102 = l_Lean_Name_toStringWithSep___main(x_101, x_100);
x_103 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_97);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_90);
x_105 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_106 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_105);
x_107 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set(x_107, 1, x_106);
x_108 = lean::box(1);
x_109 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_107, x_108);
lean::dec(x_107);
x_110 = l_Lean_Format_paren___closed__1;
x_111 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_109);
lean::cnstr_set_scalar(x_111, sizeof(void*)*2, x_90);
x_112 = l_Lean_Format_paren___closed__2;
x_113 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set(x_113, 1, x_112);
lean::cnstr_set_scalar(x_113, sizeof(void*)*2, x_90);
x_114 = l_Lean_Format_paren___closed__3;
x_115 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_113);
x_116 = l_Lean_Format_group___main(x_115);
return x_116;
}
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_6);
x_117 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_118 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_117);
x_119 = lean::box(1);
x_120 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_118, x_119);
lean::dec(x_118);
x_121 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_121, 0, x_97);
lean::cnstr_set(x_121, 1, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*2, x_90);
x_122 = l_Lean_Format_sbracket___closed__1;
x_123 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_121);
lean::cnstr_set_scalar(x_123, sizeof(void*)*2, x_90);
x_124 = l_Lean_Format_sbracket___closed__2;
x_125 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_125, 0, x_123);
lean::cnstr_set(x_125, 1, x_124);
lean::cnstr_set_scalar(x_125, sizeof(void*)*2, x_90);
x_126 = l_Lean_Format_sbracket___closed__3;
x_127 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_125);
x_128 = l_Lean_Format_group___main(x_127);
return x_128;
}
}
}
}
case 2:
{
obj* x_129; obj* x_130; obj* x_131; 
x_129 = lean::cnstr_get(x_1, 1);
lean::inc(x_129);
lean::dec(x_1);
x_130 = l_String_quote(x_129);
x_131 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
return x_131;
}
default: 
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; uint8 x_142; obj* x_143; obj* x_144; 
x_132 = lean::cnstr_get(x_1, 2);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_1, 3);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_1, 4);
lean::inc(x_134);
lean::dec(x_1);
x_135 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(x_133);
x_136 = l_List_reverse___rarg(x_134);
x_137 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(x_136);
x_138 = l_List_append___rarg(x_135, x_137);
x_139 = l_Lean_Name_toString___closed__1;
x_140 = l_Lean_Name_toStringWithSep___main(x_139, x_132);
x_141 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_141, 0, x_140);
x_142 = 0;
x_143 = l_Lean_formatDataValue___main___closed__3;
x_144 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_141);
lean::cnstr_set_scalar(x_144, sizeof(void*)*2, x_142);
if (lean::obj_tag(x_138) == 0)
{
obj* x_145; obj* x_146; 
x_145 = l_Lean_Format_join___closed__1;
x_146 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_146, 0, x_144);
lean::cnstr_set(x_146, 1, x_145);
lean::cnstr_set_scalar(x_146, sizeof(void*)*2, x_142);
return x_146;
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_147 = l_Lean_formatKVMap___closed__1;
x_148 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_138, x_147);
lean::dec(x_138);
x_149 = l_Lean_Syntax_formatStx___main___closed__4;
x_150 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_148);
lean::cnstr_set_scalar(x_150, sizeof(void*)*2, x_142);
x_151 = l_Lean_Syntax_formatStx___main___closed__5;
x_152 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_152, 0, x_150);
lean::cnstr_set(x_152, 1, x_151);
lean::cnstr_set_scalar(x_152, sizeof(void*)*2, x_142);
x_153 = l_Lean_Syntax_formatStx___main___closed__6;
x_154 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_152);
x_155 = l_Lean_Format_group___main(x_154);
x_156 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_156, 0, x_144);
lean::cnstr_set(x_156, 1, x_155);
lean::cnstr_set_scalar(x_156, sizeof(void*)*2, x_142);
return x_156;
}
}
}
}
}
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_formatStx(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_formatStx___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_Lean_HasFormat() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_formatStx), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Syntax_HasToString() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_HasRepr___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_formatStx), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
namespace lean {
obj* mk_syntax_atom_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
}
namespace lean {
obj* mk_syntax_ident_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::box(0);
x_3 = l_Lean_Name_toString___closed__1;
lean::inc(x_1);
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_1);
x_5 = lean::string_utf8_byte_size(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(3, 5, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 4, x_8);
return x_9;
}
}
}
namespace lean {
obj* mk_syntax_list_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_Lean_nullKind;
x_4 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
return x_4;
}
}
}
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_format(obj*);
obj* initialize_init_data_array_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_syntax(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
l_Lean_MacroScope_DecidableEq = _init_l_Lean_MacroScope_DecidableEq();
lean::mark_persistent(l_Lean_MacroScope_DecidableEq);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "MacroScope"), "DecidableEq"), l_Lean_MacroScope_DecidableEq);
l_Lean_MacroScope_Lean_HasFormat = _init_l_Lean_MacroScope_Lean_HasFormat();
lean::mark_persistent(l_Lean_MacroScope_Lean_HasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "MacroScope"), "Lean"), "HasFormat"), l_Lean_MacroScope_Lean_HasFormat);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "SourceInfo"), "updateTrailing"), 2, l_Lean_SourceInfo_updateTrailing);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkUniqIdRef"), 1, l_Lean_mkUniqIdRef);
w = l_Lean_mkUniqIdRef(w);
if (io_result_is_error(w)) return w;
l_Lean_nextUniqId = io_result_get_value(w);
lean::mark_persistent(l_Lean_nextUniqId);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "nextUniqId"), l_Lean_nextUniqId);
l_Lean_stxKindInh = _init_l_Lean_stxKindInh();
lean::mark_persistent(l_Lean_stxKindInh);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "stxKindInh"), l_Lean_stxKindInh);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "stxKindBeq"), 2, l_Lean_stxKindBeq___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkNameToKindTable"), 1, l_Lean_mkNameToKindTable);
w = l_Lean_mkNameToKindTable(w);
if (io_result_is_error(w)) return w;
l_Lean_nameToKindTable = io_result_get_value(w);
lean::mark_persistent(l_Lean_nameToKindTable);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "nameToKindTable"), l_Lean_nameToKindTable);
l_Lean_nextKind___closed__1 = _init_l_Lean_nextKind___closed__1();
lean::mark_persistent(l_Lean_nextKind___closed__1);
l_Lean_nextKind___closed__2 = _init_l_Lean_nextKind___closed__2();
lean::mark_persistent(l_Lean_nextKind___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "nextKind"), 2, l_Lean_nextKind);
l_Lean_mkNullKind___closed__1 = _init_l_Lean_mkNullKind___closed__1();
lean::mark_persistent(l_Lean_mkNullKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkNullKind"), 1, l_Lean_mkNullKind);
w = l_Lean_mkNullKind(w);
if (io_result_is_error(w)) return w;
l_Lean_nullKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_nullKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "nullKind"), l_Lean_nullKind);
l_Lean_mkChoiceKind___closed__1 = _init_l_Lean_mkChoiceKind___closed__1();
lean::mark_persistent(l_Lean_mkChoiceKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkChoiceKind"), 1, l_Lean_mkChoiceKind);
w = l_Lean_mkChoiceKind(w);
if (io_result_is_error(w)) return w;
l_Lean_choiceKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_choiceKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "choiceKind"), l_Lean_choiceKind);
l_Lean_mkOptionSomeKind___closed__1 = _init_l_Lean_mkOptionSomeKind___closed__1();
lean::mark_persistent(l_Lean_mkOptionSomeKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkOptionSomeKind"), 1, l_Lean_mkOptionSomeKind);
w = l_Lean_mkOptionSomeKind(w);
if (io_result_is_error(w)) return w;
l_Lean_optionSomeKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_optionSomeKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "optionSomeKind"), l_Lean_optionSomeKind);
l_Lean_mkOptionNoneKind___closed__1 = _init_l_Lean_mkOptionNoneKind___closed__1();
lean::mark_persistent(l_Lean_mkOptionNoneKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkOptionNoneKind"), 1, l_Lean_mkOptionNoneKind);
w = l_Lean_mkOptionNoneKind(w);
if (io_result_is_error(w)) return w;
l_Lean_optionNoneKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_optionNoneKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "optionNoneKind"), l_Lean_optionNoneKind);
l_Lean_mkManyKind___closed__1 = _init_l_Lean_mkManyKind___closed__1();
lean::mark_persistent(l_Lean_mkManyKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkManyKind"), 1, l_Lean_mkManyKind);
w = l_Lean_mkManyKind(w);
if (io_result_is_error(w)) return w;
l_Lean_manyKind = io_result_get_value(w);
lean::mark_persistent(l_Lean_manyKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "manyKind"), l_Lean_manyKind);
l_Lean_mkHoleKind___closed__1 = _init_l_Lean_mkHoleKind___closed__1();
lean::mark_persistent(l_Lean_mkHoleKind___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkHoleKind"), 1, l_Lean_mkHoleKind);
l_Lean_stxInh = _init_l_Lean_stxInh();
lean::mark_persistent(l_Lean_stxInh);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "stxInh"), l_Lean_stxInh);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isMissing"), 1, l_Lean_Syntax_isMissing___boxed);
l_Lean_SyntaxNodeKind_fix___main___closed__1 = _init_l_Lean_SyntaxNodeKind_fix___main___closed__1();
lean::mark_persistent(l_Lean_SyntaxNodeKind_fix___main___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "SyntaxNodeKind"), "fix"), 2, l_Lean_SyntaxNodeKind_fix);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "fixKinds"), 2, l_Lean_Syntax_fixKinds);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "unreachIsNodeMissing"), 2, l_Lean_unreachIsNodeMissing);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "unreachIsNodeAtom"), 4, l_Lean_unreachIsNodeAtom___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "unreachIsNodeIdent"), 7, l_Lean_unreachIsNodeIdent___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "withArgs"), 1, l_Lean_withArgs);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "updateArgs"), 2, l_Lean_updateArgs);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "MacroScopes"), "flip"), 2, l_Lean_MacroScopes_flip___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isIdent"), 1, l_Lean_Syntax_isIdent___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isOfKind"), 2, l_Lean_Syntax_isOfKind___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "flipScopes"), 1, l_Lean_Syntax_flipScopes___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "toSyntaxNode"), 1, l_Lean_Syntax_toSyntaxNode);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "mreplace"), 1, l_Lean_Syntax_mreplace___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "replace"), 3, l_Lean_Syntax_replace___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "updateLeading"), 1, l_Lean_Syntax_updateLeading);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "updateTrailing"), 2, l_Lean_Syntax_updateTrailing);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "getHeadInfo"), 1, l_Lean_Syntax_getHeadInfo___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "getPos"), 1, l_Lean_Syntax_getPos___boxed);
l_Lean_Syntax_reprint___main___closed__1 = _init_l_Lean_Syntax_reprint___main___closed__1();
lean::mark_persistent(l_Lean_Syntax_reprint___main___closed__1);
l_Lean_Syntax_reprint___main___closed__2 = _init_l_Lean_Syntax_reprint___main___closed__2();
lean::mark_persistent(l_Lean_Syntax_reprint___main___closed__2);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "reprint"), 1, l_Lean_Syntax_reprint___boxed);
l_Lean_Syntax_formatStx___main___closed__1 = _init_l_Lean_Syntax_formatStx___main___closed__1();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__1);
l_Lean_Syntax_formatStx___main___closed__2 = _init_l_Lean_Syntax_formatStx___main___closed__2();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__2);
l_Lean_Syntax_formatStx___main___closed__3 = _init_l_Lean_Syntax_formatStx___main___closed__3();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__3);
l_Lean_Syntax_formatStx___main___closed__4 = _init_l_Lean_Syntax_formatStx___main___closed__4();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__4);
l_Lean_Syntax_formatStx___main___closed__5 = _init_l_Lean_Syntax_formatStx___main___closed__5();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__5);
l_Lean_Syntax_formatStx___main___closed__6 = _init_l_Lean_Syntax_formatStx___main___closed__6();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___closed__6);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "formatStx"), 1, l_Lean_Syntax_formatStx);
l_Lean_Syntax_Lean_HasFormat = _init_l_Lean_Syntax_Lean_HasFormat();
lean::mark_persistent(l_Lean_Syntax_Lean_HasFormat);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "Lean"), "HasFormat"), l_Lean_Syntax_Lean_HasFormat);
l_Lean_Syntax_HasToString = _init_l_Lean_Syntax_HasToString();
lean::mark_persistent(l_Lean_Syntax_HasToString);
lean::register_constant(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "HasToString"), l_Lean_Syntax_HasToString);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "mkSimpleAtom"), 1, lean::mk_syntax_atom_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "mkSimpleIdent"), 1, lean::mk_syntax_ident_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "mkListNode"), 1, lean::mk_syntax_list_core);
return w;
}
