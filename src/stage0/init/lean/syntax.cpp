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
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___main(obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getHeadInfo___boxed(obj*);
obj* l_Lean_Syntax_replace(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Syntax_reprint___main___boxed(obj*);
obj* l_Lean_Syntax_flipScopes___rarg(obj*);
obj* l_Lean_Syntax_isNatLit(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_stxInh;
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_replace___spec__1(obj*, obj*);
extern obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_Syntax_formatStx___main___closed__5;
obj* l_Lean_Syntax_isOfKind___boxed(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_withArgs___rarg(obj*, obj*);
obj* l_Lean_Syntax_toSyntaxNode(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(obj*, obj*, obj*);
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_group___main(obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf___main___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_5__decodeOctalLitAux(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf(obj*, obj*);
obj* l_Lean_mkStrLit(obj*, obj*);
obj* l_Lean_Syntax_replace___boxed(obj*, obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_toSyntaxNode___spec__1(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l___private_init_lean_syntax_4__decodeBinLitAux___main(obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main(obj*);
obj* l_Lean_numLitKind;
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(obj*, obj*);
uint8 l_Lean_Syntax_isOfKind___main(obj*, obj*);
obj* l_Lean_Syntax_updateTrailing(obj*, obj*);
obj* l_Lean_updateArgs(obj*, obj*);
obj* l_Lean_MacroScopes_flip(obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l___private_init_lean_syntax_2__updateLeadingAux___main(obj*, obj*);
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_updateTrailing___main(obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_Syntax_isIdent___main___boxed(obj*);
obj* l_Lean_Syntax_isMissing___main___boxed(obj*);
obj* l_Lean_Syntax_reprint___boxed(obj*);
obj* l___private_init_lean_syntax_8__decodeNatLitVal(obj*);
obj* l_Lean_Syntax_formatStx___main___closed__2;
obj* l_Lean_Syntax_flipScopes___main(obj*);
obj* l_Lean_Syntax_HasToString;
obj* l_Lean_Syntax_formatStx___main___closed__4;
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___boxed(obj*, obj*, obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_6__decodeHexLitAux(obj*, obj*, obj*);
obj* l_Lean_mkNumLit(obj*, obj*);
extern obj* l_Lean_Format_join___closed__1;
obj* l___private_init_lean_syntax_6__decodeHexLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_SourceInfo_updateTrailing(obj*, obj*);
obj* l___private_init_lean_syntax_1__updateInfo___main(obj*, obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Lean_Syntax_replace___rarg(obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(obj*);
obj* l_Nat_repr(obj*);
obj* l___private_init_lean_syntax_4__decodeBinLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Syntax_isMissing___boxed(obj*);
obj* l_Lean_Syntax_isStrLit___main(obj*);
obj* l_Lean_Syntax_mreplace___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main___closed__1;
obj* l_Lean_Syntax_mreplace___boxed(obj*);
obj* l_Lean_unreachIsNodeIdent___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_MacroScope_DecidableEq;
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(obj*);
obj* l_Lean_Syntax_getPos___boxed(obj*);
obj* l_Lean_Syntax_isNatLit___main(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_Lean_HasFormat;
obj* l_Lean_Syntax_formatStx(obj*);
namespace lean {
obj* mk_syntax_str_lit_core(obj*);
}
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___boxed(obj*, obj*);
uint8 l_UInt32_decLe(uint32, uint32);
obj* l___private_init_lean_syntax_2__updateLeadingAux(obj*, obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_Syntax_isIdOrAtom(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(obj*, obj*);
uint8 l_Lean_Syntax_isOfKind(obj*, obj*);
obj* l_Lean_Syntax_getHeadInfo___main(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Syntax_formatStx___main___closed__1;
uint8 l_Lean_Syntax_isIdent___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_Lean_choiceKind;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__1(obj*, obj*, obj*);
namespace lean {
obj* mk_syntax_ident_core(obj*);
}
obj* l_Lean_strLitKind;
obj* l_Lean_Syntax_isStrLit___main___boxed(obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(obj*);
obj* l_Lean_Syntax_reprint(obj*);
obj* l_Lean_Syntax_getHeadInfo(obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Lean_Syntax_mreplace___rarg(obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeMissing(obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_HasRepr___lambda__1(obj*);
uint8 l_UInt32_decEq(uint32, uint32);
uint8 l_Lean_Syntax_isIdent(obj*);
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(obj*, obj*);
obj* l_Lean_Syntax_updateLeading(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_1__updateInfo(obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Syntax_flipScopes(obj*);
obj* l___private_init_lean_syntax_8__decodeNatLitVal___closed__1;
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__3;
obj* l___private_init_lean_syntax_6__decodeHexLitAux___main(obj*, obj*, obj*);
obj* l_Lean_MacroScope_Lean_HasFormat;
extern obj* l_Lean_formatKVMap___closed__1;
namespace lean {
obj* mk_syntax_list_core(obj*);
}
obj* l_Lean_Syntax_isNatLit___main___boxed(obj*);
obj* l_Lean_Syntax_isStrLit(obj*);
obj* l_Lean_Syntax_flipScopes___boxed(obj*);
obj* l_Lean_Syntax_isIdOrAtom___main___boxed(obj*);
obj* l_Lean_Syntax_isIdOrAtom___boxed(obj*);
namespace lean {
obj* mk_syntax_num_lit_core(obj*);
}
obj* l_Lean_Syntax_getPos(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeAtom___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___main(obj*, obj*, obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_formatDataValue___main___closed__3;
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___boxed(obj*);
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_isOfKind___main___boxed(obj*, obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
obj* l_Lean_Syntax_isNatLit___boxed(obj*);
obj* l___private_init_lean_syntax_8__decodeNatLitVal___boxed(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux(obj*, obj*, obj*);
obj* l_Lean_Syntax_mreplace___main___boxed(obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_3__reprintLeaf___main(obj*, obj*);
obj* l_Lean_MacroScopes_flip___main(obj*, obj*);
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux(obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___closed__6;
obj* l_String_quote(obj*);
obj* l_Lean_Syntax_mreplace(obj*);
obj* l_Lean_Syntax_isStrLit___boxed(obj*);
namespace lean {
obj* mk_syntax_atom_core(obj*);
}
obj* l_Lean_Syntax_mreplace___main(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkLit(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Lean_Syntax_isIdOrAtom___main(obj*);
obj* l_Lean_withArgs(obj*);
obj* l_Lean_MacroScopes_flip___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_6__decodeHexLitAux___boxed(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_replace___spec__2(obj*, obj*, obj*);
obj* l_Lean_Syntax_toSyntaxNode___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_isIdent___boxed(obj*);
obj* l_Lean_Syntax_getHeadInfo___main___boxed(obj*);
obj* l_Lean_SourceInfo_updateTrailing___main(obj*, obj*);
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
obj* _init_l_Lean_choiceKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("choice");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_nullKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("null");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_strLitKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("strLit");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_numLitKind() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("numLit");
x_3 = lean_name_mk_string(x_1, x_2);
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
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
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
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = l_Lean_choiceKind;
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::mk_nat_obj(0u);
x_8 = l_String_splitAux___main___closed__1;
x_9 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(x_4, x_4, x_7, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::array_get_size(x_4);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::nat_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = l_Lean_stxInh;
x_14 = lean::array_get(x_13, x_4, x_11);
x_15 = l_Lean_Syntax_reprint___main(x_14);
lean::dec(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
x_18 = lean::mk_nat_obj(1u);
x_19 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(x_4, x_4, x_18, x_17);
return x_19;
}
}
else
{
obj* x_20; 
x_20 = lean::box(0);
return x_20;
}
}
}
case 2:
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_1, 0);
x_22 = lean::cnstr_get(x_1, 1);
x_23 = l___private_init_lean_syntax_3__reprintLeaf___main(x_21, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
default: 
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_1, 1);
x_26 = lean::cnstr_get(x_1, 0);
x_27 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
x_29 = lean::cnstr_get(x_25, 2);
x_30 = lean::string_utf8_extract(x_27, x_28, x_29);
x_31 = l___private_init_lean_syntax_3__reprintLeaf___main(x_26, x_30);
lean::dec(x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_Lean_Syntax_formatStx___main___closed__2;
x_7 = lean_name_dec_eq(x_3, x_6);
if (lean::obj_tag(x_5) == 0)
{
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_8 = l_Lean_Syntax_formatStx___main___closed__3;
x_9 = lean::box(0);
x_10 = l_Lean_Name_replacePrefix___main(x_3, x_8, x_9);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_10);
x_13 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = 0;
x_15 = l_Lean_Format_join___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_14);
x_17 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_18 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::box(1);
x_21 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_19, x_20);
lean::dec(x_19);
x_22 = l_Lean_Format_paren___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_21);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_14);
x_24 = l_Lean_Format_paren___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_14);
x_26 = l_Lean_Format_paren___closed__3;
x_27 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
x_28 = l_Lean_Format_group___main(x_27);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_3);
x_29 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_30 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_29);
x_31 = lean::box(1);
x_32 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_30, x_31);
lean::dec(x_30);
x_33 = 0;
x_34 = l_Lean_Format_join___closed__1;
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_32);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_33);
x_36 = l_Lean_Format_sbracket___closed__1;
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_33);
x_38 = l_Lean_Format_sbracket___closed__2;
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_33);
x_40 = l_Lean_Format_sbracket___closed__3;
x_41 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = l_Lean_Format_group___main(x_41);
return x_42;
}
}
else
{
obj* x_43; uint8 x_44; 
lean::inc(x_5);
x_43 = l_List_reverse___rarg(x_5);
x_44 = !lean::is_exclusive(x_5);
if (x_44 == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_45 = lean::cnstr_get(x_5, 1);
lean::dec(x_45);
x_46 = lean::cnstr_get(x_5, 0);
lean::dec(x_46);
x_47 = l_Lean_formatKVMap___closed__1;
x_48 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(x_43, x_47);
x_49 = 0;
x_50 = l_Lean_Syntax_formatStx___main___closed__4;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_49);
x_52 = l_Lean_Syntax_formatStx___main___closed__5;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_49);
x_54 = l_Lean_Syntax_formatStx___main___closed__6;
x_55 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_53);
x_56 = l_Lean_Format_group___main(x_55);
if (x_7 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_57 = l_Lean_Syntax_formatStx___main___closed__3;
x_58 = lean::box(0);
x_59 = l_Lean_Name_replacePrefix___main(x_3, x_57, x_58);
x_60 = l_Lean_Name_toString___closed__1;
x_61 = l_Lean_Name_toStringWithSep___main(x_60, x_59);
x_62 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_49);
x_64 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_65 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_64);
lean::cnstr_set(x_5, 1, x_65);
lean::cnstr_set(x_5, 0, x_63);
x_66 = lean::box(1);
x_67 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_5, x_66);
lean::dec(x_5);
x_68 = l_Lean_Format_paren___closed__1;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_49);
x_70 = l_Lean_Format_paren___closed__2;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_69);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_49);
x_72 = l_Lean_Format_paren___closed__3;
x_73 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_71);
x_74 = l_Lean_Format_group___main(x_73);
return x_74;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::free_heap_obj(x_5);
lean::dec(x_3);
x_75 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_76 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_75);
x_77 = lean::box(1);
x_78 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_76, x_77);
lean::dec(x_76);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_56);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_49);
x_80 = l_Lean_Format_sbracket___closed__1;
x_81 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_79);
lean::cnstr_set_scalar(x_81, sizeof(void*)*2, x_49);
x_82 = l_Lean_Format_sbracket___closed__2;
x_83 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
lean::cnstr_set_scalar(x_83, sizeof(void*)*2, x_49);
x_84 = l_Lean_Format_sbracket___closed__3;
x_85 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_83);
x_86 = l_Lean_Format_group___main(x_85);
return x_86;
}
}
else
{
obj* x_87; obj* x_88; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_5);
x_87 = l_Lean_formatKVMap___closed__1;
x_88 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__3(x_43, x_87);
x_89 = 0;
x_90 = l_Lean_Syntax_formatStx___main___closed__4;
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_89);
x_92 = l_Lean_Syntax_formatStx___main___closed__5;
x_93 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_92);
lean::cnstr_set_scalar(x_93, sizeof(void*)*2, x_89);
x_94 = l_Lean_Syntax_formatStx___main___closed__6;
x_95 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_93);
x_96 = l_Lean_Format_group___main(x_95);
if (x_7 == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_97 = l_Lean_Syntax_formatStx___main___closed__3;
x_98 = lean::box(0);
x_99 = l_Lean_Name_replacePrefix___main(x_3, x_97, x_98);
x_100 = l_Lean_Name_toString___closed__1;
x_101 = l_Lean_Name_toStringWithSep___main(x_100, x_99);
x_102 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_103 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_96);
lean::cnstr_set_scalar(x_103, sizeof(void*)*2, x_89);
x_104 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_105 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_104);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set(x_106, 1, x_105);
x_107 = lean::box(1);
x_108 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_106, x_107);
lean::dec(x_106);
x_109 = l_Lean_Format_paren___closed__1;
x_110 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_108);
lean::cnstr_set_scalar(x_110, sizeof(void*)*2, x_89);
x_111 = l_Lean_Format_paren___closed__2;
x_112 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*2, x_89);
x_113 = l_Lean_Format_paren___closed__3;
x_114 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_112);
x_115 = l_Lean_Format_group___main(x_114);
return x_115;
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_3);
x_116 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_117 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(x_116);
x_118 = lean::box(1);
x_119 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_117, x_118);
lean::dec(x_117);
x_120 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_120, 0, x_96);
lean::cnstr_set(x_120, 1, x_119);
lean::cnstr_set_scalar(x_120, sizeof(void*)*2, x_89);
x_121 = l_Lean_Format_sbracket___closed__1;
x_122 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_120);
lean::cnstr_set_scalar(x_122, sizeof(void*)*2, x_89);
x_123 = l_Lean_Format_sbracket___closed__2;
x_124 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set(x_124, 1, x_123);
lean::cnstr_set_scalar(x_124, sizeof(void*)*2, x_89);
x_125 = l_Lean_Format_sbracket___closed__3;
x_126 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_124);
x_127 = l_Lean_Format_group___main(x_126);
return x_127;
}
}
}
}
case 2:
{
obj* x_128; obj* x_129; obj* x_130; 
x_128 = lean::cnstr_get(x_1, 1);
lean::inc(x_128);
lean::dec(x_1);
x_129 = l_String_quote(x_128);
x_130 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_130, 0, x_129);
return x_130;
}
default: 
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; uint8 x_141; obj* x_142; obj* x_143; 
x_131 = lean::cnstr_get(x_1, 2);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_1, 3);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_1, 4);
lean::inc(x_133);
lean::dec(x_1);
x_134 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__4(x_132);
x_135 = l_List_reverse___rarg(x_133);
x_136 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__5(x_135);
x_137 = l_List_append___rarg(x_134, x_136);
x_138 = l_Lean_Name_toString___closed__1;
x_139 = l_Lean_Name_toStringWithSep___main(x_138, x_131);
x_140 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_140, 0, x_139);
x_141 = 0;
x_142 = l_Lean_formatDataValue___main___closed__3;
x_143 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_143, 0, x_142);
lean::cnstr_set(x_143, 1, x_140);
lean::cnstr_set_scalar(x_143, sizeof(void*)*2, x_141);
if (lean::obj_tag(x_137) == 0)
{
obj* x_144; obj* x_145; 
x_144 = l_Lean_Format_join___closed__1;
x_145 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_144);
lean::cnstr_set_scalar(x_145, sizeof(void*)*2, x_141);
return x_145;
}
else
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
x_146 = l_Lean_formatKVMap___closed__1;
x_147 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_137, x_146);
lean::dec(x_137);
x_148 = l_Lean_Syntax_formatStx___main___closed__4;
x_149 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_147);
lean::cnstr_set_scalar(x_149, sizeof(void*)*2, x_141);
x_150 = l_Lean_Syntax_formatStx___main___closed__5;
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_141);
x_152 = l_Lean_Syntax_formatStx___main___closed__6;
x_153 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_151);
x_154 = l_Lean_Format_group___main(x_153);
x_155 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_155, 0, x_143);
lean::cnstr_set(x_155, 1, x_154);
lean::cnstr_set_scalar(x_155, sizeof(void*)*2, x_141);
return x_155;
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
obj* l_Lean_mkLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::mk_array(x_5, x_4);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_6);
lean::cnstr_set(x_8, 2, x_7);
return x_8;
}
}
obj* l_Lean_mkStrLit(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_strLitKind;
x_4 = l_Lean_mkLit(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_mkNumLit(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_numLitKind;
x_4 = l_Lean_mkLit(x_3, x_1, x_2);
return x_4;
}
}
namespace lean {
obj* mk_syntax_str_lit_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_Lean_strLitKind;
x_4 = l_Lean_mkLit(x_3, x_1, x_2);
return x_4;
}
}
}
namespace lean {
obj* mk_syntax_num_lit_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = lean::box(0);
x_4 = l_Lean_numLitKind;
x_5 = l_Lean_mkLit(x_4, x_2, x_3);
return x_5;
}
}
}
obj* l_Lean_Syntax_isStrLit___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_strLitKind;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_7, x_8);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = l_Lean_stxInh;
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::array_get(x_11, x_3, x_12);
if (lean::obj_tag(x_13) == 2)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
x_16 = lean::box(0);
return x_16;
}
}
}
}
else
{
obj* x_17; 
x_17 = lean::box(0);
return x_17;
}
}
}
obj* l_Lean_Syntax_isStrLit___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isStrLit___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isStrLit(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isStrLit___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isStrLit___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isStrLit(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint32 x_8; uint8 x_9; 
x_8 = 49;
x_9 = x_5 == x_8;
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_12 = lean::mk_nat_obj(2u);
x_13 = lean::nat_mul(x_12, x_3);
lean::dec(x_3);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_13, x_14);
lean::dec(x_13);
x_2 = x_11;
x_3 = x_15;
goto _start;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_18 = lean::mk_nat_obj(2u);
x_19 = lean::nat_mul(x_18, x_3);
lean::dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
}
else
{
obj* x_21; 
lean::dec(x_2);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_3);
return x_21;
}
}
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_4__decodeBinLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_4__decodeBinLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_4__decodeBinLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_4__decodeBinLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = 55;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_13 = lean::mk_nat_obj(8u);
x_14 = lean::nat_mul(x_13, x_3);
lean::dec(x_3);
x_15 = lean::uint32_to_nat(x_5);
x_16 = lean::nat_add(x_14, x_15);
lean::dec(x_15);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(48u);
x_18 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
obj* x_20; 
lean::dec(x_2);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_3);
return x_20;
}
}
}
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeOctalLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_5__decodeOctalLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeOctalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_5__decodeOctalLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeOctalLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeHexLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32 x_5; obj* x_6; uint32 x_54; uint8 x_55; 
x_5 = lean::string_utf8_get(x_1, x_2);
x_54 = 48;
x_55 = x_54 <= x_5;
if (x_55 == 0)
{
obj* x_56; 
x_56 = lean::box(0);
x_6 = x_56;
goto block_53;
}
else
{
uint32 x_57; uint8 x_58; 
x_57 = 57;
x_58 = x_5 <= x_57;
if (x_58 == 0)
{
obj* x_59; 
x_59 = lean::box(0);
x_6 = x_59;
goto block_53;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_60 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_61 = lean::mk_nat_obj(16u);
x_62 = lean::nat_mul(x_61, x_3);
lean::dec(x_3);
x_63 = lean::uint32_to_nat(x_5);
x_64 = lean::nat_add(x_62, x_63);
lean::dec(x_63);
lean::dec(x_62);
x_65 = lean::mk_nat_obj(48u);
x_66 = lean::nat_sub(x_64, x_65);
lean::dec(x_64);
x_2 = x_60;
x_3 = x_66;
goto _start;
}
}
block_53:
{
uint32 x_7; uint8 x_8; 
lean::dec(x_6);
x_7 = 97;
x_8 = x_7 <= x_5;
if (x_8 == 0)
{
uint32 x_9; uint8 x_10; 
x_9 = 65;
x_10 = x_9 <= x_5;
if (x_10 == 0)
{
obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::box(0);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = 70;
x_13 = x_5 <= x_12;
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::box(0);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_16 = lean::mk_nat_obj(16u);
x_17 = lean::nat_mul(x_16, x_3);
lean::dec(x_3);
x_18 = lean::mk_nat_obj(10u);
x_19 = lean::nat_add(x_17, x_18);
lean::dec(x_17);
x_20 = lean::uint32_to_nat(x_5);
x_21 = lean::nat_add(x_19, x_20);
lean::dec(x_20);
lean::dec(x_19);
x_22 = lean::mk_nat_obj(65u);
x_23 = lean::nat_sub(x_21, x_22);
lean::dec(x_21);
x_2 = x_15;
x_3 = x_23;
goto _start;
}
}
}
else
{
uint32 x_25; uint8 x_26; 
x_25 = 102;
x_26 = x_5 <= x_25;
if (x_26 == 0)
{
uint32 x_27; uint8 x_28; 
x_27 = 65;
x_28 = x_27 <= x_5;
if (x_28 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_2);
x_29 = lean::box(0);
return x_29;
}
else
{
uint32 x_30; uint8 x_31; 
x_30 = 70;
x_31 = x_5 <= x_30;
if (x_31 == 0)
{
obj* x_32; 
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::box(0);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_33 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_34 = lean::mk_nat_obj(16u);
x_35 = lean::nat_mul(x_34, x_3);
lean::dec(x_3);
x_36 = lean::mk_nat_obj(10u);
x_37 = lean::nat_add(x_35, x_36);
lean::dec(x_35);
x_38 = lean::uint32_to_nat(x_5);
x_39 = lean::nat_add(x_37, x_38);
lean::dec(x_38);
lean::dec(x_37);
x_40 = lean::mk_nat_obj(65u);
x_41 = lean::nat_sub(x_39, x_40);
lean::dec(x_39);
x_2 = x_33;
x_3 = x_41;
goto _start;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_43 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_44 = lean::mk_nat_obj(16u);
x_45 = lean::nat_mul(x_44, x_3);
lean::dec(x_3);
x_46 = lean::mk_nat_obj(10u);
x_47 = lean::nat_add(x_45, x_46);
lean::dec(x_45);
x_48 = lean::uint32_to_nat(x_5);
x_49 = lean::nat_add(x_47, x_48);
lean::dec(x_48);
lean::dec(x_47);
x_50 = lean::mk_nat_obj(97u);
x_51 = lean::nat_sub(x_49, x_50);
lean::dec(x_49);
x_2 = x_43;
x_3 = x_51;
goto _start;
}
}
}
}
else
{
obj* x_68; 
lean::dec(x_2);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_3);
return x_68;
}
}
}
obj* l___private_init_lean_syntax_6__decodeHexLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeHexLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeHexLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeHexLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeHexLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeHexLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_utf8_at_end(x_1, x_2);
if (x_4 == 0)
{
uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_get(x_1, x_2);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = 57;
x_10 = x_5 <= x_9;
if (x_10 == 0)
{
obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::string_utf8_next(x_1, x_2);
lean::dec(x_2);
x_13 = lean::mk_nat_obj(10u);
x_14 = lean::nat_mul(x_13, x_3);
lean::dec(x_3);
x_15 = lean::uint32_to_nat(x_5);
x_16 = lean::nat_add(x_14, x_15);
lean::dec(x_15);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(48u);
x_18 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_2 = x_12;
x_3 = x_18;
goto _start;
}
}
}
else
{
obj* x_20; 
lean::dec(x_2);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_3);
return x_20;
}
}
}
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeDecimalLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeDecimalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeDecimalLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeDecimalLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_syntax_8__decodeNatLitVal___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_8__decodeNatLitVal(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::string_length(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32 x_5; uint32 x_6; uint8 x_7; 
x_5 = lean::string_utf8_get(x_1, x_3);
x_6 = 48;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_2);
x_8 = l_Char_isDigit(x_5);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; 
x_10 = l___private_init_lean_syntax_7__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_10;
}
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_dec_eq(x_2, x_11);
lean::dec(x_2);
if (x_12 == 0)
{
uint32 x_13; uint32 x_14; uint8 x_15; 
x_13 = lean::string_utf8_get(x_1, x_11);
x_14 = 120;
x_15 = x_13 == x_14;
if (x_15 == 0)
{
uint32 x_16; uint8 x_17; 
x_16 = 88;
x_17 = x_13 == x_16;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; uint8 x_38; 
x_18 = 98;
x_38 = x_13 == x_18;
if (x_38 == 0)
{
uint8 x_39; 
x_39 = 0;
x_19 = x_39;
goto block_37;
}
else
{
uint8 x_40; 
x_40 = 1;
x_19 = x_40;
goto block_37;
}
block_37:
{
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 66;
x_21 = x_13 == x_20;
if (x_21 == 0)
{
uint32 x_22; uint8 x_23; 
x_22 = 111;
x_23 = x_13 == x_22;
if (x_23 == 0)
{
uint32 x_24; uint8 x_25; 
x_24 = 79;
x_25 = x_13 == x_24;
if (x_25 == 0)
{
uint8 x_26; 
x_26 = l_Char_isDigit(x_13);
if (x_26 == 0)
{
obj* x_27; 
x_27 = lean::box(0);
return x_27;
}
else
{
obj* x_28; 
x_28 = l___private_init_lean_syntax_7__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::mk_nat_obj(2u);
x_30 = l___private_init_lean_syntax_5__decodeOctalLitAux___main(x_1, x_29, x_3);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::mk_nat_obj(2u);
x_32 = l___private_init_lean_syntax_5__decodeOctalLitAux___main(x_1, x_31, x_3);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::mk_nat_obj(2u);
x_34 = l___private_init_lean_syntax_4__decodeBinLitAux___main(x_1, x_33, x_3);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::mk_nat_obj(2u);
x_36 = l___private_init_lean_syntax_4__decodeBinLitAux___main(x_1, x_35, x_3);
return x_36;
}
}
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::mk_nat_obj(2u);
x_42 = l___private_init_lean_syntax_6__decodeHexLitAux___main(x_1, x_41, x_3);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::mk_nat_obj(2u);
x_44 = l___private_init_lean_syntax_6__decodeHexLitAux___main(x_1, x_43, x_3);
return x_44;
}
}
else
{
obj* x_45; 
x_45 = l___private_init_lean_syntax_8__decodeNatLitVal___closed__1;
return x_45;
}
}
}
else
{
obj* x_46; 
lean::dec(x_2);
x_46 = lean::box(0);
return x_46;
}
}
}
obj* l___private_init_lean_syntax_8__decodeNatLitVal___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_syntax_8__decodeNatLitVal(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLit___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_numLitKind;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_7, x_8);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = l_Lean_stxInh;
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::array_get(x_11, x_3, x_12);
if (lean::obj_tag(x_13) == 2)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_15 = l___private_init_lean_syntax_8__decodeNatLitVal(x_14);
lean::dec(x_14);
return x_15;
}
else
{
obj* x_16; 
lean::dec(x_13);
x_16 = lean::box(0);
return x_16;
}
}
}
}
else
{
obj* x_17; 
x_17 = lean::box(0);
return x_17;
}
}
}
obj* l_Lean_Syntax_isNatLit___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isNatLit___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLit(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isNatLit___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLit___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isNatLit(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isIdOrAtom___main(obj* x_1) {
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
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
case 2:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
default: 
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_6, 0);
x_8 = lean::cnstr_get(x_6, 1);
x_9 = lean::cnstr_get(x_6, 2);
x_10 = lean::string_utf8_extract(x_7, x_8, x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
}
obj* l_Lean_Syntax_isIdOrAtom___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isIdOrAtom(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom___main(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isIdOrAtom___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom(x_1);
lean::dec(x_1);
return x_2;
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
l_Lean_choiceKind = _init_l_Lean_choiceKind();
lean::mark_persistent(l_Lean_choiceKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "choiceKind"), l_Lean_choiceKind);
l_Lean_nullKind = _init_l_Lean_nullKind();
lean::mark_persistent(l_Lean_nullKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "nullKind"), l_Lean_nullKind);
l_Lean_strLitKind = _init_l_Lean_strLitKind();
lean::mark_persistent(l_Lean_strLitKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "strLitKind"), l_Lean_strLitKind);
l_Lean_numLitKind = _init_l_Lean_numLitKind();
lean::mark_persistent(l_Lean_numLitKind);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "numLitKind"), l_Lean_numLitKind);
l_Lean_stxInh = _init_l_Lean_stxInh();
lean::mark_persistent(l_Lean_stxInh);
lean::register_constant(lean::mk_const_name(lean::mk_const_name("Lean"), "stxInh"), l_Lean_stxInh);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isMissing"), 1, l_Lean_Syntax_isMissing___boxed);
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkSimpleAtom"), 1, lean::mk_syntax_atom_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkSimpleIdent"), 1, lean::mk_syntax_ident_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkListNode"), 1, lean::mk_syntax_list_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkLit"), 3, l_Lean_mkLit);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkStrLit"), 2, l_Lean_mkStrLit);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkNumLit"), 2, l_Lean_mkNumLit);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkStrLitAux"), 1, lean::mk_syntax_str_lit_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Lean"), "mkNumLitAux"), 1, lean::mk_syntax_num_lit_core);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isStrLit"), 1, l_Lean_Syntax_isStrLit___boxed);
l___private_init_lean_syntax_8__decodeNatLitVal___closed__1 = _init_l___private_init_lean_syntax_8__decodeNatLitVal___closed__1();
lean::mark_persistent(l___private_init_lean_syntax_8__decodeNatLitVal___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isNatLit"), 1, l_Lean_Syntax_isNatLit___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name(lean::mk_const_name("Lean"), "Syntax"), "isIdOrAtom"), 1, l_Lean_Syntax_isIdOrAtom___boxed);
return w;
}
