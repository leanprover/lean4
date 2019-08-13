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
obj* l_Lean_Syntax_getTailInfo___main(obj*);
obj* l_Lean_Syntax_setTailInfoAux___main___rarg(obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3(obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_setTailInfoAux(obj*);
obj* l_Lean_Syntax_setTailInfoAux___main(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1(obj*, obj*);
obj* l_Lean_Syntax_toNat___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Syntax_getHeadInfo___main___rarg___boxed(obj*);
obj* l_Lean_Syntax_getNumArgs(obj*);
obj* l_Lean_Syntax_setTailInfo___rarg(obj*, obj*);
obj* l_Lean_Syntax_isFieldIdx___rarg___boxed(obj*);
obj* l_Lean_Syntax_getKind___rarg(obj*);
obj* l_Lean_Syntax_isNatLit(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_Syntax_ifNode(obj*, obj*);
obj* l_Lean_nullKind___closed__2;
obj* l_Lean_stxInh(obj*);
obj* l_Lean_Syntax_setArg(obj*);
extern obj* l_Lean_Format_paren___closed__2;
obj* l_Lean_unreachIsNodeOther(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_4__reprintLeaf(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(obj*);
obj* l_Lean_Syntax_getTailInfo___main___rarg___boxed(obj*);
obj* l_Lean_Syntax_getId(obj*);
obj* l_Lean_Syntax_toNat(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(obj*, obj*);
obj* l_Lean_mkStrLit(obj*, obj*);
obj* l_Lean_strLitKind___closed__1;
obj* l_Lean_Syntax_reprint___main___rarg(obj*);
obj* l_Lean_Syntax_formatStx___main___rarg(obj*);
obj* l_Lean_Syntax_asNode___rarg___boxed(obj*);
obj* l_Lean_Syntax_isNatLitAux___rarg___boxed(obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main(obj*);
obj* l_Lean_nullKind___closed__1;
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_isNatLitAux___rarg(obj*, obj*);
obj* l_Lean_Syntax_formatStx___main(obj*);
obj* l_Lean_numLitKind;
obj* l_Lean_Syntax_asNode___rarg(obj*);
uint8 l_Lean_Syntax_isIdent___rarg(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(obj*, obj*);
obj* l_Lean_Syntax_updateTrailing(obj*);
obj* l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(obj*);
obj* l_Lean_SyntaxNode_withArgs___rarg(obj*, obj*);
obj* l_Lean_SyntaxNode_getArg(obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l___private_init_lean_syntax_2__updateLeadingAux___rarg(obj*, obj*);
obj* l_Lean_Syntax_updateTrailing___main(obj*);
obj* l_Lean_Syntax_ifNode___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_syntax_7__decodeHexLitAux___main(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__1;
obj* l_Lean_SyntaxNode_getNumArgs___rarg(obj*);
obj* l_Lean_Syntax_modifyArg___rarg(obj*, obj*, obj*);
obj* l_Lean_charLitKind___closed__2;
obj* l_Lean_Syntax_setTailInfo(obj*);
obj* l_Lean_Syntax_getArg(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_Syntax_setAtomVal___rarg(obj*, obj*);
obj* l_Lean_Syntax_HasToString(obj*);
obj* l_Lean_Syntax_getHeadInfo___rarg___boxed(obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__2;
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(obj*);
obj* l_Lean_Syntax_mrewriteBottomUp___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_mrewriteBottomUp(obj*, obj*);
obj* l_Lean_mkNumLit(obj*, obj*);
obj* l_Lean_SyntaxNode_withArgs(obj*, obj*);
obj* l_Lean_Syntax_setTailInfoAux___rarg(obj*, obj*);
obj* l_Lean_Syntax_getHeadInfo___rarg(obj*);
obj* l_Lean_Syntax_isNatLit___rarg___boxed(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(obj*);
obj* l_Lean_SourceInfo_updateTrailing(obj*, obj*);
obj* l_Lean_Syntax_getTailInfo___main___rarg(obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__3;
obj* l_Lean_Syntax_formatStx___rarg(obj*);
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_Syntax_setArg___rarg(obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_syntax_9__decodeNatLitVal___closed__1;
obj* l_Lean_Syntax_getIdAt(obj*);
obj* l_Lean_Syntax_mreplace___main___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_updateTrailing___rarg(obj*, obj*);
obj* l_Lean_Syntax_mreplace___boxed(obj*, obj*);
obj* l_Lean_numLitKind___closed__2;
obj* l_Lean_unreachIsNodeIdent___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getKind(obj*);
obj* l_Lean_Syntax_Lean_HasFormat___closed__1;
obj* l_Lean_Syntax_updateTrailing___main___rarg(obj*, obj*);
obj* l_Lean_Syntax_ifNodeKind(obj*, obj*);
obj* l_Lean_Syntax_setAtomVal(obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(obj*);
obj* l_Lean_Syntax_Lean_HasFormat(obj*);
obj* l_Lean_Syntax_getArg___rarg(obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__9;
obj* l___private_init_lean_syntax_3__updateLast___main(obj*);
obj* l___private_init_lean_syntax_7__decodeHexLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx(obj*);
namespace lean {
obj* mk_syntax_str_lit_core(obj*);
}
obj* l_Lean_Syntax_isFieldIdx(obj*);
obj* l_Lean_SourceInfo_appendToLeading(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___rarg(obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getArg___rarg(obj*, obj*);
uint8 l_UInt32_decLe(uint32, uint32);
uint8 l_Lean_Syntax_isOfKind___rarg(obj*, obj*);
obj* l___private_init_lean_syntax_2__updateLeadingAux(obj*);
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1___rarg(obj*, obj*);
extern obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_Syntax_isIdOrAtom(obj*);
namespace lean {
uint8 string_utf8_at_end(obj*, obj*);
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(obj*);
obj* l_Lean_Syntax_isOfKind(obj*);
obj* l_Lean_Syntax_getHeadInfo___main(obj*);
obj* l_Lean_SyntaxNode_getIdAt___rarg(obj*, obj*);
obj* l_Lean_Syntax_getNumArgs___rarg___boxed(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_SourceInfo_truncateTrailing(obj*);
obj* l_Lean_Syntax_isStrLit___rarg(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getArgs___rarg(obj*);
obj* l_Lean_Syntax_isMissing___rarg___boxed(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getPos___rarg___boxed(obj*);
obj* l_Lean_Syntax_getHeadInfo___main___rarg(obj*);
obj* l_Lean_Syntax_getId___rarg(obj*);
obj* l_Lean_unreachIsNodeAtom(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__2(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Syntax_mrewriteBottomUp___boxed(obj*, obj*);
obj* l_Lean_Syntax_getKind(obj*);
obj* l___private_init_lean_syntax_5__decodeBinLitAux___main(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_Lean_Format_paren___closed__3;
obj* l_Lean_unreachIsNodeOther___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getIdAt(obj*);
obj* l_Lean_charLitKind___closed__1;
obj* l_Lean_nullKind;
obj* l_Lean_SyntaxNode_getNumArgs___rarg___boxed(obj*);
obj* l_Lean_choiceKind;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___main(obj*, obj*, obj*);
obj* l_Lean_Syntax_asNode(obj*);
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_getTailInfo___rarg(obj*);
namespace lean {
obj* mk_syntax_ident_core(obj*);
}
obj* l_Lean_Syntax_isNatLit___rarg(obj*);
obj* l_Lean_strLitKind;
obj* l_Lean_Syntax_isOfKind___rarg___boxed(obj*, obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg(obj*);
obj* l_Lean_Syntax_setArgs(obj*);
obj* l_Lean_choiceKind___closed__2;
obj* l___private_init_lean_syntax_4__reprintLeaf___boxed(obj*, obj*);
obj* l_Lean_Syntax_reprint(obj*);
obj* l_Lean_fieldIdxKind___closed__2;
obj* l_Lean_Syntax_getHeadInfo(obj*);
namespace lean {
uint32 string_utf8_get(obj*, obj*);
}
obj* l_Lean_Syntax_modifyArg(obj*);
obj* l_Lean_Syntax_mreplace___rarg(obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeMissing(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_3__updateLast(obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__10;
obj* l_Lean_Syntax_isIdOrAtom___rarg___boxed(obj*);
obj* l___private_init_lean_syntax_9__decodeNatLitVal(obj*);
obj* l_Lean_Syntax_isIdent___rarg___boxed(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Syntax_formatStx___main___rarg___closed__8;
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg(obj*, obj*);
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___main(obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Syntax_mrewriteBottomUp___main(obj*, obj*);
obj* l___private_init_lean_syntax_7__decodeHexLitAux(obj*, obj*, obj*);
obj* l_Lean_Syntax_isIdent(obj*);
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(obj*);
obj* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1___rarg(obj*, obj*);
obj* l___private_init_lean_syntax_5__decodeBinLitAux(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___rarg___boxed(obj*);
obj* l___private_init_lean_syntax_5__decodeBinLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getArgs___rarg___boxed(obj*);
obj* l_Lean_Syntax_updateLeading(obj*);
obj* l_Lean_SyntaxNode_getKind___rarg___boxed(obj*);
obj* l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2___boxed(obj*, obj*);
obj* l_Lean_SyntaxNode_getArg___rarg___boxed(obj*, obj*);
obj* l_Lean_Syntax_setArgs___rarg(obj*, obj*);
obj* l___private_init_lean_syntax_1__updateInfo(obj*, obj*);
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___main___boxed(obj*, obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Syntax_modifyArgs___rarg(obj*, obj*);
obj* l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Syntax_modifyArgs(obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_3__updateLast___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getIdAt___rarg___boxed(obj*, obj*);
obj* l_Lean_Syntax_reprint___main___rarg___closed__1;
obj* l_Lean_Syntax_getArgs___rarg___boxed(obj*);
obj* l_Lean_Name_replacePrefix___main(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__3;
obj* l_Lean_Syntax_rewriteBottomUp___rarg(obj*, obj*);
extern obj* l_System_FilePath_dirName___closed__1;
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___main___boxed(obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getNumArgs(obj*);
extern obj* l_Lean_HasRepr___closed__1;
obj* l___private_init_lean_syntax_3__updateLast___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__1;
namespace lean {
obj* mk_syntax_list_core(obj*);
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2___rarg(obj*, obj*, obj*);
extern obj* l_Lean_formatDataValue___closed__2;
namespace lean {
obj* format_group_core(obj*);
}
obj* l_Lean_Syntax_isIdOrAtom___rarg(obj*);
obj* l_Lean_SyntaxNode_getArgs(obj*);
obj* l_Lean_Syntax_getIdAt___rarg(obj*, obj*);
obj* l_Lean_Syntax_isStrLit(obj*);
obj* l_Lean_Syntax_getKind___rarg___boxed(obj*);
obj* l_Lean_Syntax_getArg___rarg___boxed(obj*, obj*);
obj* l_Lean_Syntax_updateLeading___rarg(obj*);
namespace lean {
obj* mk_syntax_num_lit_core(obj*);
}
obj* l_Lean_Syntax_getPos(obj*);
obj* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Syntax_reprint___main___rarg___boxed(obj*);
obj* l_Lean_SourceInfo_appendToTrailing(obj*, obj*);
obj* l_Lean_SyntaxNode_getKind___rarg(obj*);
obj* l_Array_size(obj*, obj*);
obj* l___private_init_lean_syntax_9__decodeNatLitVal___boxed(obj*);
obj* l_Lean_fieldIdxKind___closed__1;
obj* l_Lean_Syntax_getArgs(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getId___rarg___boxed(obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__5;
obj* l_Lean_unreachIsNodeAtom___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_isFieldIdx___rarg(obj*);
namespace lean {
obj* string_utf8_next(obj*, obj*);
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_getIdAt___rarg___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_syntax_6__decodeOctalLitAux(obj*, obj*, obj*);
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_utf8_extract(obj*, obj*, obj*);
}
obj* l_Lean_Syntax_ifNodeKind___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_toNat___rarg(obj*);
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_modifyArgs___rarg(obj*, obj*);
obj* l_Lean_Syntax_getPos___rarg(obj*);
namespace lean {
obj* string_utf8_byte_size(obj*);
}
uint8 l_Lean_Syntax_isMissing___rarg(obj*);
obj* l_Lean_Syntax_asNode___rarg___closed__1;
obj* l_Lean_Syntax_getTailInfo(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_Syntax_mreplace___main___boxed(obj*, obj*);
obj* l_Lean_choiceKind___closed__1;
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg___boxed(obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_isStrLit___rarg___boxed(obj*);
obj* l_Lean_Syntax_HasToString___closed__1;
obj* l___private_init_lean_syntax_7__decodeHexLitAux___boxed(obj*, obj*, obj*);
obj* l_Lean_SyntaxNode_modifyArgs(obj*);
obj* l_Lean_strLitKind___closed__2;
obj* l_Lean_Syntax_formatStx___main___rarg___closed__7;
obj* l_String_quote(obj*);
obj* l_Lean_Syntax_getNumArgs___rarg(obj*);
obj* l_Lean_Syntax_reprint___rarg(obj*);
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg(obj*);
obj* l_Lean_SyntaxNode_getArgs___rarg(obj*);
obj* l_Lean_Syntax_mreplace(obj*, obj*);
obj* l_Lean_Syntax_rewriteBottomUp(obj*);
obj* l_Lean_Syntax_isNatLitAux(obj*);
namespace lean {
obj* mk_syntax_atom_core(obj*);
}
obj* l_Lean_Syntax_mreplace___main(obj*, obj*);
obj* l_Lean_numLitKind___closed__1;
obj* l_Lean_Syntax_ifNodeKind___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_mkLit(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l___private_init_lean_syntax_5__decodeBinLitAux___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(obj*);
obj* l_Lean_Syntax_modifyArg___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_getTailInfo___rarg___boxed(obj*);
obj* l_Lean_Syntax_setArg___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__4;
obj* l_Lean_charLitKind;
obj* l_Lean_Syntax_mrewriteBottomUp___main___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(obj*);
obj* l_Lean_Syntax_formatStx___main___rarg___closed__6;
obj* l_Lean_fieldIdxKind;
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_unreachIsNodeIdent(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux(obj*, obj*, obj*);
obj* l_Lean_Syntax_isMissing(obj*);
extern obj* l_String_splitAux___main___closed__1;
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_SourceInfo_updateTrailing(obj* x_1, obj* x_2) {
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
obj* l_Lean_SourceInfo_truncateTrailing(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; uint8 x_4; 
x_3 = lean::cnstr_get(x_1, 2);
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean::cnstr_get(x_3, 2);
lean::dec(x_6);
lean::inc(x_5);
lean::cnstr_set(x_3, 2, x_5);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
lean::inc(x_8);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_8);
lean::cnstr_set(x_1, 2, x_9);
return x_1;
}
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 2);
x_11 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_15 = x_10;
} else {
 lean::dec_ref(x_10);
 x_15 = lean::box(0);
}
lean::inc(x_14);
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set(x_16, 2, x_14);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_12);
lean::cnstr_set(x_17, 2, x_16);
return x_17;
}
}
}
obj* l_Lean_SourceInfo_appendToTrailing(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 2);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 2);
lean::inc(x_4);
lean::dec(x_2);
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_1, 2);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_4);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_4, 1);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_4, 0);
lean::dec(x_11);
lean::cnstr_set(x_4, 1, x_8);
lean::cnstr_set(x_4, 0, x_7);
lean::cnstr_set(x_1, 2, x_4);
return x_1;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_4, 2);
lean::inc(x_12);
lean::dec(x_4);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_8);
lean::cnstr_set(x_13, 2, x_12);
lean::cnstr_set(x_1, 2, x_13);
return x_1;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_3, 1);
lean::inc(x_17);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_4, 2);
lean::inc(x_18);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_19 = x_4;
} else {
 lean::dec_ref(x_4);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_18);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_20);
return x_21;
}
}
}
obj* l_Lean_SourceInfo_appendToLeading(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_1, 0);
lean::dec(x_6);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_9 = !lean::is_exclusive(x_4);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_4, 2);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_4, 0);
lean::dec(x_11);
lean::cnstr_set(x_4, 2, x_8);
lean::cnstr_set(x_4, 0, x_7);
lean::cnstr_set(x_1, 0, x_4);
return x_1;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_8);
lean::cnstr_set(x_1, 0, x_13);
return x_1;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_1, 1);
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_3, 2);
lean::inc(x_17);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_19 = x_4;
} else {
 lean::dec_ref(x_4);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_17);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_15);
return x_21;
}
}
}
obj* _init_l_Lean_choiceKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("choice");
return x_1;
}
}
obj* _init_l_Lean_choiceKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_choiceKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_choiceKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_choiceKind___closed__2;
return x_1;
}
}
obj* _init_l_Lean_nullKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("null");
return x_1;
}
}
obj* _init_l_Lean_nullKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_nullKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_nullKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_nullKind___closed__2;
return x_1;
}
}
obj* _init_l_Lean_strLitKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("strLit");
return x_1;
}
}
obj* _init_l_Lean_strLitKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_strLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_strLitKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_strLitKind___closed__2;
return x_1;
}
}
obj* _init_l_Lean_charLitKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("charLit");
return x_1;
}
}
obj* _init_l_Lean_charLitKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_charLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_charLitKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_charLitKind___closed__2;
return x_1;
}
}
obj* _init_l_Lean_numLitKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("numLit");
return x_1;
}
}
obj* _init_l_Lean_numLitKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_numLitKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_numLitKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_numLitKind___closed__2;
return x_1;
}
}
obj* _init_l_Lean_fieldIdxKind___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("fieldIdx");
return x_1;
}
}
obj* _init_l_Lean_fieldIdxKind___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_fieldIdxKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_fieldIdxKind() {
_start:
{
obj* x_1; 
x_1 = l_Lean_fieldIdxKind___closed__2;
return x_1;
}
}
obj* l_Lean_stxInh(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
uint8 l_Lean_Syntax_isMissing___rarg(obj* x_1) {
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
obj* l_Lean_Syntax_isMissing(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isMissing___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isMissing___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isMissing___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_unreachIsNodeMissing(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeAtom(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeAtom___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_unreachIsNodeAtom(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
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
return x_8;
}
}
obj* l_Lean_unreachIsNodeOther(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean_unreachable();
}
}
obj* l_Lean_unreachIsNodeOther___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_unreachIsNodeOther(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_SyntaxNode_getKind___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getKind(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_getKind___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getKind___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SyntaxNode_getKind___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SyntaxNode_withArgs___rarg(obj* x_1, obj* x_2) {
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
obj* l_Lean_SyntaxNode_withArgs(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_withArgs___rarg), 2, 0);
return x_3;
}
}
obj* l_Lean_SyntaxNode_getNumArgs___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::array_get_size(x_2);
return x_3;
}
}
obj* l_Lean_SyntaxNode_getNumArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_getNumArgs___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getNumArgs___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SyntaxNode_getNumArgs___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getArg___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
x_5 = lean::array_get(x_4, x_3, x_2);
return x_5;
}
}
obj* l_Lean_SyntaxNode_getArg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_getArg___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getArg___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SyntaxNode_getArg___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_SyntaxNode_getArgs___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_getArgs___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getArgs___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SyntaxNode_getArgs___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SyntaxNode_modifyArgs___rarg(obj* x_1, obj* x_2) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_8 = lean::apply_1(x_2, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Lean_SyntaxNode_modifyArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_modifyArgs___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setAtomVal___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 2)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Lean_Syntax_setAtomVal(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setAtomVal___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_ifNode___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_4; 
lean::dec(x_3);
x_4 = lean::apply_1(x_2, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = lean::apply_1(x_3, x_5);
return x_6;
}
}
}
obj* l_Lean_Syntax_ifNode(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_ifNode___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Syntax_ifNodeKind___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean_name_dec_eq(x_5, x_2);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
else
{
obj* x_9; 
lean::dec(x_4);
x_9 = lean::apply_1(x_3, x_1);
return x_9;
}
}
else
{
obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_1);
x_10 = lean::box(0);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
}
}
obj* l_Lean_Syntax_ifNodeKind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_ifNodeKind___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_Syntax_ifNodeKind___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Syntax_ifNodeKind___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
uint8 l_Lean_Syntax_isIdent___rarg(obj* x_1) {
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
obj* l_Lean_Syntax_isIdent(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isIdent___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isIdent___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_Syntax_isIdent___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_getId___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 3)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
}
obj* l_Lean_Syntax_getId(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getId___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getId___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getId___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_Syntax_isOfKind___rarg(obj* x_1, obj* x_2) {
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
obj* l_Lean_Syntax_isOfKind(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isOfKind___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isOfKind___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_Syntax_isOfKind___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Syntax_asNode___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Array_empty___closed__1;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_asNode___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_2; 
x_2 = l_Lean_Syntax_asNode___rarg___closed__1;
return x_2;
}
}
}
obj* l_Lean_Syntax_asNode(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_asNode___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_asNode___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_asNode___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getNumArgs___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Syntax_asNode___rarg(x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_4 = lean::array_get_size(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Syntax_getNumArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getNumArgs___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getNumArgs___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getNumArgs___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getArgs___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Syntax_asNode___rarg(x_1);
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_getArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getArgs___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getArgs___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getArgs___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getArg___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Syntax_asNode___rarg(x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = lean::box(0);
x_6 = lean::array_get(x_5, x_4, x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Syntax_getArg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getArg___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getArg___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_getArg___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_setArgs___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_2);
return x_1;
}
else
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Lean_Syntax_setArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setArgs___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_modifyArgs___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 1)
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::inc(x_6);
lean::dec(x_1);
x_8 = lean::apply_1(x_2, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Lean_Syntax_modifyArgs(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_modifyArgs___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setArg___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::array_set(x_5, x_2, x_3);
lean::cnstr_set(x_1, 1, x_6);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_1);
x_9 = lean::array_set(x_8, x_2, x_3);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean::dec(x_3);
return x_1;
}
}
}
obj* l_Lean_Syntax_setArg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setArg___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setArg___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_setArg___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Syntax_modifyArg___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_3);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_5, x_2);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_5, x_2, x_9);
x_11 = lean::apply_1(x_3, x_8);
x_12 = lean::array_fset(x_10, x_2, x_11);
lean::cnstr_set(x_1, 1, x_12);
return x_1;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_1);
x_15 = lean::array_get_size(x_14);
x_16 = lean::nat_dec_lt(x_2, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_3);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::array_fget(x_14, x_2);
x_19 = lean::box(0);
x_20 = lean::array_fset(x_14, x_2, x_19);
x_21 = lean::apply_1(x_3, x_18);
x_22 = lean::array_fset(x_20, x_2, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_13);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean::dec(x_3);
return x_1;
}
}
}
obj* l_Lean_Syntax_modifyArg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_modifyArg___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_modifyArg___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_modifyArg___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Syntax_getIdAt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Syntax_getArg___rarg(x_1, x_2);
x_4 = l_Lean_Syntax_getId___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Syntax_getIdAt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getIdAt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getIdAt___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_getIdAt___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_getKind___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Syntax_asNode___rarg(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_getKind(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getKind___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getKind___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getKind___rarg(x_1);
lean::dec(x_1);
return x_2;
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
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg), 4, 0);
return x_3;
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
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Syntax_mreplace___main___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_8 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___rarg(x_1, x_2, x_7, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg___lambda__2), 3, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_14 = lean::apply_2(x_13, lean::box(0), x_11);
return x_14;
}
}
}
obj* l_Lean_Syntax_mreplace___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 1)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_2);
x_13 = lean::apply_1(x_2, x_3);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg___lambda__3), 6, 5);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_11);
lean::closure_set(x_14, 3, x_10);
lean::closure_set(x_14, 4, x_12);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::box(0);
x_4 = x_16;
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
obj* l_Lean_Syntax_mreplace___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___rarg), 3, 0);
return x_3;
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
obj* l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_ummapAux___main___at_Lean_Syntax_mreplace___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_mreplace___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mreplace___main(x_1, x_2);
lean::dec(x_2);
return x_3;
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
obj* l_Lean_Syntax_mreplace(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Syntax_mreplace___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mreplace(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg(x_4, x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_17 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1___boxed), 6, 5);
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
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::apply_1(x_2, x_4);
return x_5;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 1)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_8 = l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg(x_1, x_2, x_7, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mrewriteBottomUp___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_2);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
else
{
obj* x_11; 
lean::dec(x_1);
x_11 = lean::apply_1(x_2, x_3);
return x_11;
}
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mrewriteBottomUp___main___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_ummapAux___main___at_Lean_Syntax_mrewriteBottomUp___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mrewriteBottomUp___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Syntax_mrewriteBottomUp___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mrewriteBottomUp___rarg), 3, 0);
return x_3;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mrewriteBottomUp(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_12 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1___rarg(x_1, x_8);
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
obj* l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 1)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_6 = l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2___rarg(x_1, x_5, x_4);
lean::cnstr_set(x_2, 1, x_6);
x_7 = lean::apply_1(x_1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_2);
x_10 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_11 = l_Array_ummapAux___main___at_Lean_Syntax_rewriteBottomUp___spec__2___rarg(x_1, x_10, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::apply_1(x_1, x_12);
return x_13;
}
}
else
{
obj* x_14; 
x_14 = lean::apply_1(x_1, x_2);
return x_14;
}
}
}
obj* l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_rewriteBottomUp___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_mrewriteBottomUp___main___at_Lean_Syntax_rewriteBottomUp___spec__1___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_rewriteBottomUp(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_rewriteBottomUp___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_syntax_1__updateInfo(obj* x_1, obj* x_2) {
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
obj* l___private_init_lean_syntax_2__updateLeadingAux___rarg(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_1, 0);
lean::dec(x_7);
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = lean::cnstr_get(x_9, 2);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_10, 2);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l___private_init_lean_syntax_1__updateInfo(x_9, x_2);
lean::cnstr_set(x_3, 0, x_12);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_1);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_15, 2);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_16, 2);
lean::inc(x_17);
lean::dec(x_16);
x_18 = l___private_init_lean_syntax_1__updateInfo(x_15, x_2);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_1, 0, x_19);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_1);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_17);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_22 = lean::cnstr_get(x_1, 1);
lean::inc(x_22);
lean::dec(x_1);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_24 = x_3;
} else {
 lean::dec_ref(x_3);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_23, 2);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_25, 2);
lean::inc(x_26);
lean::dec(x_25);
x_27 = l___private_init_lean_syntax_1__updateInfo(x_23, x_2);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_26);
return x_31;
}
}
}
case 3:
{
obj* x_32; 
x_32 = lean::cnstr_get(x_1, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_1);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_2);
return x_34;
}
else
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_1);
if (x_35 == 0)
{
obj* x_36; uint8 x_37; 
x_36 = lean::cnstr_get(x_1, 0);
lean::dec(x_36);
x_37 = !lean::is_exclusive(x_32);
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_38 = lean::cnstr_get(x_32, 0);
x_39 = lean::cnstr_get(x_38, 2);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_39, 2);
lean::inc(x_40);
lean::dec(x_39);
x_41 = l___private_init_lean_syntax_1__updateInfo(x_38, x_2);
lean::cnstr_set(x_32, 0, x_41);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_1);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_40);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_44 = lean::cnstr_get(x_32, 0);
lean::inc(x_44);
lean::dec(x_32);
x_45 = lean::cnstr_get(x_44, 2);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_45, 2);
lean::inc(x_46);
lean::dec(x_45);
x_47 = l___private_init_lean_syntax_1__updateInfo(x_44, x_2);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_1, 0, x_48);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_1);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_46);
return x_50;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_51 = lean::cnstr_get(x_1, 1);
x_52 = lean::cnstr_get(x_1, 2);
x_53 = lean::cnstr_get(x_1, 3);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_32, 0);
lean::inc(x_54);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 x_55 = x_32;
} else {
 lean::dec_ref(x_32);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_54, 2);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_56, 2);
lean::inc(x_57);
lean::dec(x_56);
x_58 = l___private_init_lean_syntax_1__updateInfo(x_54, x_2);
if (lean::is_scalar(x_55)) {
 x_59 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_59 = x_55;
}
lean::cnstr_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
lean::cnstr_set(x_60, 2, x_52);
lean::cnstr_set(x_60, 3, x_53);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_57);
return x_62;
}
}
}
default: 
{
obj* x_63; obj* x_64; 
lean::dec(x_1);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_2);
return x_64;
}
}
}
}
obj* l___private_init_lean_syntax_2__updateLeadingAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_syntax_2__updateLeadingAux___rarg), 2, 0);
return x_2;
}
}
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_13 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1___rarg(x_9, x_3);
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
obj* l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
if (lean::obj_tag(x_1) == 1)
{
uint8 x_58; 
x_58 = !lean::is_exclusive(x_1);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_59 = lean::cnstr_get(x_1, 1);
x_60 = lean::mk_nat_obj(0u);
x_61 = l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2___rarg(x_60, x_59, x_2);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; 
x_63 = lean::cnstr_get(x_61, 0);
lean::cnstr_set(x_1, 1, x_63);
lean::cnstr_set(x_61, 0, x_1);
return x_61;
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_61);
lean::cnstr_set(x_1, 1, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_1);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_1, 0);
x_68 = lean::cnstr_get(x_1, 1);
lean::inc(x_68);
lean::inc(x_67);
lean::dec(x_1);
x_69 = lean::mk_nat_obj(0u);
x_70 = l_Array_ummapAux___main___at_Lean_Syntax_updateLeading___spec__2___rarg(x_69, x_68, x_2);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_70, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_73 = x_70;
} else {
 lean::dec_ref(x_70);
 x_73 = lean::box(0);
}
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_67);
lean::cnstr_set(x_74, 1, x_71);
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_72);
return x_75;
}
}
else
{
obj* x_76; 
x_76 = lean::box(0);
x_3 = x_76;
goto block_57;
}
block_57:
{
lean::dec(x_3);
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_1);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_1, 0);
lean::dec(x_7);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_9, 2);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_10, 2);
lean::inc(x_11);
lean::dec(x_10);
x_12 = l___private_init_lean_syntax_1__updateInfo(x_9, x_2);
lean::cnstr_set(x_4, 0, x_12);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_14, 2);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_15, 2);
lean::inc(x_16);
lean::dec(x_15);
x_17 = l___private_init_lean_syntax_1__updateInfo(x_14, x_2);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_1, 0, x_18);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_16);
return x_19;
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_4, 0);
lean::inc(x_21);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_22 = x_4;
} else {
 lean::dec_ref(x_4);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_21, 2);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_23, 2);
lean::inc(x_24);
lean::dec(x_23);
x_25 = l___private_init_lean_syntax_1__updateInfo(x_21, x_2);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_20);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
}
}
case 3:
{
obj* x_29; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; 
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_2);
return x_30;
}
else
{
uint8 x_31; 
x_31 = !lean::is_exclusive(x_1);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_1, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_29);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_29, 0);
x_35 = lean::cnstr_get(x_34, 2);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_35, 2);
lean::inc(x_36);
lean::dec(x_35);
x_37 = l___private_init_lean_syntax_1__updateInfo(x_34, x_2);
lean::cnstr_set(x_29, 0, x_37);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_1);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_29, 0);
lean::inc(x_39);
lean::dec(x_29);
x_40 = lean::cnstr_get(x_39, 2);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_40, 2);
lean::inc(x_41);
lean::dec(x_40);
x_42 = l___private_init_lean_syntax_1__updateInfo(x_39, x_2);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_1, 0, x_43);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_45 = lean::cnstr_get(x_1, 1);
x_46 = lean::cnstr_get(x_1, 2);
x_47 = lean::cnstr_get(x_1, 3);
lean::inc(x_47);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_29, 0);
lean::inc(x_48);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_49 = x_29;
} else {
 lean::dec_ref(x_29);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_48, 2);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_50, 2);
lean::inc(x_51);
lean::dec(x_50);
x_52 = l___private_init_lean_syntax_1__updateInfo(x_48, x_2);
if (lean::is_scalar(x_49)) {
 x_53 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_53 = x_49;
}
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_45);
lean::cnstr_set(x_54, 2, x_46);
lean::cnstr_set(x_54, 3, x_47);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
return x_55;
}
}
}
default: 
{
obj* x_56; 
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_1);
lean::cnstr_set(x_56, 1, x_2);
return x_56;
}
}
}
}
}
obj* l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_updateLeading___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Lean_Syntax_mreplace___main___at_Lean_Syntax_updateLeading___spec__1___rarg(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Syntax_updateLeading(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_updateLeading___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_updateTrailing___main___rarg(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
x_5 = lean::array_get_size(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_9 = lean::cnstr_get(x_2, 1);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_2, 0);
lean::dec(x_10);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_5, x_11);
lean::dec(x_5);
x_13 = lean::box(0);
x_14 = lean::array_get(x_13, x_4, x_12);
x_15 = l_Lean_Syntax_updateTrailing___main___rarg(x_1, x_14);
x_16 = lean::array_set(x_4, x_12, x_15);
lean::dec(x_12);
lean::cnstr_set(x_2, 1, x_16);
return x_2;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_2);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_5, x_17);
lean::dec(x_5);
x_19 = lean::box(0);
x_20 = lean::array_get(x_19, x_4, x_18);
x_21 = l_Lean_Syntax_updateTrailing___main___rarg(x_1, x_20);
x_22 = lean::array_set(x_4, x_18, x_21);
lean::dec(x_18);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_3);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
}
case 2:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_25; 
x_25 = !lean::is_exclusive(x_2);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::cnstr_get(x_2, 0);
lean::dec(x_26);
x_27 = !lean::is_exclusive(x_24);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_24, 0);
x_29 = l_Lean_SourceInfo_updateTrailing(x_28, x_1);
lean::cnstr_set(x_24, 0, x_29);
return x_2;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_24, 0);
lean::inc(x_30);
lean::dec(x_24);
x_31 = l_Lean_SourceInfo_updateTrailing(x_30, x_1);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_2, 0, x_32);
return x_2;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_2, 1);
lean::inc(x_33);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_35 = x_24;
} else {
 lean::dec_ref(x_24);
 x_35 = lean::box(0);
}
x_36 = l_Lean_SourceInfo_updateTrailing(x_34, x_1);
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_33);
return x_38;
}
}
}
case 3:
{
obj* x_39; 
x_39 = lean::cnstr_get(x_2, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_2);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = lean::cnstr_get(x_2, 0);
lean::dec(x_41);
x_42 = !lean::is_exclusive(x_39);
if (x_42 == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_39, 0);
x_44 = l_Lean_SourceInfo_updateTrailing(x_43, x_1);
lean::cnstr_set(x_39, 0, x_44);
return x_2;
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_39, 0);
lean::inc(x_45);
lean::dec(x_39);
x_46 = l_Lean_SourceInfo_updateTrailing(x_45, x_1);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_2, 0, x_47);
return x_2;
}
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_48 = lean::cnstr_get(x_2, 1);
x_49 = lean::cnstr_get(x_2, 2);
x_50 = lean::cnstr_get(x_2, 3);
lean::inc(x_50);
lean::inc(x_49);
lean::inc(x_48);
lean::dec(x_2);
x_51 = lean::cnstr_get(x_39, 0);
lean::inc(x_51);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_52 = x_39;
} else {
 lean::dec_ref(x_39);
 x_52 = lean::box(0);
}
x_53 = l_Lean_SourceInfo_updateTrailing(x_51, x_1);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
lean::cnstr_set(x_55, 2, x_49);
lean::cnstr_set(x_55, 3, x_50);
return x_55;
}
}
}
default: 
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l_Lean_Syntax_updateTrailing___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_updateTrailing___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_updateTrailing___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_updateTrailing___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_updateTrailing(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_updateTrailing___rarg), 2, 0);
return x_2;
}
}
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg(obj* x_1, obj* x_2) {
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
x_7 = l_Lean_Syntax_getHeadInfo___main___rarg(x_6);
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
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo___main___rarg(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg(x_2, x_3);
return x_4;
}
case 2:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
return x_6;
}
default: 
{
obj* x_7; 
x_7 = lean::box(0);
return x_7;
}
}
}
}
obj* l_Lean_Syntax_getHeadInfo___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getHeadInfo___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main___at_Lean_Syntax_getHeadInfo___main___spec__1___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_getHeadInfo___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getHeadInfo___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getHeadInfo___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getPos___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getHeadInfo___main___rarg(x_1);
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
obj* l_Lean_Syntax_getPos(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getPos___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getPos___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getPos___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_lt(x_4, x_2);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = lean::array_fget(x_1, x_8);
x_10 = l_Lean_Syntax_getTailInfo___main___rarg(x_9);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
x_2 = x_8;
x_3 = lean::box(0);
goto _start;
}
else
{
lean::dec(x_8);
return x_10;
}
}
}
}
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getTailInfo___main___rarg(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::array_get_size(x_2);
x_4 = l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg(x_2, x_3, lean::box(0));
return x_4;
}
case 2:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_6; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
return x_6;
}
default: 
{
obj* x_7; 
x_7 = lean::box(0);
return x_7;
}
}
}
}
obj* l_Lean_Syntax_getTailInfo___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getTailInfo___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindRevAux___main___at_Lean_Syntax_getTailInfo___main___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Syntax_getTailInfo___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getTailInfo___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___main___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_getTailInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_getTailInfo___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_getTailInfo___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_getTailInfo___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_3__updateLast___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::dec(x_4);
lean::inc(x_1);
x_9 = lean::array_get(x_1, x_2, x_8);
lean::inc(x_3);
x_10 = lean::apply_1(x_3, x_9);
if (lean::obj_tag(x_10) == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_3);
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_10, 0);
x_14 = lean::array_set(x_2, x_8, x_13);
lean::dec(x_8);
lean::cnstr_set(x_10, 0, x_14);
return x_10;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_16 = lean::array_set(x_2, x_8, x_15);
lean::dec(x_8);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
obj* x_18; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_18 = lean::box(0);
return x_18;
}
}
}
obj* l___private_init_lean_syntax_3__updateLast___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_syntax_3__updateLast___main___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_syntax_3__updateLast___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_syntax_3__updateLast___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_syntax_3__updateLast(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_syntax_3__updateLast___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::box(0);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
x_9 = lean::array_get(x_4, x_2, x_8);
lean::inc(x_1);
x_10 = l_Lean_Syntax_setTailInfoAux___main___rarg(x_1, x_9);
if (lean::obj_tag(x_10) == 0)
{
x_3 = x_8;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_1);
x_12 = !lean::is_exclusive(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_10, 0);
x_14 = lean::array_set(x_2, x_8, x_13);
lean::dec(x_8);
lean::cnstr_set(x_10, 0, x_14);
return x_10;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
lean::dec(x_10);
x_16 = lean::array_set(x_2, x_8, x_15);
lean::dec(x_8);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
obj* x_18; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_18 = lean::box(0);
return x_18;
}
}
}
obj* l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setTailInfoAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::array_get_size(x_5);
x_7 = l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1___rarg(x_1, x_5, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
lean::free_heap_obj(x_2);
lean::dec(x_4);
x_8 = lean::box(0);
return x_8;
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_7, 0);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_7, 0, x_2);
return x_7;
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_7, 0);
lean::inc(x_11);
lean::dec(x_7);
lean::cnstr_set(x_2, 1, x_11);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_2);
return x_12;
}
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_2);
x_15 = lean::array_get_size(x_14);
x_16 = l___private_init_lean_syntax_3__updateLast___main___at_Lean_Syntax_setTailInfoAux___main___spec__1___rarg(x_1, x_14, x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; 
lean::dec(x_13);
x_17 = lean::box(0);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_19 = x_16;
} else {
 lean::dec_ref(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_18);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_20);
return x_21;
}
}
}
case 2:
{
uint8 x_22; 
x_22 = !lean::is_exclusive(x_2);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_2, 0);
lean::dec(x_23);
lean::cnstr_set(x_2, 0, x_1);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = lean::cnstr_get(x_2, 1);
lean::inc(x_25);
lean::dec(x_2);
x_26 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
case 3:
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_2);
if (x_28 == 0)
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_2, 0);
lean::dec(x_29);
lean::cnstr_set(x_2, 0, x_1);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_2);
return x_30;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_2, 1);
x_32 = lean::cnstr_get(x_2, 2);
x_33 = lean::cnstr_get(x_2, 3);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_2);
x_34 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_31);
lean::cnstr_set(x_34, 2, x_32);
lean::cnstr_set(x_34, 3, x_33);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
default: 
{
obj* x_36; 
lean::dec(x_2);
lean::dec(x_1);
x_36 = lean::box(0);
return x_36;
}
}
}
}
obj* l_Lean_Syntax_setTailInfoAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setTailInfoAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setTailInfoAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_setTailInfoAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_setTailInfoAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setTailInfoAux___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_setTailInfo___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = l_Lean_Syntax_setTailInfoAux___main___rarg(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
return x_1;
}
else
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
}
obj* l_Lean_Syntax_setTailInfo(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_setTailInfo___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_syntax_4__reprintLeaf(obj* x_1, obj* x_2) {
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
obj* l___private_init_lean_syntax_4__reprintLeaf___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_syntax_4__reprintLeaf(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_Lean_Syntax_reprint___main___rarg(x_8);
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
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_Lean_Syntax_reprint___main___rarg(x_8);
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
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* _init_l_Lean_Syntax_reprint___main___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Syntax_reprint___main___rarg(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_choiceKind;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(0u);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg(x_3, x_3, x_6, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::array_get_size(x_3);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_9, x_10);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::box(0);
x_13 = lean::array_get(x_12, x_3, x_10);
x_14 = l_Lean_Syntax_reprint___main___rarg(x_13);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; 
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::mk_nat_obj(1u);
x_18 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg(x_3, x_3, x_17, x_16);
return x_18;
}
}
else
{
obj* x_19; 
x_19 = lean::box(0);
return x_19;
}
}
}
case 2:
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_1, 0);
x_21 = lean::cnstr_get(x_1, 1);
x_22 = l___private_init_lean_syntax_4__reprintLeaf(x_20, x_21);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
case 3:
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_24 = lean::cnstr_get(x_1, 1);
x_25 = lean::cnstr_get(x_1, 0);
x_26 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
x_28 = lean::cnstr_get(x_24, 2);
x_29 = lean::string_utf8_extract(x_26, x_27, x_28);
x_30 = l___private_init_lean_syntax_4__reprintLeaf(x_25, x_29);
lean::dec(x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
default: 
{
obj* x_32; 
x_32 = l_Lean_Syntax_reprint___main___rarg___closed__1;
return x_32;
}
}
}
}
obj* l_Lean_Syntax_reprint___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_reprint___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_Syntax_reprint___main___spec__2___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Syntax_reprint___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_reprint___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___main___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_reprint(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_reprint___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_reprint___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_reprint___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg(obj* x_1) {
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
x_6 = l_Lean_Syntax_formatStx___main___rarg(x_4);
x_7 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg(x_5);
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
x_10 = l_Lean_Syntax_formatStx___main___rarg(x_8);
x_11 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg), 1, 0);
return x_2;
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
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg(obj* x_1) {
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
x_6 = l_Lean_Syntax_formatStx___main___rarg(x_4);
x_7 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg(x_5);
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
x_10 = l_Lean_Syntax_formatStx___main___rarg(x_8);
x_11 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("<missing>");
return x_1;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Syntax_formatStx___main___rarg___closed__1;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Lean");
return x_1;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Parser");
return x_1;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Syntax_formatStx___main___rarg___closed__4;
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__7() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("noKind");
return x_1;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__8() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Syntax_formatStx___main___rarg___closed__6;
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__9() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("<other>");
return x_1;
}
}
obj* _init_l_Lean_Syntax_formatStx___main___rarg___closed__10() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Syntax_formatStx___main___rarg___closed__9;
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Syntax_formatStx___main___rarg(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_Lean_Syntax_formatStx___main___rarg___closed__2;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_Lean_Syntax_formatStx___main___rarg___closed__8;
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_7 = l_Lean_Syntax_formatStx___main___rarg___closed__6;
x_8 = lean::box(0);
x_9 = l_Lean_Name_replacePrefix___main(x_3, x_7, x_8);
x_10 = l_System_FilePath_dirName___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_9);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_14 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__1___rarg(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::box(1);
x_17 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_15, x_16);
lean::dec(x_15);
x_18 = 0;
x_19 = l_Lean_Format_paren___closed__2;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_18);
x_21 = l_Lean_Format_paren___closed__3;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_18);
x_23 = l_Lean_Format_paren___closed__1;
x_24 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = lean::format_group_core(x_24);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_3);
x_26 = l_Array_toList___rarg(x_4);
lean::dec(x_4);
x_27 = l_List_map___main___at_Lean_Syntax_formatStx___main___spec__3___rarg(x_26);
x_28 = lean::box(1);
x_29 = l_Lean_Format_joinSep___main___at_Lean_Syntax_formatStx___main___spec__2(x_27, x_28);
lean::dec(x_27);
x_30 = 0;
x_31 = l_Lean_Format_sbracket___closed__2;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_30);
x_33 = l_Lean_Format_sbracket___closed__3;
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_30);
x_35 = l_Lean_Format_sbracket___closed__1;
x_36 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
x_37 = lean::format_group_core(x_36);
return x_37;
}
}
case 2:
{
obj* x_38; obj* x_39; obj* x_40; 
x_38 = lean::cnstr_get(x_1, 1);
lean::inc(x_38);
lean::dec(x_1);
x_39 = l_String_quote(x_38);
x_40 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
case 3:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; 
x_41 = lean::cnstr_get(x_1, 2);
lean::inc(x_41);
lean::dec(x_1);
x_42 = l_System_FilePath_dirName___closed__1;
x_43 = l_Lean_Name_toStringWithSep___main(x_42, x_41);
x_44 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
x_45 = 0;
x_46 = l_Lean_formatDataValue___closed__2;
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_45);
return x_47;
}
default: 
{
obj* x_48; 
lean::dec(x_1);
x_48 = l_Lean_Syntax_formatStx___main___rarg___closed__10;
return x_48;
}
}
}
}
obj* l_Lean_Syntax_formatStx___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_formatStx___main___rarg), 1, 0);
return x_2;
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
obj* l_Lean_Syntax_formatStx___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_formatStx___main___rarg(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_formatStx(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_formatStx___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_Lean_Syntax_Lean_HasFormat___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_formatStx___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Syntax_Lean_HasFormat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_Lean_HasFormat___closed__1;
return x_2;
}
}
obj* _init_l_Lean_Syntax_HasToString___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Syntax_Lean_HasFormat___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_HasToString___closed__1;
return x_2;
}
}
obj* l_Lean_SyntaxNode_getIdAt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
x_5 = lean::array_get(x_4, x_3, x_2);
x_6 = l_Lean_Syntax_getId___rarg(x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_SyntaxNode_getIdAt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SyntaxNode_getIdAt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_SyntaxNode_getIdAt___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SyntaxNode_getIdAt___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
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
x_3 = l_System_FilePath_dirName___closed__1;
lean::inc(x_1);
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_1);
x_5 = lean::string_utf8_byte_size(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
lean::cnstr_set(x_7, 2, x_5);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_7);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_8);
return x_9;
}
}
}
namespace lean {
obj* mk_syntax_list_core(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_nullKind;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
}
obj* l_Lean_mkLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::mk_array(x_5, x_4);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
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
obj* l_Lean_Syntax_isStrLit___rarg(obj* x_1) {
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
x_11 = lean::box(0);
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
obj* l_Lean_Syntax_isStrLit(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isStrLit___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isStrLit___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isStrLit___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_5__decodeBinLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l___private_init_lean_syntax_5__decodeBinLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeBinLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_5__decodeBinLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeBinLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_5__decodeBinLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_5__decodeBinLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeOctalLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeOctalLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeOctalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_6__decodeOctalLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_6__decodeOctalLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeHexLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l___private_init_lean_syntax_7__decodeHexLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeHexLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeHexLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeHexLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_7__decodeHexLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_7__decodeHexLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___main(obj* x_1, obj* x_2, obj* x_3) {
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
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_8__decodeDecimalLitAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_8__decodeDecimalLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_syntax_8__decodeDecimalLitAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_syntax_8__decodeDecimalLitAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_syntax_9__decodeNatLitVal___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_syntax_9__decodeNatLitVal(obj* x_1) {
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
x_10 = l___private_init_lean_syntax_8__decodeDecimalLitAux___main(x_1, x_3, x_3);
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
x_28 = l___private_init_lean_syntax_8__decodeDecimalLitAux___main(x_1, x_3, x_3);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::mk_nat_obj(2u);
x_30 = l___private_init_lean_syntax_6__decodeOctalLitAux___main(x_1, x_29, x_3);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::mk_nat_obj(2u);
x_32 = l___private_init_lean_syntax_6__decodeOctalLitAux___main(x_1, x_31, x_3);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = lean::mk_nat_obj(2u);
x_34 = l___private_init_lean_syntax_5__decodeBinLitAux___main(x_1, x_33, x_3);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
x_35 = lean::mk_nat_obj(2u);
x_36 = l___private_init_lean_syntax_5__decodeBinLitAux___main(x_1, x_35, x_3);
return x_36;
}
}
}
else
{
obj* x_41; obj* x_42; 
x_41 = lean::mk_nat_obj(2u);
x_42 = l___private_init_lean_syntax_7__decodeHexLitAux___main(x_1, x_41, x_3);
return x_42;
}
}
else
{
obj* x_43; obj* x_44; 
x_43 = lean::mk_nat_obj(2u);
x_44 = l___private_init_lean_syntax_7__decodeHexLitAux___main(x_1, x_43, x_3);
return x_44;
}
}
else
{
obj* x_45; 
x_45 = l___private_init_lean_syntax_9__decodeNatLitVal___closed__1;
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
obj* l___private_init_lean_syntax_9__decodeNatLitVal___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_syntax_9__decodeNatLitVal(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLitAux___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 1)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean_name_dec_eq(x_3, x_1);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_get_size(x_4);
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
x_11 = lean::box(0);
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::array_get(x_11, x_4, x_12);
if (lean::obj_tag(x_13) == 2)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_15 = l___private_init_lean_syntax_9__decodeNatLitVal(x_14);
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
obj* l_Lean_Syntax_isNatLitAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isNatLitAux___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLitAux___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Syntax_isNatLitAux___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Syntax_isNatLit___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux___rarg(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Syntax_isNatLit(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isNatLit___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isNatLit___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isNatLit___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isFieldIdx___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_fieldIdxKind;
x_3 = l_Lean_Syntax_isNatLitAux___rarg(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Syntax_isFieldIdx(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isFieldIdx___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isFieldIdx___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isFieldIdx___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_isIdOrAtom___rarg(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 2:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
case 3:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::cnstr_get(x_4, 1);
x_7 = lean::cnstr_get(x_4, 2);
x_8 = lean::string_utf8_extract(x_5, x_6, x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
default: 
{
obj* x_10; 
x_10 = lean::box(0);
return x_10;
}
}
}
}
obj* l_Lean_Syntax_isIdOrAtom(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_isIdOrAtom___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_isIdOrAtom___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_isIdOrAtom___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Syntax_toNat___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_numLitKind;
x_3 = l_Lean_Syntax_isNatLitAux___rarg(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::mk_nat_obj(0u);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
return x_5;
}
}
}
obj* l_Lean_Syntax_toNat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Syntax_toNat___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Syntax_toNat___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_toNat___rarg(x_1);
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
l_Lean_choiceKind___closed__1 = _init_l_Lean_choiceKind___closed__1();
lean::mark_persistent(l_Lean_choiceKind___closed__1);
l_Lean_choiceKind___closed__2 = _init_l_Lean_choiceKind___closed__2();
lean::mark_persistent(l_Lean_choiceKind___closed__2);
l_Lean_choiceKind = _init_l_Lean_choiceKind();
lean::mark_persistent(l_Lean_choiceKind);
l_Lean_nullKind___closed__1 = _init_l_Lean_nullKind___closed__1();
lean::mark_persistent(l_Lean_nullKind___closed__1);
l_Lean_nullKind___closed__2 = _init_l_Lean_nullKind___closed__2();
lean::mark_persistent(l_Lean_nullKind___closed__2);
l_Lean_nullKind = _init_l_Lean_nullKind();
lean::mark_persistent(l_Lean_nullKind);
l_Lean_strLitKind___closed__1 = _init_l_Lean_strLitKind___closed__1();
lean::mark_persistent(l_Lean_strLitKind___closed__1);
l_Lean_strLitKind___closed__2 = _init_l_Lean_strLitKind___closed__2();
lean::mark_persistent(l_Lean_strLitKind___closed__2);
l_Lean_strLitKind = _init_l_Lean_strLitKind();
lean::mark_persistent(l_Lean_strLitKind);
l_Lean_charLitKind___closed__1 = _init_l_Lean_charLitKind___closed__1();
lean::mark_persistent(l_Lean_charLitKind___closed__1);
l_Lean_charLitKind___closed__2 = _init_l_Lean_charLitKind___closed__2();
lean::mark_persistent(l_Lean_charLitKind___closed__2);
l_Lean_charLitKind = _init_l_Lean_charLitKind();
lean::mark_persistent(l_Lean_charLitKind);
l_Lean_numLitKind___closed__1 = _init_l_Lean_numLitKind___closed__1();
lean::mark_persistent(l_Lean_numLitKind___closed__1);
l_Lean_numLitKind___closed__2 = _init_l_Lean_numLitKind___closed__2();
lean::mark_persistent(l_Lean_numLitKind___closed__2);
l_Lean_numLitKind = _init_l_Lean_numLitKind();
lean::mark_persistent(l_Lean_numLitKind);
l_Lean_fieldIdxKind___closed__1 = _init_l_Lean_fieldIdxKind___closed__1();
lean::mark_persistent(l_Lean_fieldIdxKind___closed__1);
l_Lean_fieldIdxKind___closed__2 = _init_l_Lean_fieldIdxKind___closed__2();
lean::mark_persistent(l_Lean_fieldIdxKind___closed__2);
l_Lean_fieldIdxKind = _init_l_Lean_fieldIdxKind();
lean::mark_persistent(l_Lean_fieldIdxKind);
l_Lean_Syntax_asNode___rarg___closed__1 = _init_l_Lean_Syntax_asNode___rarg___closed__1();
lean::mark_persistent(l_Lean_Syntax_asNode___rarg___closed__1);
l_Lean_Syntax_reprint___main___rarg___closed__1 = _init_l_Lean_Syntax_reprint___main___rarg___closed__1();
lean::mark_persistent(l_Lean_Syntax_reprint___main___rarg___closed__1);
l_Lean_Syntax_formatStx___main___rarg___closed__1 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__1();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__1);
l_Lean_Syntax_formatStx___main___rarg___closed__2 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__2();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__2);
l_Lean_Syntax_formatStx___main___rarg___closed__3 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__3();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__3);
l_Lean_Syntax_formatStx___main___rarg___closed__4 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__4();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__4);
l_Lean_Syntax_formatStx___main___rarg___closed__5 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__5();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__5);
l_Lean_Syntax_formatStx___main___rarg___closed__6 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__6();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__6);
l_Lean_Syntax_formatStx___main___rarg___closed__7 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__7();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__7);
l_Lean_Syntax_formatStx___main___rarg___closed__8 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__8();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__8);
l_Lean_Syntax_formatStx___main___rarg___closed__9 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__9();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__9);
l_Lean_Syntax_formatStx___main___rarg___closed__10 = _init_l_Lean_Syntax_formatStx___main___rarg___closed__10();
lean::mark_persistent(l_Lean_Syntax_formatStx___main___rarg___closed__10);
l_Lean_Syntax_Lean_HasFormat___closed__1 = _init_l_Lean_Syntax_Lean_HasFormat___closed__1();
lean::mark_persistent(l_Lean_Syntax_Lean_HasFormat___closed__1);
l_Lean_Syntax_HasToString___closed__1 = _init_l_Lean_Syntax_HasToString___closed__1();
lean::mark_persistent(l_Lean_Syntax_HasToString___closed__1);
l___private_init_lean_syntax_9__decodeNatLitVal___closed__1 = _init_l___private_init_lean_syntax_9__decodeNatLitVal___closed__1();
lean::mark_persistent(l___private_init_lean_syntax_9__decodeNatLitVal___closed__1);
return w;
}
